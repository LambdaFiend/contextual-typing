module MyQuickCheck where

import           Data.List
import qualified Data.Set        as S
import           Display
import           Evaluation
import           Helper
import           Lexer
import           Parser
import           Syntax
import           Test.QuickCheck
import           Typing

-- Generators

genCapital :: Int -> Gen String
genCapital size = do
  x <- elements ['A' .. 'Z']
  xs <- take (size - 26) <$> listOf (elements availableLetters)
  return (x : xs)

genNonCapital :: Int -> Gen String
genNonCapital size = do
  x <- elements ['a' .. 'z']
  xs <- take (size - 26) <$> listOf (elements availableLetters)
  return (x : xs)

availableLetters :: [Char]
availableLetters = '\'' : ['A' .. 'Z'] ++ ['a' .. 'z']

isCapitalized :: String -> Bool
isCapitalized []      = True
isCapitalized (x : _) = elem x ['A' .. 'Z']

instance Arbitrary TermNode where
  arbitrary = sized (genTermNode [])

genTermNode :: NameContext -> Int -> Gen TermNode
genTermNode ctx size = TermNode noPos <$> genTerm ctx size

instance Arbitrary Term where
  arbitrary = sized (genTerm [])

genTerm :: NameContext -> Int -> Gen Term
genTerm ctx size
  | size > 0 = oneof (termNonLeaf ctx (size - 1))
  | otherwise = oneof (termLeaf ctx)

termNonLeaf :: NameContext -> Int -> [Gen Term]
termNonLeaf ctx size =
  [ genNonCapital size >>= \x -> TmAbs x <$> genTermNode (x : ctx) size,
    TmApp <$> genTermNode ctx size <*> genTermNode ctx size,
    genCapital size >>= \x -> TmTyAbs x <$> genTermNode (x : ctx) size,
    TmTyApp <$> genTermNode ctx size <*> genType ctx size,
    TmAnno <$> genTermNode ctx size <*> genType ctx size,
    genNonCapital size >>= \x -> TmAbsAnno x <$> genType ctx size <*> genTermNode ctx size,
    TmTuple <$> ((:) <$> genTermNode ctx size <*> ((:) <$> genTermNode ctx size <*> listOf (genTermNode ctx size))),
    TmProj <$> genTermNode ctx size <*> elements [1 .. 100],
    TmIf <$> genTermNode ctx size <*> genTermNode ctx size <*> genTermNode ctx size,
    generateTwoDistinct size >>= \xs -> let xs' = S.toList $ S.fromList xs in TmAbsUnc xs' <$> genTermNode (reverse xs' ++ ctx) size,
    generateTwoDistinct size >>= \xs -> let xs' = S.toList $ S.fromList xs in TmAbsUncAnno xs' <$> vectorOf (length xs') (genType ctx size) <*> genTermNode (reverse xs' ++ ctx) size,
    TmFix <$> genTermNode ctx size,
    TmCons <$> genTermNode ctx size <*> genTermNode ctx size
  ]

generateTwoDistinct :: Int -> Gen [String]
generateTwoDistinct size = do
  first <- genNonCapital size
  second <- suchThat (genNonCapital size) (\x -> x /= first)
  xs <- listOf (genNonCapital size)
  return (first : second : xs)

termLeaf :: NameContext -> [Gen Term]
termLeaf ctx =
  [ TmConst <$> (ConstInt <$> elements [1 .. 100]),
    pure $ TmConst (ConstFloat 0.0),
    TmConst <$> (ConstBool <$> arbitrary),
    TmConst <$> (ConstChar <$> elements (['a' .. 'z'] ++ ['A' .. 'Z'])),
    pure $ TmConst ConstUnit,
    pure $ TmConst ConstHead,
    pure $ TmConst ConstTail,
    pure $ TmConst ConstEmpty,
    pure $ TmNil
  ]
    ++ if filter (not . isCapitalized) ctx == [] then [] else pure (TmVarRaw <$> elements (filter (not . isCapitalized) ctx))

instance Arbitrary Type where
  arbitrary = sized (genType [])

genType :: NameContext -> Int -> Gen Type
genType ctx size
  | size > 0 = oneof (typeNonLeaf ctx (size - 1))
  | otherwise = oneof (typeLeaf ctx)

typeNonLeaf :: NameContext -> Int -> [Gen Type]
typeNonLeaf ctx size =
  [ TyArrow <$> genType ctx size <*> genType ctx size,
    genCapital size >>= \x -> TyForAll x <$> (TyArrow (TyVarRaw x) <$> genType (x : ctx) size),
    TyTuple <$> ((:) <$> genType ctx size <*> ((:) <$> genType ctx size <*> vectorOf size (genType ctx size))),
    TyList <$> genType ctx size
  ]

typeLeaf :: NameContext -> [Gen Type]
typeLeaf ctx =
  map
    pure
    [ TyInt,
      TyFloat,
      TyBool,
      TyChar,
      TyUnit
    ]
    ++ if filter isCapitalized ctx == [] then [] else pure (TyVarRaw <$> elements (filter isCapitalized ctx))

-- Properties

goodDisplayProperty :: TermNode -> Property
goodDisplayProperty t = property ((findDisplayErrors $ showTerm' $ genIndex' t) [] == [])

roundTripProperty :: TermNode -> Property
roundTripProperty t =
  let generated = genIndex' t
      displayed = showTerm' generated
      parsed = case parser $ alexScanTokens displayed of Left e -> TermNode noPos (TmError ("Failed to parse:\n" ++ e)); Right t' -> genIndex' t'
   in property (showTerm' generated == showTerm' parsed)

subjectReduction :: TermNode -> Property
subjectReduction t =
  let generated = genIndex' t
      evaluated = snd (eval 1 generated)
      inferredg = infer' generated
      inferrede = infer' evaluated
   in findTypeErrors inferredg == [] && findTermErrors evaluated == [] ==> inferredg == inferrede

hasType :: Type -> Property
hasType ty =
  let ty' = genIndexType [] ty
      t = sized (genTermNodeHab (collectTyVars ty) ty)
      generated = genIndex' <$> t
   in forAll generated (\tm -> findTermErrors tm == [] ==> (infer' tm) == ty')

genTermNodeHab :: TypingEnvironment -> Type -> Int -> Gen TermNode
genTermNodeHab ctx ty size = TermNode noPos <$> genTermHab ctx ty size

genTermHab :: TypingEnvironment -> Type -> Int -> Gen Term
genTermHab ctx ty size
  | size == 0 = termNonLeafHab ctx ty size
  | otherwise = do
      b <- elements [True, False]
      if b
        then termNonLeafHab ctx ty size
        else oneof (termNonLeafHabElim ctx ty (size - 1))

termNonLeafHab :: TypingEnvironment -> Type -> Int -> Gen Term
termNonLeafHab ctx (TyArrow ty1 ty2) size = (fixName (map getNameTy ctx) <$> genNonCapital size) >>= \x -> TmAbsAnno x ty1 <$> genTermNodeHab (TmVarBind x ty1 : ctx) ty2 size
termNonLeafHab ctx (TyForAll x ty1) size = TmTyAbs x <$> genTermNodeHab (TyVarBind x : ctx) ty1 size
termNonLeafHab ctx (TyVar _ _ x) _ = pure $ case find (\y -> case y of (TmVarBind _ (TyVarRaw x')) | x == x' -> True; (TmVarBind _ (TyVar _ _ x')) | x == x' -> True; _ -> False) ctx of Just (TmVarBind x' _) -> TmVarRaw x'; _ -> TmError "Bad context in QuickCheck habitation generation"
termNonLeafHab ctx (TyVarRaw x) _ = pure $ case find (\y -> case y of (TmVarBind _ (TyVarRaw x')) | x == x' -> True; (TmVarBind _ (TyVar _ _ x')) | x == x' -> True; _ -> False) ctx of Just (TmVarBind x' _) -> TmVarRaw x'; _ -> TmError "Bad context in QuickCheck habitation generation"
termNonLeafHab ctx (TyList ty1) size = getTm <$> (foldr (\x y -> TermNode noPos (TmCons x y)) (TermNode noPos TmNil) <$> (vectorOf 1 (genTermNodeHab ctx ty1 size)))
termNonLeafHab ctx (TyTuple tys) size = TmTuple <$> (foldr (\ty1 lis -> (genTermNodeHab ctx ty1 size >>= \x -> ((:) x) <$> lis)) (pure []) tys)
termNonLeafHab _ TyInt _ = pure $ TmConst (ConstInt 0)
termNonLeafHab _ TyFloat _ = pure $ TmConst (ConstFloat 0.0)
termNonLeafHab _ TyChar _ = pure $ TmConst (ConstChar 'a')
termNonLeafHab _ TyBool _ = pure $ TmConst (ConstBool True)
termNonLeafHab _ TyUnit _ = pure $ TmConst (ConstUnit)

termNonLeafHabElim :: TypingEnvironment -> Type -> Int -> [Gen Term]
termNonLeafHabElim ctx ty size =
  [ (fixName (map getNameTy ctx) <$> genNonCapital size) >>= \x -> (fixTyNames (map getNameTy ctx) <$> genType [] size) >>= \ty1 -> genTermNodeHab (TmVarBind x ty1 : ctx) ty size >>= \t1 -> genTermNodeHab ctx ty1 size >>= \t2 -> pure $ TmApp (TermNode noPos (TmAbsAnno x ty1 t1)) t2,
    (fixName (map getNameTy ctx) <$> genCapital size) >>= \x -> (fixTyNames (map getNameTy ctx) <$> genType [] size) >>= \ty1 -> genTermNodeHab (TyVarBind x : ctx) ty size >>= \t1 -> pure $ TmTyApp (TermNode noPos (TmTyAbs x t1)) ty1,
    elements [1 .. size + 1] >>= \n -> vectorOf n (fixTyNames (map getNameTy ctx) <$> genType [] size) >>= \tys -> elements [1 .. n] >>= \k -> pure (map (\ty' -> genTermNodeHab ctx ty' size) tys) >>= \tms -> pure (take (k - 1) tms ++ [genTermNodeHab ctx ty size] ++ drop k tms) >>= \tms' -> TmProj <$> (TermNode noPos <$> (TmTuple <$> (foldr (\x lis -> ((:) <$> x) <*> lis)) (pure []) tms')) <*> pure k
  ]
