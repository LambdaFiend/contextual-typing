module Display where

import           Data.List
import           Lexer
import           Syntax

showTerm' :: TermNode -> String
showTerm' t =
  case showTerm [] t of
    "()" -> showTerm [] t
    _    -> removeOuterParens $ showTerm [] t

showTerm :: NameContext -> TermNode -> String
showTerm ctx t =
  case getTm t of
    TmInt n -> show n
    TmVarRaw x -> "#" ++ "Raw term variable found in display: " ++ x ++ showFileInfo (getFI t) ++ "#"
    TmVar k l x ->
      let ctxLength = length ctx
       in if l == ctxLength
            then getNameFromContext ctx k x
            else "#TmVar: bad context length: " ++ show l ++ "/=" ++ show ctxLength ++ "#"
    TmAbs x t1 ->
      let x' = fixName ctx x
       in "(" ++ "λ" ++ x' ++ "." ++ showTerm (x' : ctx) t1 ++ ")"
    TmApp t1 t2 -> "(" ++ showTerm ctx t1 ++ " " ++ showTerm ctx t2 ++ ")"
    TmTyAbs x t1 ->
      let x' = fixName ctx x
       in "(" ++ "Λ" ++ x' ++ "." ++ showTerm (x' : ctx) t1 ++ ")"
    TmTyApp t1 ty1 -> "(" ++ showTerm ctx t1 ++ " @" ++ showType ctx ty1 ++ ")"
    TmAnno t1 ty1 -> "(" ++ showTerm ctx t1 ++ " : " ++ showType ctx ty1 ++ ")"
    TmError e -> "#" ++ e ++ "#"

showType' :: Type -> String
showType' ty = removeOuterParens $ showType [] ty

showType :: NameContext -> Type -> String
showType ctx ty =
  case ty of
    TyInt -> "Int"
    TyVar k l x ->
      let ctxLength = length ctx
       in if l == ctxLength
            then getNameFromContext ctx k x
            else "#TyVar: bad context length: " ++ show l ++ "/=" ++ show ctxLength ++ "#"
    TyVarRaw x -> "#" ++ "Raw type variable found in display: " ++ x ++ "#"
    TyForAll x ty1 ->
      let x' = fixName ctx x
       in "(" ++ "∀" ++ x' ++ "." ++ showType (x' : ctx) ty1 ++ ")"
    TyArrow ty1 ty2 -> "(" ++ showType ctx ty1 ++ " → " ++ showType ctx ty2 ++ ")"
    TyError e -> e

showFileInfo :: FileInfo -> String
showFileInfo (AlexPn p l c) =
  "\n"
    ++ "Absolute Offset: "
    ++ show p
    ++ "\n"
    ++ "Line: "
    ++ show l
    ++ "\n"
    ++ "Column: "
    ++ show c

-- Display helper functions below this line

removeOuterParens :: String -> String
removeOuterParens xs
  | length xs >= 2 =
      let xs' = reverse $ getTail xs
       in if getHead xs == '(' && getHead xs' == ')'
            then reverse $ getTail xs'
            else xs
  | otherwise = xs
  where
    getHead = (\ws -> case ws of (y : _) -> y; _ -> '\0')
    getTail = (\ws -> case ws of (_ : ys) -> ys; _ -> [])

fixName :: NameContext -> Name -> Name
fixName ctx x
  | (length $ filter ((==) x) ctx) < 1 = x
  | otherwise = fixName ctx (x ++ "\'")

getNameFromContext :: NameContext -> Index -> Name -> Name
getNameFromContext ctx ind x
  | ind >= 0 && ind < length ctx = ctx !! ind
  | otherwise = x -- "#TmVar: no name context for var#"

showStringList :: [String] -> String
showStringList xs = "[" ++ showStringList' xs ++ "]"
  where
    showStringList' :: [String] -> String
    showStringList' []        = ""
    showStringList' [x]       = x
    showStringList' (x : xs') = x ++ ", " ++ showStringList' xs'

showSurroundingInfo :: NameContext -> SurroundingInfo -> String
showSurroundingInfo ctx info =
  case info of
    SType ty -> showType ctx ty
    STerm t  -> showTerm ctx t

showSurroundingContext :: NameContext -> SurroundingContext -> String
showSurroundingContext nctx sctx = showStringList (map (showSurroundingInfo nctx) sctx)

showTypingEnvironment :: NameContext -> TypingEnvironment -> String
showTypingEnvironment nctx ctx = showStringList (map (\(nctx'', ctx') -> showTyEnvBinding nctx'' ctx') (zip nctx' ctx))
  where
    nctx' = [drop k x | (x, k) <- zip (take (length ctx) (repeat nctx)) [0 ..]]

showTyEnvBinding :: NameContext -> TyEnvBinding -> String
showTyEnvBinding ctx b =
  case b of
    TmVarBind x ty -> x ++ " : " ++ showType ctx ty
    TyVarBind x    -> x

showSubtypingEnvironment :: NameContext -> SubtypingEnvironment -> String
showSubtypingEnvironment nctx ctx = showStringList (map (showSubTyEnvBinding nctx) ctx)

showSubTyEnvBinding :: NameContext -> SubTyEnvBinding -> String
showSubTyEnvBinding ctx b =
  case b of
    UniversalTyVar x -> x
    SolvedTyVar x ty -> x ++ " = " ++ showType ctx ty
    UnsolvedTyVar x  -> x

showPolarity :: Polarity -> String
showPolarity PositivePolarity = "+"
showPolarity NegativePolarity = "-"
