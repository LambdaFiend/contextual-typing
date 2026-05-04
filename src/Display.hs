module Display where

import           Data.List
import           Lexer
import           Syntax

showTerm' :: TermNode -> String
showTerm' t =
  case getTm t of
    (TmConst ConstUnit) -> showTerm [] t
    TmTuple _           -> showTerm [] t
    _                   -> removeOuterParens (showTerm [] t)

showTerm :: NameContext -> TermNode -> String
showTerm ctx t =
  case getTm t of
    TmConst c -> showConst c
    TmVarRaw x -> "#" ++ "Raw term variable found in display: " ++ x ++ showFileInfo (getFI t) ++ "#"
    TmVar k l x ->
      let ctxLength = length ctx
       in if l == ctxLength
            then getNameFromContext ctx k x
            else "#TmVar: bad context length: " ++ show l ++ "/=" ++ show ctxLength ++ " for " ++ x ++ "#"
    TmAbs x t1 ->
      let x' = fixName ctx x
       in "(" ++ "λ" ++ x' ++ "." ++ showTerm (x' : ctx) t1 ++ ")"
    TmApp t1 t2 -> "(" ++ showTerm ctx t1 ++ " " ++ showTerm ctx t2 ++ ")"
    TmTyAbs x t1 ->
      let x' = fixName ctx x
       in "(" ++ "Λ" ++ x' ++ "." ++ showTerm (x' : ctx) t1 ++ ")"
    TmTyApp t1 ty1 -> "(" ++ showTerm ctx t1 ++ " @" ++ showType ctx ty1 ++ ")"
    TmAnno t1 ty1 -> "(" ++ showTerm ctx t1 ++ " : " ++ showType ctx ty1 ++ ")"
    TmAbsAnno x ty1 t1 ->
      let x' = fixName ctx x
       in "(" ++ "λ" ++ x' ++ ": " ++ showType ctx ty1 ++ "." ++ showTerm (x' : ctx) t1 ++ ")"
    TmTuple (t1 : ts) -> "(" ++ foldr (\x y -> y ++ ", " ++ x) (showTerm ctx t1) (reverse (map (showTerm ctx) ts)) ++ ")"
    TmTuple [] -> "#TmTuple: bad tuple length#"
    TmProj t1 n -> "(" ++ showTerm ctx t1 ++ "." ++ show n ++ ")"
    TmIf t1 t2 t3 -> "(" ++ "if " ++ showTerm ctx t1 ++ " then " ++ showTerm ctx t2 ++ " else " ++ showTerm ctx t3 ++ ")"
    TmAbsUnc xs t1 ->
      let xs' = map (fixName ctx) xs
       in "(" ++ "λ" ++ "(" ++ intercalate ", " xs' ++ ")" ++ "." ++ showTerm (reverse xs' ++ ctx) t1 ++ ")"
    TmAbsUncAnno xs tys t1 ->
      let xs' = map (fixName ctx) xs
       in "(" ++ "λ" ++ "(" ++ intercalate ", " (map (\(x, y) -> x ++ ": " ++ showType ctx y) (zip xs' tys)) ++ ")" ++ "." ++ showTerm (reverse xs' ++ ctx) t1 ++ ")"
    TmFix t1 -> "(" ++ "fix " ++ showTerm ctx t1 ++ ")"
    TmError e -> "#" ++ e ++ "#"

showConst :: ConstInfo -> String
showConst c =
  case c of
    ConstInt n         -> show n
    ConstFloat u       -> show u
    ConstBool b        -> show b
    ConstUnit          -> "()"
    ConstOpI op        -> showNumOp op ++ "ⁱ"
    ConstOpF op        -> showNumOp op ++ "ᶠ"
    ConstOpInt op n    -> showNumOp op ++ "ⁱ" ++ "<" ++ show n ++ ">"
    ConstOpFloat op u  -> showNumOp op ++ "ᶠ" ++ "<" ++ show u ++ ">"
    ConstOpB op        -> showBoolOp op ++ "ᵇ"
    ConstOpBool op b   -> showBoolOp op ++ "ᵇ" ++ "<" ++ show b ++ ">"
    ConstNot           -> "not"
    ConstOpIB op       -> showBoolBoolOp op ++ "ⁱ"
    ConstOpIntB op n   -> showBoolBoolOp op ++ "ⁱ" ++ "<" ++ show n ++ ">"
    ConstOpFB op       -> showBoolBoolOp op ++ "ᶠ"
    ConstOpFloatB op u -> showBoolBoolOp op ++ "ᶠ" ++ "<" ++ show u ++ ">"
    ConstOpU           -> "==" ++ "ᵘ"
    ConstOpUnit        -> "==" ++ "ᵘ" ++ "<" ++ "()" ++ ">"
    ConstOpNU          -> "/=" ++ "ᵘ"
    ConstOpNUnit       -> "/=" ++ "ᵘ" ++ "<" ++ "()" ++ ">"

showNumOp :: NumOp -> String
showNumOp op =
  case op of
    PlusOp  -> "+"
    MinusOp -> "-"
    MultOp  -> "*"
    DivOp   -> "/"

showBoolOp :: BoolOp -> String
showBoolOp op =
  case op of
    AndOp -> "&&"
    OrOp  -> "||"
    EqOpB -> "=="
    NEOpB -> "/="

showBoolBoolOp :: BoolBoolOp -> String
showBoolBoolOp op =
  case op of
    LTOp -> "<"
    GTOp -> ">"
    LEOp -> "<="
    GEOp -> ">="
    EqOp -> "=="
    NEOp -> "/="

showType' :: Type -> String
showType' ty =
  case ty of
    TyUnit    -> showType [] ty
    TyTuple _ -> showType [] ty
    _         -> removeOuterParens (showType [] ty)

showType :: NameContext -> Type -> String
showType ctx ty =
  case ty of
    TyInt -> "Int"
    TyFloat -> "Float"
    TyBool -> "Bool"
    TyUnit -> "()"
    TyVar k l x ->
      let ctxLength = length ctx
       in if l == ctxLength
            then getNameFromContext ctx k x
            else "#TyVar: bad context length: " ++ show l ++ "/=" ++ show ctxLength ++ " for " ++ x ++ "#"
    TyVarRaw x -> "#" ++ "Raw type variable found in display: " ++ x ++ "#"
    TyForAll x ty1 ->
      let x' = fixName ctx x
       in "(" ++ "∀" ++ x' ++ "." ++ showType (x' : ctx) ty1 ++ ")"
    TyArrow ty1 ty2 -> "(" ++ showType ctx ty1 ++ " → " ++ showType ctx ty2 ++ ")"
    TyTuple (ty1 : tys) -> "(" ++ foldr (\x y -> y ++ ", " ++ x) (showType ctx ty1) (reverse (map (showType ctx) tys)) ++ ")"
    TyTuple [] -> "#TyTuple: bad tuple length#"
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
    SProj n  -> "." ++ show n

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
showPolarity PositivePolarity = "<=+"
showPolarity NegativePolarity = "<=-"
