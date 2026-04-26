module Display where

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
    TmVarRaw x -> "#" ++ "Raw variable found in display: " ++ x ++ showFileInfo (getFI t) ++ "#"
    TmVar k l x ->
      let ctxLength = length ctx
       in if l == ctxLength
            then getNameFromContext ctx k x
            else "#TmVar: bad context length: " ++ show l ++ "/=" ++ show ctxLength ++ "#"
    TmAbs x t1 ->
      let x' = fixName ctx x
       in "(" ++ "λ" ++ x' ++ "." ++ showTerm (x' : ctx) t1 ++ ")"
    TmApp t1 t2 -> "(" ++ showTerm ctx t1 ++ " " ++ showTerm ctx t2 ++ ")"
    TmError e -> "#" ++ e ++ "#"

showType' :: Type -> String
showType' ty = removeOuterParens (showType ty)

showType :: Type -> String
showType ty =
  case ty of
    TyInt           -> "Int"
    TyArrow ty1 ty2 -> "(" ++ showType ty1 ++ " → " ++ showType ty2 ++ ")"
    TyError e       -> "#" ++ e ++ "#"

getNameFromContext :: NameContext -> Index -> Name -> Name
getNameFromContext ctx ind x
  | ind >= 0 && ind < length ctx = ctx !! ind
  | otherwise = x -- "#TmVar: no name context for var#"

fixName :: NameContext -> Name -> Name
fixName ctx x
  | (length $ filter ((==) x) ctx) < 1 = x
  | otherwise = fixName ctx (x ++ "\'")

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

showStringList :: [String] -> String
showStringList xs = "[" ++ showStringList' xs ++ "]"
  where
    showStringList' :: [String] -> String
    showStringList' []        = ""
    showStringList' [x]       = x
    showStringList' (x : xs') = x ++ ", " ++ showStringList' xs'
