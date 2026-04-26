module Helper where

import           Data.List
import           Syntax

newtype UpdatedTmArrTm = UpdatedTmArrTm
  {updateTmArrTm :: (TermNode, TermNode -> UpdatedTmArrTm, TermNode -> UpdatedTmArrTm, Type -> Type)}

traverseDownTm :: (TermNode -> UpdatedTmArrTm) -> TermNode -> TermNode
traverseDownTm f t = TermNode fi $
  case tm of
    TmConst _     -> tm
    TmVar _ _ _   -> tm
    TmVarRaw _    -> tm
    TmAbs x t1    -> TmAbs x (traverseTm' t1)
    TmApp t1 t2   -> TmApp (traverseTm' t1) (traverseTm' t2)
    TmAnno t1 ty1 -> TmAnno (traverseTm' t1) ty1
    TmRec xs ts   -> TmRec xs (map traverseTm' ts)
    TmProj t1 x   -> TmProj (traverseTm' t1) x
    _             -> tm
  where
    tm = getTm t'
    fi = getFI t'
    traverseTm' = traverseDownTm f'
    (t', f', _, _) = updateTmArrTm $ f t

isVal :: TermNode -> Bool
isVal t =
  case getTm t of
    TmConst _                       -> True
    TmAbs _ _                       -> True
    TmRec _ ts | and $ map isVal ts -> True
    TmAnno t1 _ | isVal t1          -> True
    _                               -> False

evalSubst :: TermNode -> TermNode -> TermNode
evalSubst s t = shift' 0 (-1) (subst' 0 (shift' 0 1 s) t)

varCtxLengthSuc' :: TermNode -> TermNode
varCtxLengthSuc' t = traverseDownTm varCtxLengthSuc t

varCtxLengthSuc :: TermNode -> UpdatedTmArrTm
varCtxLengthSuc t =
  UpdatedTmArrTm $
    case getTm t of
      TmVar k l x -> (TermNode (getFI t) (TmVar k (l + 1) x), id', id', id)
      _           -> (t, varCtxLengthSuc, varCtxLengthSuc, id)

shift' :: Index -> Index -> TermNode -> TermNode
shift' c d t = traverseDownTm (shift c d) t

shift :: Index -> Index -> TermNode -> UpdatedTmArrTm
shift c d t =
  UpdatedTmArrTm $
    case getTm t of
      TmVar k l x -> (TermNode (getFI t) (TmVar (if k < c then k else k + d) (l + d) x), id', id', id)
      TmAbs _ _ -> (t, shift (c + 1) d, shift c d, id)
      _ -> (t, shift c d, shift c d, id)

subst' :: Index -> TermNode -> TermNode -> TermNode
subst' j s t = traverseDownTm (subst 0 j s) t

subst :: Index -> Index -> TermNode -> TermNode -> UpdatedTmArrTm
subst c j s t =
  UpdatedTmArrTm $
    case getTm t of
      TmVar k _ _ -> (if k == j + c then shift' 0 (j + c) s else t, id', id', id)
      TmAbs _ _ -> (t, subst (c + 1) j s, subst c j s, id)
      _ -> (t, subst c j s, subst c j s, id)

genIndex' :: TermNode -> TermNode
genIndex' t = traverseDownTm (genIndex []) t

genIndex :: NameContext -> TermNode -> UpdatedTmArrTm
genIndex ctx t =
  UpdatedTmArrTm $
    case getTm t of
      TmVarRaw x | elem x ctx -> (TermNode (getFI t) (TmVar (length $ takeWhile (/= x) ctx) (length ctx) x), genIndex ctx, genIndex ctx, id)
      TmVarRaw x -> (TermNode (getFI t) (TmError ("Free variables are not allowed: " ++ x)), genIndex ctx, genIndex ctx, id)
      TmAbs x _ -> (t, genIndex (x : ctx), genIndex ctx, id)
      TmRec xs _ | nub xs /= xs -> (TermNode (getFI t) (TmError ("All of the labels in a record must be unique within that record, and the repeated ones are: " ++ show (xs \\ nub xs))), genIndex ctx, genIndex ctx, id)
      _ -> (t, genIndex ctx, genIndex ctx, id)

id' :: TermNode -> UpdatedTmArrTm
id' t = UpdatedTmArrTm (t, id', id', id)

findDisplayErrors' :: String -> Either String String
findDisplayErrors' s =
  case findDisplayErrors s [] of
    [] -> Right s
    s' -> Left $ intercalate "\n" s'

findDisplayErrors :: String -> String -> [String]
findDisplayErrors [] [] = []
findDisplayErrors [] _ = error "Someone needs to fix this, there's an error message which does not have its identifiers matching."
findDisplayErrors ('#' : xs) [] = findDisplayErrors xs ['#']
findDisplayErrors ('#' : xs) ys = ((\s -> case s of [] -> []; (_ : xs') -> xs') $ reverse ys) : findDisplayErrors xs []
findDisplayErrors (_ : xs) [] = findDisplayErrors xs []
findDisplayErrors (x : xs) ys = findDisplayErrors xs (x : ys)

findTypeErrors' :: Type -> String
findTypeErrors' t = intercalate "\n" $ findTypeErrors t

findTypeErrors :: Type -> [String]
findTypeErrors t =
  case t of
    TyError e     -> [e]
    TyArrow t1 t2 -> findTypeErrors t1 ++ findTypeErrors t2
    TyInter t1 t2 -> findTypeErrors t1 ++ findTypeErrors t2
    TyRec _ t1    -> findTypeErrors t1
    _             -> []

findTermErrors' :: TermNode -> String
findTermErrors' t = intercalate "\n" $ findTermErrors t

findTermErrors :: TermNode -> [String]
findTermErrors t =
  let tm = getTm t
   in case tm of
        TmError e     -> [e]
        TmAbs _ t1    -> findTermErrors t1
        TmApp t1 t2   -> findTermErrors t1 ++ findTermErrors t2
        TmRec _ ts    -> concat $ map findTermErrors ts
        TmAnno t1 ty1 -> findTermErrors t1 ++ findTypeErrors ty1
        TmProj t1 _   -> findTermErrors t1
        _             -> []
