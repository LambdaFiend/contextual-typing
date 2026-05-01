module Evaluation where

import           Display
import           Helper
import           Syntax

eval1 :: TermNode -> TermNode
eval1 t =
  let tm = getTm t; fi = getFI t
   in TermNode fi $
        case tm of
          TmApp (TermNode _ (TmAnno (TermNode fi1 (TmAnno t11 ty1)) _)) t2 -> TmApp (TermNode fi1 (TmAnno t11 ty1)) t2
          TmApp (TermNode _ (TmConst ConstPlus)) (TermNode _ (TmConst (ConstInt n))) -> TmConst (ConstPlusInt n)
          TmApp (TermNode _ (TmConst ConstPlus)) (TermNode _ (TmConst (ConstFloat u))) -> TmConst (ConstPlusFloat u)
          TmApp (TermNode _ (TmConst (ConstPlusInt n1))) (TermNode _ (TmConst (ConstInt n2))) -> TmConst (ConstInt (n1 + n2))
          TmApp (TermNode _ (TmConst (ConstPlusFloat u1))) (TermNode _ (TmConst (ConstFloat u2))) -> TmConst (ConstFloat (u1 + u2))
          TmApp (TermNode _ (TmAbs _ t11)) v2 | isVal v2 -> getTm $ evalSubst v2 t11
          TmApp (TermNode _ (TmAnno (TermNode _ (TmAbs _ t11)) (TyArrow _ ty2))) v2 | isVal v2 -> TmAnno (evalSubst v2 t11) ty2
          TmApp v1 t2
            | isVal v1 ->
                let result = eval1 t2
                 in checkError result $ TmApp v1 result
          TmApp t1 t2
            | not $ isVal t1 ->
                let result = eval1 t1
                 in checkError result $ TmApp result t2
          TmAnno t1 ty
            | not $ isVal t1 ->
                let result = eval1 t1
                 in checkError result $ TmAnno result ty
          TmProj v1@(TermNode _ (TmRec xs ts)) x
            | isVal v1 ->
                case lookup x (zip xs ts) of
                  Just t' -> getTm t'
                  Nothing -> TmError ("Couldn't find a matching label inside the record for the projection label " ++ x)
          TmProj v1@(TermNode _ (TmAnno (TermNode _ (TmRec xs ts)) ty)) x
            | isVal v1 ->
                case (lookup x (zip xs ts), getTypeFromRecord x ty) of
                  (Just t', Just ty') -> TmAnno t' ty'
                  _ -> TmError ("Couldn't find a matching label inside the record for the projection label " ++ x)
          TmProj t1 x ->
            let result = eval1 t1
             in checkError result $ TmProj result x
          TmRec xs ts ->
            let xsTs = zip xs ts
                firstHalf = takeWhile (\(_, y) -> isVal y) xsTs
                secondHalf = dropWhile (\(_, y) -> isVal y) xsTs
                newMiddle = (\ts' -> case ts' of (t' : _) -> [(fst t', eval1 $ snd t')]; [] -> []) secondHalf
                rest = (\ts' -> case ts' of (_ : ts'') -> ts''; [] -> []) secondHalf
             in case newMiddle of
                  [(_, TermNode _ (TmError e))] -> TmError e
                  _ ->
                    let (xs', ts') = unzip (firstHalf ++ newMiddle ++ rest)
                     in TmRec xs' ts'
          _ -> TmError ("No rule applies" ++ showFileInfo fi)
  where
    checkError :: TermNode -> Term -> Term
    checkError term result =
      case getTm term of
        TmError e -> TmError e
        _         -> result

type Counter = Int

getTypeFromRecord :: Name -> Type -> Maybe Type
getTypeFromRecord x (TyInter ty1 ty2) =
  case getTypeFromRecord x ty2 of
    Just ty' -> Just ty'
    Nothing  -> getTypeFromRecord x ty1
getTypeFromRecord x (TyRec x1 ty1) | x == x1 = Just ty1
getTypeFromRecord _ _ = Nothing

eval' :: TermNode -> (Counter, TermNode)
eval' t = eval 0 t

eval :: Counter -> TermNode -> (Counter, TermNode)
eval n t@(TermNode _ (TmError _)) = (n, t)
eval n t
  | isVal t = (n, t)
  | otherwise = eval (n + 1) $ eval1 t

evalN :: Counter -> TermNode -> (Counter, TermNode)
evalN n t@(TermNode _ (TmError e)) = (n, t)
evalN n t
  | n <= 0 || isVal t = (n, t)
  | otherwise = evalN (n - 1) $ eval1 t
