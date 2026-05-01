module Evaluation where

import           Display
import           Helper
import           Syntax

eval1 :: TermNode -> TermNode
eval1 t =
  TermNode (getFI t) $
    case getTm t of
      TmApp (TermNode fi1 (TmAnno (TermNode _ (TmTyAbs _ t1)) (TyForAll _ ty1))) (TermNode fi2 (TmInt n)) ->
        TmApp (TermNode fi1 (TmAnno (shift' 0 (-1) t1) (typingEvalSubst TyInt ty1))) (TermNode fi2 (TmInt n))
      TmApp (TermNode fi1 (TmAnno (TermNode _ (TmTyAbs _ t1)) (TyForAll _ ty1))) (TermNode fi2 (TmAnno t2 ty2)) ->
        TmApp (TermNode fi1 (TmAnno (shift' 0 (-1) t1) (typingEvalSubst ty2 ty1))) (TermNode fi2 (TmAnno t2 ty2))
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmAnno t11 ty1)) _)) t2 -> TmApp (TermNode fi1 (TmAnno t11 ty1)) t2
      TmApp (TermNode _ (TmAbs _ t11)) v2
        | isVal v2 ->
            getTm (evalSubst v2 t11)
      TmApp (TermNode _ (TmAnno (TermNode _ (TmAbs _ t11)) (TyArrow _ ty2))) v2
        | isVal v2 ->
            TmAnno (TermNode (getFI t) (getTm (evalSubst v2 t11))) ty2
      TmApp v1 t2
        | isVal v1 ->
            let result = eval1 t2
             in checkError result (TmApp v1 result)
      TmApp t1 t2
        | not (isVal t1) ->
            let result = eval1 t1
             in checkError result (TmApp result t2)
      TmTyApp (TermNode _ (TmAnno (TermNode fi1 (TmAnno t11 ty1)) _)) ty -> TmTyApp (TermNode fi1 (TmAnno t11 ty1)) ty
      TmTyApp t1 ty
        | not (isVal t1) ->
            let result = eval1 t1
             in checkError result (TmTyApp result ty)
      TmTyApp (TermNode _ (TmTyAbs _ t11)) ty -> getTm (evalTyTermSubst ty t11)
      TmTyApp (TermNode _ (TmAnno (TermNode _ (TmTyAbs _ t11)) (TyForAll _ ty1))) ty2 -> TmAnno (evalTyTermSubst ty2 t11) (typingEvalSubst ty2 ty1)
      TmAnno (TermNode _ (TmAnno t11 ty1)) _ -> TmAnno t11 ty1
      TmAnno t1 ty
        | not $ isVal t1 ->
            let result = eval1 t1
             in checkError result $ TmAnno result ty
      _ -> TmError ("No rule applies" ++ showFileInfo (getFI t))
  where
    checkError :: TermNode -> Term -> Term
    checkError term result =
      case getTm term of
        TmError e -> TmError e
        _         -> result

type Counter = Int

eval' :: TermNode -> (Counter, TermNode)
eval' t = eval 0 t

eval :: Counter -> TermNode -> (Counter, TermNode)
eval n t@(TermNode _ (TmError _)) = (n, t)
eval n t
  | isVal t = (n, t)
  | otherwise = eval (n + 1) $ eval1 t

evalN :: Counter -> TermNode -> (Counter, TermNode)
evalN n t@(TermNode _ (TmError _)) = (n, t)
evalN n t
  | n <= 0 || isVal t = (n, t)
  | otherwise = evalN (n - 1) $ eval1 t
