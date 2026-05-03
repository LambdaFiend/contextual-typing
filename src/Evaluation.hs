module Evaluation where

import           Display
import           Helper
import           Syntax

eval1 :: TermNode -> TermNode
eval1 t =
  TermNode (getFI t) $
    case getTm t of
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst ConstNot)) (TyArrow _ ty2))) (TermNode _ (TmConst (ConstBool b))) -> TmAnno (TermNode fi1 (TmConst (ConstBool (not b)))) ty2
      TmApp (TermNode _ (TmConst ConstNot)) (TermNode _ (TmConst (ConstBool b))) -> TmConst (ConstBool (not b))
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst (ConstOpB op))) (TyArrow _ ty2))) (TermNode _ (TmConst (ConstBool b))) -> TmAnno (TermNode fi1 (TmConst (ConstOpBool op b))) ty2
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst (ConstOpBool op b1))) (TyArrow _ ty2))) (TermNode _ (TmConst (ConstBool b2))) -> TmAnno (TermNode fi1 (TmConst (ConstBool ((boolOpToOp op) b1 b2)))) ty2
      TmApp (TermNode _ (TmConst (ConstOpB op))) (TermNode _ (TmConst (ConstBool b))) -> TmConst (ConstOpBool op b)
      TmApp (TermNode _ (TmConst (ConstOpBool op b1))) (TermNode _ (TmConst (ConstBool b2))) -> TmConst (ConstBool ((boolOpToOp op) b1 b2))
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst (ConstOpF op))) (TyArrow _ ty2))) (TermNode _ (TmConst (ConstFloat u))) -> TmAnno (TermNode fi1 (TmConst (ConstOpFloat op u))) ty2
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst (ConstOpFloat op u1))) (TyArrow _ ty2))) (TermNode _ (TmConst (ConstFloat u2))) -> TmAnno (TermNode fi1 (TmConst (ConstFloat ((fracOpToOp op) u1 u2)))) ty2
      TmApp (TermNode _ (TmConst (ConstOpF op))) (TermNode _ (TmConst (ConstFloat u))) -> TmConst (ConstOpFloat op u)
      TmApp (TermNode _ (TmConst (ConstOpFloat op u1))) (TermNode _ (TmConst (ConstFloat u2))) -> TmConst (ConstFloat ((fracOpToOp op) u1 u2))
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst (ConstOpI op))) (TyArrow _ ty2))) (TermNode _ (TmConst (ConstInt n))) -> TmAnno (TermNode fi1 (TmConst (ConstOpInt op n))) ty2
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst (ConstOpInt op n1))) (TyArrow _ ty2))) (TermNode _ (TmConst (ConstInt n2))) -> TmAnno (TermNode fi1 (TmConst (ConstInt ((numOpToOp op) n1 n2)))) ty2
      TmApp (TermNode _ (TmConst (ConstOpI op))) (TermNode _ (TmConst (ConstInt n))) -> TmConst (ConstOpInt op n)
      TmApp (TermNode _ (TmConst (ConstOpInt op n1))) (TermNode _ (TmConst (ConstInt n2))) -> TmConst (ConstInt ((numOpToOp op) n1 n2))
      TmApp (TermNode fi1 (TmAnno (TermNode _ (TmTyAbs _ t1)) (TyForAll _ ty1))) (TermNode fi2 (TmConst c)) ->
        TmApp (TermNode fi1 (TmAnno (shift' 0 (-1) t1) (typingEvalSubst (constToType c) ty1))) (TermNode fi2 (TmConst c))
      TmApp (TermNode fi1 (TmAnno (TermNode _ (TmTyAbs _ t1)) (TyForAll _ ty1))) (TermNode fi2 (TmAnno t2 ty2)) ->
        TmApp (TermNode fi1 (TmAnno (shift' 0 (-1) t1) (typingEvalSubst ty2 ty1))) (TermNode fi2 (TmAnno t2 ty2))
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmAnno t11 ty1)) _)) t2 -> TmApp (TermNode fi1 (TmAnno t11 ty1)) t2
      TmApp (TermNode _ (TmAbs _ t11)) v2
        | isVal v2 ->
            getTm (evalSubst v2 t11)
      TmApp (TermNode _ (TmAnno (TermNode _ (TmAbs _ t11)) (TyArrow _ ty2))) v2
        | isVal v2 ->
            TmAnno (TermNode (getFI t) (getTm (evalSubst v2 t11))) ty2
      TmApp (TermNode _ (TmAbsAnno _ _ t11)) v2
        | isVal v2 ->
            getTm (evalSubst v2 t11)
      TmApp (TermNode _ (TmAnno (TermNode _ (TmAbsAnno _ _ t11)) (TyArrow _ ty2))) v2
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
             in checkError result (TmAnno result ty)
      TmAnno (TermNode _ (TmConst c)) _ -> TmConst c
      TmPair t1 t2
        | not (isVal t1) ->
            let result = eval1 t1
             in checkError result (TmPair result t2)
      TmPair t1 t2
        | not (isVal t1) ->
            let result = eval1 t2
             in checkError result (TmPair t1 result)
      TmFst t1
        | not (isVal t1) ->
            let result = eval1 t1
             in checkError result (TmFst result)
      TmSnd t1
        | not (isVal t1) ->
            let result = eval1 t1
             in checkError result (TmSnd result)
      TmFst (TermNode _ (TmPair t1 _)) -> getTm t1
      TmSnd (TermNode _ (TmPair _ t2)) -> getTm t2
      TmFst (TermNode _ (TmAnno (TermNode _ (TmPair t1 _)) (TyProduct ty1 _))) -> TmAnno t1 ty1
      TmSnd (TermNode _ (TmAnno (TermNode _ (TmPair _ t2)) (TyProduct _ ty2))) -> TmAnno t2 ty2
      TmIf t1 t2 t3
        | not (isVal t1) ->
            let result = eval1 t1
             in checkError result (TmIf result t2 t3)
      TmIf t1 t2 t3
        | not (isVal t2) ->
            let result = eval1 t2
             in checkError result (TmIf t1 result t3)
      TmIf t1 t2 t3
        | not (isVal t3) ->
            let result = eval1 t3
             in checkError result (TmIf t1 t2 result)
      TmIf (TermNode _ (TmConst (ConstBool True))) t2 _ -> getTm t2
      TmIf (TermNode _ (TmConst (ConstBool False))) _ t3 -> getTm t3
      TmIf (TermNode _ (TmAnno (TermNode _ (TmConst (ConstBool True))) _)) t2 _ -> getTm t2
      TmIf (TermNode _ (TmAnno (TermNode _ (TmConst (ConstBool False))) _)) _ t3 -> getTm t3
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
