module Evaluation where

import           Data.List
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
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst (ConstOpFB op))) (TyArrow _ ty2))) (TermNode _ (TmConst (ConstFloat u))) -> TmAnno (TermNode fi1 (TmConst (ConstOpFloatB op u))) ty2
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst (ConstOpFloatB op u1))) (TyArrow _ ty2))) (TermNode _ (TmConst (ConstFloat u2))) -> TmAnno (TermNode fi1 (TmConst (ConstBool ((fracBoolOpToOp op) u1 u2)))) ty2
      TmApp (TermNode _ (TmConst (ConstOpFB op))) (TermNode _ (TmConst (ConstFloat u))) -> TmConst (ConstOpFloatB op u)
      TmApp (TermNode _ (TmConst (ConstOpFloatB op u1))) (TermNode _ (TmConst (ConstFloat u2))) -> TmConst (ConstBool ((fracBoolOpToOp op) u1 u2))
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst (ConstOpIB op))) (TyArrow _ ty2))) (TermNode _ (TmConst (ConstInt n))) -> TmAnno (TermNode fi1 (TmConst (ConstOpIntB op n))) ty2
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst (ConstOpIntB op n1))) (TyArrow _ ty2))) (TermNode _ (TmConst (ConstInt n2))) -> TmAnno (TermNode fi1 (TmConst (ConstBool ((numBoolOpToOp op) n1 n2)))) ty2
      TmApp (TermNode _ (TmConst (ConstOpIB op))) (TermNode _ (TmConst (ConstInt n))) -> TmConst (ConstOpIntB op n)
      TmApp (TermNode _ (TmConst (ConstOpIntB op n1))) (TermNode _ (TmConst (ConstInt n2))) -> TmConst (ConstBool ((numBoolOpToOp op) n1 n2))
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst (ConstOpCB op))) (TyArrow _ ty2))) (TermNode _ (TmConst (ConstChar c))) -> TmAnno (TermNode fi1 (TmConst (ConstOpCharB op c))) ty2
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst (ConstOpCharB op c1))) (TyArrow _ ty2))) (TermNode _ (TmConst (ConstChar c2))) -> TmAnno (TermNode fi1 (TmConst (ConstBool ((charBoolOpToOp op) c1 c2)))) ty2
      TmApp (TermNode _ (TmConst (ConstOpCB op))) (TermNode _ (TmConst (ConstChar c))) -> TmConst (ConstOpCharB op c)
      TmApp (TermNode _ (TmConst (ConstOpCharB op c1))) (TermNode _ (TmConst (ConstChar c2))) -> TmConst (ConstBool ((charBoolOpToOp op) c1 c2))
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst ConstOpU)) (TyArrow _ ty2))) (TermNode _ (TmConst ConstUnit)) -> TmAnno (TermNode fi1 (TmConst ConstOpUnit)) ty2
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst ConstOpUnit)) (TyArrow _ ty2))) (TermNode _ (TmConst ConstUnit)) -> TmAnno (TermNode fi1 (TmConst (ConstBool True))) ty2
      TmApp (TermNode _ (TmConst ConstOpU)) (TermNode _ (TmConst ConstUnit)) -> TmConst ConstOpUnit
      TmApp (TermNode _ (TmConst ConstOpUnit)) (TermNode _ (TmConst ConstUnit)) -> TmConst (ConstBool True)
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst ConstOpNU)) (TyArrow _ ty2))) (TermNode _ (TmConst ConstUnit)) -> TmAnno (TermNode fi1 (TmConst ConstOpNUnit)) ty2
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst ConstOpNUnit)) (TyArrow _ ty2))) (TermNode _ (TmConst ConstUnit)) -> TmAnno (TermNode fi1 (TmConst (ConstBool False))) ty2
      TmApp (TermNode _ (TmConst ConstOpNU)) (TermNode _ (TmConst ConstUnit)) -> TmConst ConstOpNUnit
      TmApp (TermNode _ (TmConst ConstOpNUnit)) (TermNode _ (TmConst ConstUnit)) -> TmConst (ConstBool False)
      TmApp (TermNode _ (TmAnno (TermNode _ (TmConst ConstHead)) (TyArrow _ ty2))) (TermNode _ (TmCons t1 _)) -> TmAnno t1 ty2
      TmApp (TermNode _ (TmConst ConstHead)) (TermNode _ (TmCons t1 _)) -> getTm t1
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst ConstHead)) (TyArrow _ ty12))) (TermNode _ (TmAnno (TermNode _ (TmCons t1 _)) (TyList ty2))) -> TmAnno (TermNode fi1 (TmAnno t1 ty2)) ty12
      TmApp (TermNode _ (TmConst ConstHead)) (TermNode _ (TmAnno (TermNode _ (TmCons t1 _)) (TyList ty2))) -> TmAnno t1 ty2
      TmApp (TermNode _ (TmAnno (TermNode _ (TmConst ConstTail)) (TyArrow _ ty2))) (TermNode _ (TmCons _ t2)) -> TmAnno t2 ty2
      TmApp (TermNode _ (TmConst ConstTail)) (TermNode _ (TmCons _ t2)) -> getTm t2
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst ConstTail)) (TyArrow _ ty12))) (TermNode _ (TmAnno (TermNode _ (TmCons _ t2)) ty2)) -> TmAnno (TermNode fi1 (TmAnno t2 ty2)) ty12
      TmApp (TermNode _ (TmConst ConstTail)) (TermNode _ (TmAnno (TermNode _ (TmCons _ t2)) ty2)) -> TmAnno t2 ty2
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst ConstEmpty)) (TyArrow _ ty2))) (TermNode _ (TmCons _ _)) -> TmAnno (TermNode fi1 (TmConst (ConstBool False))) ty2
      TmApp (TermNode _ (TmConst ConstEmpty)) (TermNode _ (TmCons _ _)) -> TmConst (ConstBool False)
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst ConstEmpty)) (TyArrow _ ty12))) (TermNode _ (TmAnno (TermNode _ (TmCons _ _)) _)) -> TmAnno (TermNode fi1 (TmConst (ConstBool False))) ty12
      TmApp (TermNode _ (TmConst ConstEmpty)) (TermNode _ (TmAnno (TermNode _ (TmCons _ _)) _)) -> TmConst (ConstBool False)
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst ConstEmpty)) (TyArrow _ ty2))) (TermNode _ TmNil) -> TmAnno (TermNode fi1 (TmConst (ConstBool True))) ty2
      TmApp (TermNode _ (TmConst ConstEmpty)) (TermNode _ TmNil) -> TmConst (ConstBool True)
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmConst ConstEmpty)) (TyArrow _ ty12))) (TermNode _ (TmAnno (TermNode _ TmNil) _)) -> TmAnno (TermNode fi1 (TmConst (ConstBool True))) ty12
      TmApp (TermNode _ (TmConst ConstEmpty)) (TermNode _ (TmAnno (TermNode _ TmNil) _)) -> TmConst (ConstBool True)
      TmApp (TermNode fi1 (TmAnno (TermNode _ (TmTyAbs _ t1)) (TyForAll _ ty1))) (TermNode fi2 (TmConst c)) ->
        TmApp (TermNode fi1 (TmAnno (shift' 0 (-1) t1) (typingEvalSubst (constToType c) ty1))) (TermNode fi2 (TmConst c))
      TmApp (TermNode fi1 (TmAnno (TermNode _ (TmTyAbs _ t1)) (TyForAll _ ty1))) (TermNode fi2 (TmAnno t2 ty2)) ->
        TmApp (TermNode fi1 (TmAnno (shift' 0 (-1) t1) (typingEvalSubst ty2 ty1))) (TermNode fi2 (TmAnno t2 ty2))
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmAnno t11 ty1)) _)) t2 -> TmApp (TermNode fi1 (TmAnno t11 ty1)) t2
      TmApp (TermNode _ (TmAbsUnc xs t11)) v2@(TermNode _ (TmTuple ts))
        | length xs == length ts && isVal v2 ->
            getTm (foldr (\(y, n) x -> evalSubst (shift' 0 n y) x) t11 (reverse (zip (reverse ts) [1 ..])))
      TmApp (TermNode _ (TmAnno (TermNode _ (TmAbsUnc xs t11)) (TyArrow _ ty2))) v2@(TermNode _ (TmTuple ts))
        | length xs == length ts && isVal v2 ->
            TmAnno (TermNode (getFI t) (getTm (foldr (\(y, n) x -> evalSubst (shift' 0 n y) x) t11 (reverse (zip (reverse ts) [1 ..]))))) ty2
      TmApp (TermNode fi1 (TmAbsUncAnno xs tys t11)) v2@(TermNode _ (TmTuple ts))
        | length xs == length ts && isVal v2 ->
            getTm (foldr (\((y, z), n) x -> evalSubst (TermNode fi1 (TmAnno (shift' 0 n y) (tyShift 0 n z))) x) t11 (reverse (zip (reverse (zip ts tys)) [1 ..])))
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmAbsUncAnno xs tys t11)) (TyArrow _ ty2))) v2@(TermNode _ (TmTuple ts))
        | length xs == length ts && isVal v2 ->
            TmAnno (TermNode (getFI t) (getTm (foldr (\((y, z), n) x -> evalSubst (TermNode fi1 (TmAnno (shift' 0 n y) (tyShift 0 n z))) x) t11 (reverse (zip (reverse (zip ts tys)) [1 ..]))))) ty2
      TmApp (TermNode _ (TmAbs _ t11)) v2
        | isVal v2 ->
            getTm (evalSubst v2 t11)
      TmApp (TermNode _ (TmAnno (TermNode _ (TmAbs _ t11)) (TyArrow _ ty2))) v2
        | isVal v2 ->
            TmAnno (TermNode (getFI t) (getTm (evalSubst v2 t11))) ty2
      TmApp (TermNode fi1 (TmAbsAnno _ ty1 t11)) v2
        | isVal v2 ->
            getTm (evalSubst (TermNode fi1 (TmAnno v2 ty1)) t11)
      TmApp (TermNode _ (TmAnno (TermNode fi1 (TmAbsAnno _ ty1 t11)) (TyArrow _ ty2))) v2
        | isVal v2 ->
            TmAnno (TermNode (getFI t) (getTm (evalSubst (TermNode fi1 (TmAnno v2 ty1)) t11))) ty2
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
      TmTuple ts
        | not (all isVal ts) ->
            case dropWhile isVal ts of
              (t1 : ts') ->
                let result = eval1 t1
                 in checkError result (TmTuple (takeWhile isVal ts ++ [result] ++ ts'))
              [] -> TmError ("TmTuple: There was a strange evaluation error")
      TmProj t1 n
        | not (isVal t1) ->
            let result = eval1 t1
             in checkError result (TmProj result n)
      TmProj (TermNode _ (TmTuple ts)) n ->
        case ts !? (n - 1) of
          Just t1 -> getTm t1
          Nothing -> TmError ("Tuple projection is index out of bounds for the number: " ++ show n)
      TmProj (TermNode _ (TmAnno (TermNode _ (TmTuple ts)) (TyTuple tys))) n ->
        if length ts == length tys
          then case (ts !? (n - 1), tys !? (n - 1)) of
            (Just t1, Just ty1) -> TmAnno t1 ty1
            (_, _) -> TmError ("Tuple projection is index out of bounds for the number: " ++ show n)
          else TmError ("Tuple length is not the same as its annotation length: " ++ show (length ts) ++ " /= " ++ show (length tys))
      TmIf t1 t2 t3
        | not (isVal t1) ->
            let result = eval1 t1
             in checkError result (TmIf result t2 t3)
      TmIf (TermNode _ (TmConst (ConstBool True))) t2 _ -> getTm t2
      TmIf (TermNode _ (TmConst (ConstBool False))) _ t3 -> getTm t3
      TmIf (TermNode _ (TmAnno (TermNode _ (TmConst (ConstBool True))) _)) t2 _ -> getTm t2
      TmIf (TermNode _ (TmAnno (TermNode _ (TmConst (ConstBool False))) _)) _ t3 -> getTm t3
      TmFix (TermNode _ (TmAbs _ t2)) -> getTm (evalSubst t t2)
      TmFix (TermNode _ (TmAbsAnno _ _ t2)) -> getTm (evalSubst t t2)
      TmFix (TermNode _ (TmAbsUnc _ t2)) -> getTm (evalSubst t t2)
      TmFix (TermNode _ (TmAbsUncAnno _ _ t2)) -> getTm (evalSubst t t2)
      TmFix (TermNode _ (TmAnno (TermNode _ (TmAbs _ t2)) (TyArrow _ ty2))) -> TmAnno (evalSubst t t2) ty2
      TmFix (TermNode _ (TmAnno (TermNode _ (TmAbsAnno _ _ t2)) (TyArrow _ ty2))) -> TmAnno (evalSubst t t2) ty2
      TmFix (TermNode _ (TmAnno (TermNode _ (TmAbsUnc _ t2)) (TyArrow _ ty2))) -> TmAnno (evalSubst t t2) ty2
      TmFix (TermNode _ (TmAnno (TermNode _ (TmAbsUncAnno _ _ t2)) (TyArrow _ ty2))) -> TmAnno (evalSubst t t2) ty2
      TmFix t1
        | not (isVal t1) ->
            let result = eval1 t1
             in checkError result (TmFix result)
      TmCons t1 t2
        | not (isVal t1) ->
            let result = eval1 t1
             in checkError result (TmCons result t2)
      TmCons v1 t2
        | not (isVal t2) ->
            let result = eval1 t2
             in checkError result (TmCons v1 result)
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
