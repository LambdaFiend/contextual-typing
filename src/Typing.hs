module Typing where

import           Data.List
import           Display
import           Helper
import           Syntax

infer' :: TermNode -> Type
infer' t = infer [] [] t

infer :: TypingEnvironment -> SurroundingContext -> TermNode -> Type
infer tctx sctx t =
  case (sctx, getTm t) of
    ([], TmConst c) -> constToType c
    ([], TmVar k _ x)
      | k < length tctx ->
          case tctx !? k of
            Just (TmVarBind _ ty1) -> tyShift 0 k (ty1)
            _ -> TyError ("| infer AT-Var: index out of bounds for " ++ x ++ " of the typing environment Γ ≡ " ++ showTypingEnvironment nctx tctx)
    ([], TmAnno t1 ty1) ->
      case infer tctx [SType ty1] t1 of
        TyError e -> TyError ("| infer AT-Ann: failed to infer the term e ≡ " ++ showTerm nctx t1 ++ " using the annotation of type A ≡ " ++ "[" ++ showType nctx ty1 ++ "]" ++ " as the surrounding context Σ" ++ "\n" ++ e)
        _ -> ty1
    ([SType (TyArrow ty1 ty2)], TmAbs x t1) ->
      case infer (TmVarBind x (tyShift 0 1 ty1) : tctx) [SType (tyShift 0 1 ty2)] t1 of
        TyError e -> TyError ("| infer AT-Lam1: failed to infer e ≡ " ++ showTerm (x : nctx) t1 ++ " assuming " ++ x ++ " assigned to the type A ≡ " ++ showType nctx ty1 ++ " at the top of the typing environment Γ ≡ " ++ showTypingEnvironment nctx tctx ++ " and the type B ≡ " ++ showType nctx ty2 ++ " as the surrounding context Σ" ++ "\n" ++ e)
        ty3 -> TyArrow ty1 (tyShift 0 (-1) ty3)
    ((STerm t2 : sctx'), TmAbs x t1) ->
      case infer tctx [] t2 of
        TyError e -> TyError ("| infer AT-Lam2: failed to infer the contextual argument e2 ≡ " ++ showTerm nctx t2 ++ "\n" ++ e)
        ty1 ->
          case infer (TmVarBind x (tyShift 0 1 ty1) : tctx) (shiftSurroundingContext sctx' 1) t1 of
            TyError e -> TyError ("| infer AT-Lam2: failed to infer the term e ≡ " ++ showTerm (x : nctx) t1 ++ " assuming " ++ x ++ " assigned to the type A ≡ " ++ showType nctx ty1 ++ " at the top of the typing environment Γ ≡ " ++ showTypingEnvironment nctx tctx ++ " and the smaller surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx' ++ "\n" ++ e)
            ty2 -> TyArrow ty1 (tyShift 0 (-1) ty2)
    ([SType (TyArrow (TyTuple tys) ty2)], TmAbsUnc xs t1)
      | length tys == length xs ->
          let tctx' = reverse (map (\(x, y) -> TmVarBind x y) (zip xs (map (\(x, y) -> tyShift 0 y x) (zip tys [1 ..])))) ++ tctx
              nctx' = reverse xs ++ nctx
           in case infer tctx' [SType (tyShift 0 (length xs) ty2)] t1 of
                TyError e -> TyError ("| infer AT-Lam-UC1: failed to infer e ≡ " ++ showTerm nctx' t1 ++ " assuming the typing environment Γ ≡ " ++ showTypingEnvironment nctx' tctx' ++ " and the type B ≡ " ++ showType nctx ty2 ++ " as the surrounding context Σ" ++ "\n" ++ e)
                ty2' -> TyArrow (TyTuple tys) (tyShift 0 (-(length xs)) ty2')
    ([SType (TyArrow (TyTuple tys) _)], TmAbsUnc _ _) -> TyError ("| infer AT-Lam-UC1: the length of the tuple A ≡ " ++ showType nctx (TyTuple tys) ++ " is not the same as the length of the expected tuple by the uncurried function e ≡ " ++ showTerm nctx t)
    ((STerm (TermNode _ (TmTuple ts)) : sctx'), TmAbsUnc xs t1)
      | length ts == length xs ->
          let uncfn :: (TermNode, Int) -> Type
              uncfn (t2, n) =
                case infer tctx [] t2 of
                  TyError e -> TyError ("| infer AT-Lam-UC2: failed to infer e" ++ show n ++ " ≡ " ++ showTerm nctx t2 ++ " assuming the empty surrounding context Σ" ++ "\n" ++ e)
                  ty2 -> ty2
              tys = map uncfn (zip ts [1 ..])
           in if all (\x -> case x of TyError _ -> False; _ -> True) tys
                then
                  let tctx' = reverse (map (\(x, y) -> TmVarBind x y) (zip xs (map (\(x, y) -> tyShift 0 y x) (zip tys [1 ..])))) ++ tctx
                      nctx' = reverse xs ++ nctx
                   in case infer tctx' (shiftSurroundingContext sctx' (length xs)) t1 of
                        TyError e -> TyError ("| infer AT-Lam-UC2: failed to infer e ≡ " ++ showTerm nctx' t1 ++ " assuming the typing environment Γ ≡ " ++ showTypingEnvironment nctx' tctx' ++ " and the surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx ++ "\n" ++ e)
                        ty2' -> TyArrow (TyTuple tys) (tyShift 0 (-(length xs)) ty2')
                else case find (\x -> case x of TyError _ -> True; _ -> False) tys of
                  Just r -> r
                  Nothing -> TyError ("| infer AT-Lam-UC2: there was an unexpected error")
    ((STerm (TermNode fi (TmTuple ts)) : _), TmAbsUnc _ _) -> TyError ("| infer AT-Lam-UC1: the length of the contextual tuple e2 ≡ " ++ showTerm nctx (TermNode fi (TmTuple ts)) ++ " is not the same as the length of the expected tuple by the uncurried function e1 ≡ " ++ showTerm nctx t)
    ([SType (TyArrow (TyTuple tys1) ty2)], TmAbsUncAnno xs tys2 t1)
      | length tys1 == length xs ->
          if tys1 == tys2
            then
              let tctx' = reverse (map (\(x, y) -> TmVarBind x y) (zip xs (map (\(x, y) -> tyShift 0 y x) (zip tys1 [1 ..])))) ++ tctx
                  nctx' = reverse xs ++ nctx
               in case infer tctx' [SType (tyShift 0 (length xs) ty2)] t1 of
                    TyError e -> TyError ("| infer AT-AnnLam-UC1: failed to infer e ≡ " ++ showTerm nctx' t1 ++ " assuming the typing environment Γ ≡ " ++ showTypingEnvironment nctx' tctx' ++ " and the type B ≡ " ++ showType nctx ty2 ++ " as the surrounding context Σ" ++ "\n" ++ e)
                    ty2' -> TyArrow (TyTuple tys1) (tyShift 0 (-(length xs)) ty2')
            else TyError ("| infer AT-AnnLam-UC1: annotated lambda types from e ≡ " ++ showTerm nctx t ++ " are not equal to the contextual type information from the tuple type ≡ " ++ showType nctx (TyTuple tys1))
    ([SType (TyArrow (TyTuple tys1) _)], TmAbsUncAnno _ _ _) -> TyError ("| infer AT-AnnLam-UC1: the length of the tuple A ≡ " ++ showType nctx (TyTuple tys1) ++ " is not the same as the length of the expected tuple by the uncurried function e ≡ " ++ showTerm nctx t)
    ((STerm (TermNode _ (TmTuple ts)) : sctx'), TmAbsUncAnno xs tys2 t1)
      | length ts == length xs ->
          let uncfn :: ((TermNode, Type), Int) -> Type
              uncfn ((t2, ty2), n) =
                case infer tctx [SType ty2] t2 of
                  TyError e -> TyError ("| infer AT-AnnLam-UC2: failed to infer e" ++ show n ++ " ≡ " ++ showTerm nctx t2 ++ " assuming the type A" ++ show n ++ " as the surrounding context Σ" ++ "\n" ++ e)
                  ty2' -> ty2'
              tys = map uncfn (zip (zip ts tys2) [1 ..])
           in if all (\x -> case x of TyError _ -> False; _ -> True) tys
                then
                  let tctx' = reverse (map (\(x, y) -> TmVarBind x y) (zip xs (map (\(x, y) -> tyShift 0 y x) (zip tys [1 ..])))) ++ tctx
                      nctx' = reverse xs ++ nctx
                   in case infer tctx' (shiftSurroundingContext sctx' (length xs)) t1 of
                        TyError e -> TyError ("| infer AT-AnnLam-UC2: failed to infer e ≡ " ++ showTerm nctx' t1 ++ " assuming the typing environment Γ ≡ " ++ showTypingEnvironment nctx' tctx' ++ " and the surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx ++ "\n" ++ e)
                        ty2' -> TyArrow (TyTuple tys2) (tyShift 0 (-(length xs)) ty2')
                else case find (\x -> case x of TyError _ -> True; _ -> False) tys of
                  Just r -> r
                  Nothing -> TyError ("| infer AT-AnnLam-UC2: there was an unexpected error")
    ((STerm (TermNode fi (TmTuple ts)) : _), TmAbsUncAnno _ _ _) -> TyError ("| infer AT-Lam-UC1: the length of the contextual tuple e2 ≡ " ++ showTerm nctx (TermNode fi (TmTuple ts)) ++ " is not the same as the length of the expected tuple by the uncurried function e1 ≡ " ++ showTerm nctx t)
    ([], TmAbsUncAnno xs tys t1) ->
      let tctx' = reverse (map (\(x, y) -> TmVarBind x y) (zip xs (map (\(x, y) -> tyShift 0 y x) (zip tys [1 ..])))) ++ tctx
          nctx' = reverse xs ++ nctx
       in case infer tctx' [] t1 of
            TyError e -> TyError ("| infer AT-AnnLam-UC3: failed to infer e ≡ " ++ showTerm nctx' t1 ++ " assuming the typing environment Γ ≡ " ++ showTypingEnvironment nctx' tctx' ++ "\n" ++ e)
            ty2' -> TyArrow (TyTuple tys) (tyShift 0 (-(length xs)) ty2')
    ([SType (TyArrow ty1 ty2)], TmAbsAnno x ty21 t1) ->
      if ty1 == ty21
        then case infer (TmVarBind x (tyShift 0 1 ty1) : tctx) [SType (tyShift 0 1 ty2)] t1 of
          TyError e -> TyError ("| infer AT-AnnLam1: failed to infer e ≡ " ++ showTerm (x : nctx) t1 ++ " assuming " ++ x ++ " assigned to the type A ≡ " ++ showType nctx ty1 ++ " at the top of the typing environment Γ ≡ " ++ showTypingEnvironment nctx tctx ++ " and the type B ≡ " ++ showType nctx ty2 ++ " as the surrounding context Σ" ++ "\n" ++ e)
          ty3 -> TyArrow ty1 (tyShift 0 (-1) ty3)
        else TyError ("| infer AT-AnnLam1: there was a type mismatch between type A ≡ " ++ showType nctx ty1 ++ " and from the lambda annotation of the term e ≡ " ++ showTerm nctx t ++ " the type C ≡ " ++ showType nctx ty21)
    ((STerm t2 : sctx'), TmAbsAnno x ty21 t1) ->
      case infer tctx [SType ty21] t2 of
        TyError e -> TyError ("| infer AT-AnnLam2: failed to infer the contextual argument e2 ≡ " ++ showTerm nctx t2 ++ " assuming the annotated type A ≡ " ++ showType nctx ty21 ++ " as the surrounding context Σ" ++ "\n" ++ e)
        ty1 ->
          case infer (TmVarBind x (tyShift 0 1 ty1) : tctx) (shiftSurroundingContext sctx' 1) t1 of
            TyError e -> TyError ("| infer AT-AnnLam2: failed to infer the term e ≡ " ++ showTerm (x : nctx) t1 ++ " assuming " ++ x ++ " assigned to the type A ≡ " ++ showType nctx ty1 ++ " at the top of the typing environment Γ ≡ " ++ showTypingEnvironment nctx tctx ++ " and the smaller surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx' ++ "\n" ++ e)
            ty2 -> TyArrow ty1 (tyShift 0 (-1) ty2)
    ([], TmAbsAnno x ty21 t1) ->
      case infer (TmVarBind x (tyShift 0 1 ty21) : tctx) [] t1 of
        TyError e -> TyError ("| infer AT-AnnLam3: failed to infer the contextual argument e ≡ " ++ showTerm (x : nctx) t1 ++ "\n" ++ e)
        ty1 -> TyArrow ty21 (tyShift 0 (-1) ty1)
    (_, TmApp t1 t2) ->
      case infer tctx (STerm t2 : sctx) t1 of
        TyError e -> TyError ("| infer AT-App: failed to infer the term e1 ≡ " ++ showTerm nctx t1 ++ " assuming the term e2 ≡ " ++ showTerm nctx t2 ++ " at the top of the surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx ++ "\n" ++ e)
        TyArrow _ ty2 -> ty2
        ty1 -> TyError ("| infer AT-App: arrow type expected but got: " ++ "\n" ++ showType nctx ty1)
    ([], TmTyAbs x t1) ->
      case infer (TyVarBind x : tctx) [] t1 of
        TyError e -> TyError ("| infer AT-TLam1: failed to infer the term e ≡ " ++ showTerm (x : nctx) t1 ++ " assuming the type variable α ≡ " ++ x ++ " at the top of the typing environment Γ ≡ " ++ showTypingEnvironment nctx tctx ++ " and assuming the empty surrounding context Σ" ++ "\n" ++ e)
        ty1 -> TyForAll x ty1
    ([SType (TyForAll _ ty1)], TmTyAbs x2 t1) ->
      case infer (TyVarBind x2 : tctx) [SType (tySubst 0 0 (TyVar 0 (1 + length nctx) x2) ty1)] t1 of
        TyError e -> TyError ("| infer AT-TLam2: failed to infer the term e ≡ " ++ showTerm (x2 : nctx) t1 ++ " assuming the type B ≡ " ++ showType (x2 : nctx) ty1 ++ " as the surrounding context Σ and the type variable α ≡ " ++ x2 ++ " at the top of the typing environment Γ ≡ " ++ showTypingEnvironment nctx tctx ++ "\n" ++ e)
        ty2 -> TyForAll x2 ty2
    (_, TmTyApp t1 ty1) ->
      case infer tctx [] t1 of
        TyError e -> TyError ("| infer AT-TApp: failed to infer the term e ≡ " ++ showTerm nctx t1 ++ " assuming the empty surrounding context Σ" ++ "\n" ++ e)
        TyForAll _ ty2 ->
          let ty2' = typingEvalSubst ty1 ty2
           in case subtypeInfer tctx [] ty2' sctx of
                (_, TyError e) -> TyError ("| infer AT-TApp: failed to subtype infer the term's e ≡ " ++ showTerm nctx t1 ++ " inferred, and substituted with type A ≡ " ++ showType nctx ty1 ++ ", type B ≡ " ++ showType nctx ty2' ++ e)
                (Just [], ty3) -> ty3
                (Just stctx, _) -> TyError ("| infer AT-TApp: subtype infer returned a subtyping environment Δ expected to be empty, but got ≡ " ++ showSubtypingEnvironment nctx stctx)
                (Nothing, _) -> TyError ("| infer AT-TApp: subtype infer returned a subtyping environment Δ expected to be empty, but got nothing")
        ty2 -> TyError ("| infer AT-TApp: expected to infer, for e ≡ " ++ showTerm nctx t1 ++ ", a for-all type of the form ∀α.B, but got " ++ showType nctx ty2)
    ([], TmTuple ts) ->
      let tuplefn :: (TermNode, Int) -> Type
          tuplefn (t1, n) =
            case infer tctx [] t1 of
              TyError e -> TyError ("| infer AT-Tuple: failed to infer e" ++ show n ++ " ≡ " ++ showTerm nctx t1 ++ " assuming the empty surrounding context Σ" ++ "\n" ++ e)
              ty1 -> ty1
          tys = map tuplefn (zip ts [1 ..])
       in if all (\x -> case x of TyError _ -> False; _ -> True) tys
            then TyTuple tys
            else case find (\x -> case x of TyError _ -> True; _ -> False) tys of
              Just r -> r
              Nothing -> TyError ("| infer AT-Tuple: there was an unexpected error")
    ([SType (TyTuple tys)], TmTuple ts)
      | length tys == length ts ->
          let tuplefn :: ((TermNode, Type), Int) -> Type
              tuplefn ((t1, ty1), n) =
                case infer tctx [SType ty1] t1 of
                  TyError e -> TyError ("| infer AT-AnnTuple: failed to infer e" ++ show n ++ " ≡ " ++ showTerm nctx t1 ++ " assuming the type A" ++ show n ++ " ≡ " ++ "[" ++ showType nctx ty1 ++ "]" ++ " as the surrounding context Σ" ++ "\n" ++ e)
                  ty1' -> ty1'
              tys' = map tuplefn (zip (zip ts tys) [1 ..])
           in if all (\x -> case x of TyError _ -> False; _ -> True) tys'
                then TyTuple tys'
                else case find (\x -> case x of TyError _ -> True; _ -> False) tys' of
                  Just r -> r
                  Nothing -> TyError ("| infer AT-AnnTuple: there was an unexpected error")
    ([SType (TyTuple tys)], TmTuple _) -> TyError ("| infer AT-AnnTuple: the length of A ≡ " ++ showType nctx (TyTuple tys) ++ " is not the same as the length of e ≡ " ++ showTerm nctx t)
    (_, TmProj t1 n) ->
      case infer tctx ((SProj n) : sctx) t1 of
        TyError e -> TyError ("| infer AT-Proj: failed to infer e ≡ " ++ showTerm nctx t1 ++ " assuming ." ++ show n ++ " at the top of the surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx ++ "\n" ++ e)
        TyTuple tys
          | (n - 1) < length tys ->
              case tys !? (n - 1) of
                Just r -> r
                Nothing -> TyError ("| infer AT-AnnTuple: there was an unexpected error")
        TyTuple _ -> TyError ("| infer AT-Proj: expected to have enough length for the projection number " ++ show n ++ ", but didn't get the right length from the inferred type of e ≡ " ++ showTerm nctx t1 ++ " assuming ." ++ show n ++ " at the top of the surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx)
        _ -> TyError ("| infer AT-Proj: expected the tuple type but got something else from the inferred type of e ≡ " ++ showTerm nctx t1 ++ " assuming ." ++ show n ++ " at the top of the surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx)
    (((SProj n) : sctx'), TmTuple ts) ->
      if (n - 1) < length ts
        then
          let tys = ruleATTupleProj tctx sctx' (zip ts [1 ..]) n
           in if all (\x -> case x of TyError _ -> False; _ -> True) tys
                then TyTuple tys
                else case find (\x -> case x of TyError _ -> True; _ -> False) tys of
                  Just r -> r
                  Nothing -> TyError ("| infer AT-TupleProj: there was an unexpected error")
        else TyError ("| infer AT-TupleProj: expected to have enough length for the projection number " ++ show n ++ ", but didn't get the right length from the tuple e ≡ " ++ showTerm nctx t)
    (_, TmIf t1 t2 t3) ->
      case infer tctx [SType TyBool] t1 of
        TyError e -> TyError ("| infer AT-If: failed to infer e1 ≡ " ++ showTerm nctx t1 ++ " assuming the type A ≡ TyBool as the surrounding context Σ" ++ "\n" ++ e)
        TyBool ->
          case (infer tctx sctx t2, infer tctx sctx t3) of
            (TyError e, _) -> TyError ("| infer AT-If: failed to infer e2 ≡ " ++ showTerm nctx t1 ++ " assuming the surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx ++ "\n" ++ e)
            (_, TyError e) -> TyError ("| infer AT-If: failed to infer e3 ≡ " ++ showTerm nctx t1 ++ " assuming the surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx ++ "\n" ++ e)
            (ty2, ty3) | ty2 == ty3 -> ty2
            (ty2, ty3) -> TyError ("| infer AT-If: type mismatch between the type B ≡ " ++ showType nctx ty2 ++ " and the type C ≡ " ++ showType nctx ty3 ++ ", of term e2 ≡ " ++ showTerm nctx t2 ++ " and the term e3 ≡ " ++ showTerm nctx t3 ++ ", respectively")
        _ -> TyError ("| infer AT-If: expected TyBool but got something else from the type of inferring e1 ≡ " ++ showTerm nctx t1 ++ " assuming the type A ≡ TyBool as the surrounding context Σ")
    (_, _)
      | isGenericConsumer t ->
          case infer tctx [] t of
            TyError e -> TyError ("| infer AT-Sub: failed to infer the term g ≡ " ++ showTerm nctx t ++ "\n" ++ e)
            ty1 ->
              case subtypeInfer tctx [] ty1 sctx of
                (_, TyError e) -> TyError ("| infer AT-Sub: failed to subtype infer the term's g ≡ " ++ showTerm nctx t ++ " inferred type A ≡ " ++ showType nctx ty1 ++ " against the surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx ++ "\n" ++ e)
                (Just [], ty2) -> ty2
                (Just stctx, _) -> TyError ("| infer AT-Sub: subtype infer returned a subtyping environment Δ expected to be empty, but got ≡ " ++ showSubtypingEnvironment nctx stctx)
                (Nothing, _) -> TyError ("| infer AT-Sub: subtype infer returned a subtyping environment Δ expected to be empty, but got nothing")
    (_, _) -> TyError ("| infer No rules apply: the typing environment Γ ≡ " ++ showTypingEnvironment nctx tctx ++ ", the surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx ++ " and the term e ≡ " ++ showTerm nctx t)
  where
    nctx = map getNameTy tctx

ruleATTupleProj :: TypingEnvironment -> SurroundingContext -> [(TermNode, Int)] -> Int -> [Type]
ruleATTupleProj _ _ [] _ = []
ruleATTupleProj tctx sctx ((t1, n) : ts) k =
  let sctx' = if n == k then sctx else []
   in case infer tctx sctx' t1 of
        TyError e -> TyError ("| infer AT-Tuple-Proj: failed to infer e" ++ show n ++ " ≡ " ++ showTerm nctx t1 ++ " assuming the surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx' ++ "\n" ++ e) : []
        ty1 -> ty1 : ruleATTupleProj tctx sctx ts k
  where
    nctx = map getNameTy tctx

subtypeInfer :: TypingEnvironment -> SubtypingEnvironment -> Type -> SurroundingContext -> (Maybe SubtypingEnvironment, Type)
subtypeInfer tctx stctx ty sctx =
  case (ty, sctx) of
    (_, []) ->
      if isClosedType stctx ty
        then (Just stctx, substCtxToTy stctx ty)
        else (Nothing, TyError ("| subtype infer AS-Empty: type A ≡ " ++ showType nctx ty ++ " is not closed under the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx))
    (_, [SType ty1]) ->
      case subtypeCheck tctx stctx ty PositivePolarity (tyShift 0 (length stctx) ty1) of
        (Nothing, Nothing) -> (Nothing, TyError ("| subtype infer AS-Type: expected subtyping environment Δ' but got nothing, despite no subtype check errors"))
        (Just stctx', Nothing) -> (Just stctx', ty1)
        (_, Just e) -> (Nothing, TyError ("| subtype infer AS-Type: failed to subtype check the type A ≡ " ++ showType nctx ty ++ "\n" ++ e))
    (TyForAll x ty1, (STerm _ : _)) ->
      case subtypeInfer tctx (UnsolvedTyVar x : stctx) ty1 sctx of
        (_, TyError e) -> (Nothing, TyError ("| subtype infer AS-∀L: failed to subtype infer A ≡ " ++ showType (x : nctx) ty1 ++ " assuming α̂^ ≡ " ++ x ++ " at the top of the subtyping context Δ ≡ " ++ showSubtypingEnvironment ntctx stctx ++ "\n" ++ e))
        (Just (_ : stctx'), ty2) -> (Just stctx', ty2)
        (Just [], _) -> (Nothing, TyError ("| subtype infer AS-∀L: expected non-empty subtyping environment Δ' but got empty"))
        (Nothing, _) -> (Nothing, TyError ("| subtype infer AS-∀L: expected non-empty subtyping environment Δ' but got nothing"))
    (TyArrow (TyTuple tys) ty2, (STerm (TermNode _ (TmTuple ts)) : sctx')) ->
      let (tys', stctx') = ruleASTermUC tctx stctx (zip (zip tys ts) [1 ..])
       in if all (\x -> case x of TyError _ -> False; _ -> True) tys'
            then case subtypeInfer tctx stctx' ty2 sctx' of
              (_, TyError e) -> (Nothing, TyError ("| infer AS-Term-UC: failed to subtype infer B ≡ " ++ showType nctx ty2 ++ " assuming the subtyping environment Δ' ≡ " ++ showSubtypingEnvironment ntctx stctx ++ " and the surrounding context Σ ≡ " ++ showSurroundingContext ntctx sctx ++ "\n" ++ e))
              (Just stctx'', ty3) -> (Just stctx'', TyArrow (TyTuple tys') ty3)
              (Nothing, _) -> (Nothing, TyError ("| infer AS-Term-UC: expected the subtyping environment Δ'' but got nothing"))
            else case find (\x -> case x of TyError _ -> True; _ -> False) tys' of
              Just r -> (Nothing, r)
              Nothing -> (Nothing, TyError ("| infer AS-Term-UC: there was an unexpected error"))
    (TyArrow ty1 ty2, (STerm t1 : sctx'))
      | isClosedType stctx ty1 ->
          let sty1 = substCtxToTy stctx ty1
           in case infer tctx [SType (substCtxToTy stctx ty1)] t1 of
                TyError e -> (Nothing, TyError ("| subtype infer AS-Trm-C: failed to infer the term e ≡ " ++ showTerm ntctx t1 ++ " assuming [Δ]A ≡ " ++ "[" ++ showType nctx sty1 ++ "]" ++ " as the surrounding context Σ" ++ "\n" ++ e))
                _ ->
                  case subtypeInfer tctx stctx ty2 sctx' of
                    (_, TyError e) -> (Nothing, TyError ("| subtype infer AS-Trm-C: failed to subtype infer B ≡ " ++ showType nctx ty2 ++ " assuming the surrounding context Σ ≡ " ++ showSurroundingContext ntctx sctx ++ "\n" ++ e))
                    (Just stctx', ty3) -> (Just stctx', TyArrow sty1 ty3)
                    (Nothing, _) -> (Nothing, TyError ("| subtype infer AS-Trm-C: expected subtyping environment Δ' but got nothing"))
    (TyArrow ty1 ty2, (STerm t1 : sctx'))
      | not (isClosedType stctx ty) ->
          case infer tctx [] t1 of
            TyError e -> (Nothing, TyError ("| subtype infer AS-Trm-O: failed to infer e ≡ " ++ showTerm ntctx t1 ++ " assuming an empty surrounding context" ++ "\n" ++ e))
            ty3 ->
              case subtypeCheck tctx stctx (tyShift 0 (length stctx) ty3) NegativePolarity ty1 of
                (Nothing, Nothing) -> (Nothing, TyError ("| subtype infer AS-Trm-O: expected subtyping environment Δ' but got nothing, despite no subtype check errors"))
                (Just stctx', Nothing) ->
                  case subtypeInfer tctx stctx' ty2 sctx' of
                    (_, TyError e) -> (Nothing, TyError ("| subtype infer AS-Trm-O: failed to subtype infer the type B ≡ " ++ showType nctx ty2 ++ " assuming the subtyping environment Δ' ≡ " ++ showSubtypingEnvironment ntctx stctx' ++ " and the surrounding context Σ ≡ " ++ showSurroundingContext ntctx sctx' ++ "\n" ++ e))
                    (Just stctx'', ty4) -> (Just stctx'', TyArrow ty3 ty4)
                    (Nothing, _) -> (Nothing, TyError ("| subtype infer AS-Trm-C: expected subtyping environment Δ'' but got nothing"))
                (_, Just e) -> (Nothing, TyError ("| subtype infer AS-Trm-O: failed to subtype check the type C ≡ " ++ showType nctx ty3 ++ " assuming the surrounding context Σ as the type A ≡ " ++ "[" ++ showType nctx ty1 ++ "]" ++ "\n" ++ e))
    (TyVar k _ x, _)
      | k < length stctx && (case stctx !? k of Just s -> isSolved s; Nothing -> False) ->
          case stctx !? k of
            Just (SolvedTyVar x' ty1)
              | x == x' ->
                  case subtypeInfer tctx stctx (tyShift 0 (length stctx) ty1) sctx of
                    (_, TyError e) -> (Nothing, TyError ("| subtype infer AS-SVar: failed to subtype infer the type A ≡ " ++ showType nctx ty1 ++ "\n" ++ e))
                    (Just (s : stctx'), ty2) -> (Just (s : stctx'), ty2)
                    (Just [], _) -> (Nothing, TyError ("| subtype infer AS-SVar: expected non-empty Δ but got an empty Δ"))
                    (Nothing, _) -> (Nothing, TyError ("| subtype infer AS-SVar: expected non-empty Δ but got nothing"))
            Just (SolvedTyVar x' _) -> (Nothing, TyError ("| subtype infer AS-SVar: expected α ≡ " ++ x ++ " but got α ≡ " ++ x'))
            Just _ -> (Nothing, TyError ("| subtype infer AS-SVar: expected α to be solved but α ≡ " ++ x ++ " is unsolved and thus name mismatches are not checked"))
            Nothing -> (Nothing, TyError ("| subtype infer AS-SVar: index out of bounds for " ++ x ++ " of the typing environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx))
    (TyVar k _ x, (STerm t1 : _))
      | k < length stctx && (case stctx !? k of Just s -> isUnsolved s; Nothing -> False) ->
          case subtypeInferAux tctx sctx of
            TyError e -> (Nothing, TyError ("| subtype infer AS-Infs: failed to subtype infer auxiliary judgement assuming e ≡ " ++ showTerm ntctx t1 ++ " at the top of the surrounding context Σ ≡ " ++ showSurroundingContext ntctx sctx ++ "\n" ++ e))
            ty1 ->
              case drop (k - 1) stctx of
                (UnsolvedTyVar x' : stctx') | x == x' -> (Just (take (k - 1) stctx ++ (SolvedTyVar x' ty1 : stctx')), ty1)
                (UnsolvedTyVar x' : _) -> (Nothing, TyError ("| subtype infer AS-Infs: expected unsolved α ≡ " ++ x ++ " but got unsolved α ≡ " ++ x'))
                (_ : _) -> (Nothing, TyError ("| subtype infer AS-Infs: expected unsolved type variable for α ≡ " ++ x ++ " in the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx ++ " but didn't get it"))
                [] -> (Nothing, TyError ("| subtype infer AS-Infs: index out of bounds for " ++ x ++ " in the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx))
    (TyTuple tys, ((SProj n) : sctx')) ->
      case tys !? (n - 1) of
        Just ty1 ->
          case subtypeInfer tctx stctx ty1 sctx' of
            (_, TyError e) -> (Nothing, TyError ("| subtype infer AS-Proj: failed to subtype infer the type A ≡ " ++ showType nctx ty1 ++ " assuming Σ ≡ " ++ showSurroundingContext ntctx sctx' ++ "\n" ++ e))
            (Just stctx', ty1') -> (Just stctx', TyTuple (take (n - 1) tys ++ [ty1'] ++ drop n tys))
            (Nothing, _) -> (Nothing, TyError ("| subtype infer AS-Proj: expected a subtyping environment Δ' but got nothing"))
        Nothing -> (Nothing, TyError ("| subtype infer AS-Proj: the projection number ≡ " ++ show n ++ " is out of bounds for the tuple type A ≡ " ++ showType nctx ty))
    (_, _) -> (Nothing, TyError ("| subtype infer No rules apply: the typing environment Γ ≡ " ++ showTypingEnvironment ntctx tctx ++ ", the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx ++ ", the type A ≡ " ++ showType nctx ty ++ " and the surrounding context Σ ≡ " ++ showSurroundingContext ntctx sctx))
  where
    nctx = nstctx ++ ntctx
    ntctx = map getNameTy tctx
    nstctx = map getNameSubTy stctx

subtypeInferAux :: TypingEnvironment -> SurroundingContext -> Type
subtypeInferAux tctx sctx =
  case sctx of
    [SType ty1] -> ty1
    (STerm t1 : sctx') ->
      case infer tctx [] t1 of
        TyError e -> TyError ("| subtype infer auxiliary judgement AS-Infer-Con: failed to infer the term e ≡ " ++ showTerm nctx t1 ++ " assuming the empty surrounding context Σ" ++ "\n" ++ e)
        ty1 ->
          case subtypeInferAux tctx sctx' of
            TyError e -> TyError ("| subtype infer auxiliary judgement AS-Infer-Con: failed to subtype infer auxiliary judgement the surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx ++ "\n" ++ e)
            ty2 -> TyArrow ty1 ty2
    _ -> TyError ("| subtype infer auxiliary judgement No rules apply: the typing environment Γ ≡ " ++ showTypingEnvironment nctx tctx ++ " and the surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx)
  where
    nctx = map getNameTy tctx

subtypeCheck :: TypingEnvironment -> SubtypingEnvironment -> Type -> Polarity -> Type -> (Maybe SubtypingEnvironment, Maybe String)
subtypeCheck tctx stctx ty1 pol ty2 =
  case (ty1, pol, ty2) of
    (TyInt, _, TyInt) -> (Just stctx, Nothing)
    (TyFloat, _, TyFloat) -> (Just stctx, Nothing)
    (TyBool, _, TyBool) -> (Just stctx, Nothing)
    (TyUnit, _, TyUnit) -> (Just stctx, Nothing)
    (TyVar k1 _ x1, _, TyVar k2 _ x2)
      | x1 == x2 && k1 == k2 ->
          if ((k1 < length tctx && elem x1 ntctx) || (k1 < length stctx && elem x1 nstctx))
            then (Just stctx, Nothing)
            else (Nothing, Just ("| subtype check AS-UVar: α ≡ " ++ x1 ++ show k1 ++ show k2 ++ x2 ++ " is either out-of-scope or somehow does not belong to the typing environment Γ ≡ " ++ showTypingEnvironment ntctx tctx ++ " and to the Δ ≡ " ++ showSubtypingEnvironment ntctx stctx))
    (TyVar k _ x, PositivePolarity, _)
      | k < length stctx && (case stctx !? k of Just s -> isUnsolved s; Nothing -> False) ->
          case drop k stctx of
            (UnsolvedTyVar x' : stctx') | x == x' -> (Just (take k stctx ++ (SolvedTyVar x' (tyShift 0 (-(length stctx)) ty2) : stctx')), Nothing)
            (UnsolvedTyVar x' : _) -> (Nothing, Just ("| subtype check AS-MVar-L: expected unsolved α ≡ " ++ x ++ " but got unsolved α ≡ " ++ x'))
            (_ : _) -> (Nothing, Just ("| subtype check AS-MVar-L: expected unsolved type variable for α ≡ " ++ x ++ " in the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx ++ " but didn't get it"))
            [] -> (Nothing, Just ("| subtype check AS-MVar-L: index out of bounds for " ++ x ++ " in the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx))
    (_, NegativePolarity, TyVar k _ x)
      | k < length stctx && (case stctx !? k of Just s -> isUnsolved s; Nothing -> False) ->
          case drop k stctx of
            (UnsolvedTyVar x' : stctx') | x == x' -> (Just (take k stctx ++ (SolvedTyVar x' (tyShift 0 (-(length stctx)) ty1) : stctx')), Nothing)
            (UnsolvedTyVar x' : _) -> (Nothing, Just ("| subtype check AS-MVar-R: expected unsolved α ≡ " ++ x ++ " but got unsolved α ≡ " ++ x'))
            (_ : _) -> (Nothing, Just ("| subtype check AS-MVar-R: expected unsolved type variable for α ≡ " ++ x ++ " in the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx ++ " but didn't get it"))
            [] -> (Nothing, Just ("| subtype check AS-MVar-R: index out of bounds for " ++ x ++ " in the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx))
    (TyVar k _ x, PositivePolarity, _)
      | k < length stctx && (case stctx !? k of Just s -> isSolved s; Nothing -> False) ->
          case findSolution stctx x k of
            Just ty2' | (tyShift 0 (-(length stctx)) ty2) == ty2' -> (Just stctx, Nothing)
            Just ty2' -> (Nothing, Just ("| subtype check AS-SVar-L: α's ≡ " ++ x ++ " solution ≡ " ++ showType nctx ty2' ++ " does not match A ≡ " ++ showType nctx ty2))
            Nothing -> (Nothing, Just ("| subtype check AS-SVar-L: there's not solution for α ≡ " ++ x))
    (_, PositivePolarity, TyVar k _ x)
      | k < length stctx && (case stctx !? k of Just s -> isSolved s; Nothing -> False) ->
          case findSolution stctx x k of
            Just ty1' | (tyShift 0 (-(length stctx)) ty1) == ty1' -> (Just stctx, Nothing)
            Just ty1' -> (Nothing, Just ("| subtype check AS-SVar-L: α's ≡ " ++ x ++ " solution ≡ " ++ showType nctx ty1' ++ " does not match A ≡ " ++ showType nctx ty1))
            Nothing -> (Nothing, Just ("| subtype check AS-SVar-L: there's no solution for α ≡ " ++ x ++ " in the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx))
    (TyArrow ty11 ty12, _, TyArrow ty21 ty22) ->
      case subtypeCheck tctx stctx ty21 (negatePolarity pol) ty11 of
        (_, Just e) -> (Nothing, Just ("| subtype check AS-Arr: failed to subtype check the type C ≡ " ++ showType nctx ty21 ++ " against the type A ≡ " ++ showType nctx ty11 ++ "\n" ++ e))
        (Just stctx', Nothing) ->
          case subtypeCheck tctx stctx' ty12 pol ty22 of
            (_, Just e) -> (Nothing, Just ("| subtype check AS-Arr: failed to subtype check the type A ≡ " ++ showType nctx ty12 ++ " against the type D ≡ " ++ showType nctx ty22 ++ "\n" ++ e))
            (Just stctx'', Nothing) -> (Just stctx'', Nothing)
            (Nothing, _) -> (Nothing, Just ("| subtype check AS-Arr: expected subtyping environment Δ' but got nothing"))
        (Nothing, _) -> (Nothing, Just ("| subtype check AS-Arr: expected subtyping environment Δ' but got nothing"))
    (TyForAll _ ty11, _, TyForAll x2 ty21) ->
      case subtypeCheck tctx (UniversalTyVar x2 : stctx) (tySubst 0 0 (TyVar 0 (1 + length nctx) x2) ty11) pol ty21 of
        (_, Just e) -> (Nothing, Just ("| subtype check AS-Arr: failed to subtype check the type A ≡ " ++ showType (x2 : nctx) ty11 ++ " against the type B ≡ " ++ showType (x2 : nctx) ty21 ++ " assuming the universal type variable α ≡ " ++ x2 ++ " at the top of the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx ++ "\n" ++ e))
        (Just stctx', Nothing) ->
          case stctx' of
            (var : stctx'') | getNameSubTy var == x2 -> (Just stctx'', Nothing)
            (_ : _) -> (Nothing, Just ("| subtype check AS-∀: expected the top of Δ' to be a variable binding of α ≡ " ++ x2 ++ " but got another name"))
            [] -> (Nothing, Just ("| subtype check AS-∀: the subtyping environment Δ' is empty and shouldn't be"))
        (Nothing, _) -> (Nothing, Just ("| subtype check AS-∀: expected subtyping environment Δ' but got nothing"))
    (TyTuple tys1, _, TyTuple tys2) ->
      if length tys1 == length tys2
        then ruleASTuple tctx stctx (zip (zip tys1 tys2) [1 ..]) pol
        else (Nothing, Just ("| subtype AS-Tuple: tuple A's length ≡ " ++ show (length tys1) ++ " is not the same as tuple B's length ≡ " ++ show (length tys2)))
    (_, _, _) -> (Nothing, Just ("| subtype check No rules apply: the typing environment Γ ≡ " ++ showTypingEnvironment ntctx tctx ++ ", the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx ++ ", the type A ≡ " ++ showType nctx ty1 ++ ", the polarity is " ++ showPolarity pol ++ " and the type B ≡ " ++ showType nctx ty2))
  where
    nctx = nstctx ++ ntctx
    ntctx = map getNameTy tctx
    nstctx = map getNameSubTy stctx

ruleASTuple :: TypingEnvironment -> SubtypingEnvironment -> [((Type, Type), Int)] -> Polarity -> (Maybe SubtypingEnvironment, Maybe String)
ruleASTuple _ stctx [] _ = (Just stctx, Nothing)
ruleASTuple tctx stctx (((ty1, ty2), n) : tys) pol =
  case subtypeCheck tctx stctx ty1 pol ty2 of
    (_, Just e) -> (Nothing, Just ("| subtype check AS-Tuple: failed to subtype check the type A" ++ show n ++ " ≡ " ++ showType nctx ty1 ++ " against the type C" ++ show n ++ " ≡ " ++ showType nctx ty2 ++ " assuming the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx ++ "\n" ++ e))
    (Just stctx', Nothing) -> ruleASTuple tctx stctx' tys pol
    (Nothing, _) -> (Nothing, Just ("| subtype check AS-Tuple: expected subtyping environment Δ' but got nothing"))
  where
    nctx = nstctx ++ ntctx
    ntctx = map getNameTy tctx
    nstctx = map getNameSubTy stctx

subtypeInferUncAux :: TypingEnvironment -> SubtypingEnvironment -> Type -> TermNode -> (Type, Maybe SubtypingEnvironment)
subtypeInferUncAux tctx stctx ty t =
  if isClosedType stctx ty
    then
      let sTy = substCtxToTy stctx ty
       in case infer tctx [SType sTy] t of
            TyError e -> (TyError ("| subtype infer uncurried auxiliary judgement Closed: failed to infer for the term e ≡ " ++ showTerm nctx t ++ " assuming the type A ≡ " ++ showType nctx sTy ++ " as the surrounding context Σ" ++ "\n" ++ e), Nothing)
            _ -> (sTy, Just stctx)
    else case infer tctx [] t of
      TyError e -> (TyError ("| subtype infer uncurried auxiliary judgement Open: failed to infer for the term e ≡ " ++ showTerm nctx t ++ " assuming the empty surrounding context Σ" ++ "\n" ++ e), Nothing)
      ty1 ->
        case subtypeCheck tctx stctx ty1 NegativePolarity ty of
          (_, Just e) -> (TyError ("| subtype infer uncurried auxiliary judgement Open: failed to subtype check for the type B ≡ " ++ showType nctx ty1 ++ " against the type A ≡ " ++ showType nctx ty ++ " assuming negative polarity" ++ "\n" ++ e), Nothing)
          (Just stctx', Nothing) -> (ty1, Just stctx')
          (Nothing, _) -> (TyError ("| subtype infer uncurried auxiliary judgement Open: expected Δ' but got nothing"), Nothing)
  where
    nctx = nstctx ++ ntctx
    ntctx = map getNameTy tctx
    nstctx = map getNameSubTy stctx

ruleASTermUC :: TypingEnvironment -> SubtypingEnvironment -> [((Type, TermNode), Int)] -> ([Type], SubtypingEnvironment)
ruleASTermUC _ stctx [] = ([], stctx)
ruleASTermUC tctx stctx (((ty, t), n) : tys) =
  case subtypeInferUncAux tctx stctx ty t of
    (TyError e, _) -> ([TyError ("| infer AS-Term-UC: failed to subtype infer uncurried auxiliary judgement the type A" ++ show n ++ " ≡ " ++ showType nctx ty ++ " and the term e" ++ show n ++ " ≡ " ++ showTerm ntctx t ++ " assuming the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx ++ "\n" ++ e)], stctx)
    (ty1, Just stctx') ->
      let (tys', stctx'') = ruleASTermUC tctx stctx' tys
       in (ty1 : tys', stctx'')
    (_, Nothing) -> ([TyError ("| infer AS-Term-UC: expected Δ' but got nothing")], stctx)
  where
    nctx = nstctx ++ ntctx
    ntctx = map getNameTy tctx
    nstctx = map getNameSubTy stctx
