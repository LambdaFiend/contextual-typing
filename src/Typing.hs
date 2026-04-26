module Typing where

import           Data.List
import           Display
import           Helper
import           Syntax

infer' :: TermNode -> Type
infer' t = infer [] [] t

infer :: TypeContext -> SurroundingContext -> TermNode -> Type
infer tctx sctx t =
  case (sctx, getTm t) of
    ([], TmConst c) -> constToType c
    ([], TmVar k _ x)
      | k < length tctx ->
          case map snd tctx !? k of
            Just ty -> ty
            Nothing -> TyError ("| infer CAVar: index out of bounds for " ++ x ++ " of the context Γ ≡ " ++ showStringList (map (\(a, b) -> a ++ " : " ++ showType' b) tctx))
    (_, TmProj t1 x) ->
      case infer tctx (SLabel x : sctx) t1 of
        TyRec y ty1 | x == y -> ty1
        TyError e -> TyError ("| infer CAPrj: failed to infer the term e ≡ " ++ showTerm (map fst tctx) t1 ++ " assuming the label a ≡ " ++ x ++ " at the top of the surrounding context Σ ≡ " ++ showStringList (map (showSurroundingInfo (map fst tctx)) sctx) ++ "\n" ++ e)
        ty -> TyError ("| infer CAPrj: expected record type but got " ++ showType' ty)
    (_, TmApp t1 t2) ->
      case infer tctx (STerm t2 : sctx) t1 of
        TyArrow _ ty2 -> ty2
        TyError e -> TyError ("| infer CAApp: failed to infer the term e1 ≡ " ++ showTerm (map fst tctx) t1 ++ " assuming the term e2 ≡ " ++ showTerm (map fst tctx) t2 ++ " at the top of the surrounding context Σ ≡ " ++ showStringList (map (showSurroundingInfo (map fst tctx)) sctx) ++ "\n" ++ e)
        ty -> TyError ("| infer CAApp: arrow type expected but got: " ++ "\n" ++ showType' ty)
    ((SType (TyArrow ty1 ty2) : []), TmAbs x t1) ->
      case infer ((x, ty1) : tctx) [SType ty2] t1 of
        TyError e -> TyError ("| infer CALam1: failed to infer e ≡ " ++ showTerm (map fst ((x, ty1) : tctx)) t1 ++ " assuming " ++ x ++ " assigned to the type A ≡ " ++ showType' ty1 ++ " at the top of the environment Γ ≡ " ++ showStringList (map (\(a, b) -> a ++ " : " ++ showType' b) tctx) ++ " and the type B ≡ " ++ showType' ty2 ++ " as the surrounding context Σ" ++ "\n" ++ e)
        ty3 -> TyArrow ty1 ty3
    ([], TmRec xs ts) ->
      case map (\(x, tm) -> TyRec x tm) (zip xs (map (infer tctx []) ts)) of
        [] -> TyTop
        tys
          | concat (map findTypeErrors tys) /= [] ->
              TyError ("| infer CARcd: failed to infer the record's terms {ai = ei} ≡ " ++ showTerm (map fst tctx) t ++ "\n" ++ "{" ++ "\n" ++ unlines (map showType' tys) ++ "\n" ++ "}")
        (ty1 : tys) -> foldl TyInter ty1 tys
    ((STerm t2 : sctx'), TmAbs x t1) ->
      case infer tctx [] t2 of
        TyError e -> TyError ("| infer CALam2: failed to infer the contextual argument e2 ≡ " ++ showTerm (map fst tctx) t2 ++ "\n" ++ e)
        ty1 ->
          case infer ((x, ty1) : tctx) (map (\s -> case s of STerm s' -> STerm (shift' 0 1 s'); _ -> s) sctx') t1 of
            TyError e -> TyError ("| infer CALam2: failed to infer the term e ≡ " ++ showTerm (map fst ((x, ty1) : tctx)) t1 ++ " assuming " ++ x ++ " assigned to the type A ≡ " ++ showType' ty1 ++ " at the top of the environment Γ ≡ " ++ showStringList (map (\(a, b) -> a ++ " : " ++ showType' b) tctx) ++ " and the smaller surrounding context Σ ≡ " ++ showStringList (map (showSurroundingInfo (map fst tctx)) sctx') ++ "\n" ++ e)
            ty -> TyArrow ty1 ty
    ([], TmAnno t1 ty1) ->
      case infer tctx (SType ty1 : []) t1 of
        TyError e -> TyError ("| infer CAAnn: failed to infer the term e ≡ " ++ showTerm (map fst tctx) t1 ++ " using the annotation of type A ≡ " ++ showType' ty1 ++ " as the surrounding context Σ" ++ "\n" ++ e)
        _ -> ty1
    (_, _)
      | isGenericConsumer t && sctx /= [] ->
          case infer tctx [] t of
            TyError e -> TyError ("| infer CASub: failed to infer the term g ≡ " ++ showTerm (map fst tctx) t ++ "\n" ++ e)
            ty1 ->
              case supertype tctx ty1 sctx of
                TyError e -> TyError ("| infer CASub: failed to supertype the term g ≡ " ++ showTerm (map fst tctx) t ++ " inferred type A ≡ " ++ showType' ty1 ++ "\n" ++ e)
                ty2 -> ty2
    (_, _) -> TyError ("| infer No rules apply: the environment Γ ≡ " ++ showStringList (map (\(a, b) -> a ++ " : " ++ showType' b) tctx) ++ ", the surrounding context Σ ≡ " ++ showStringList (map (showSurroundingInfo (map fst tctx)) sctx) ++ " and the term e ≡ " ++ showTerm (map fst tctx) t)

supertype :: TypeContext -> Type -> SurroundingContext -> Type
supertype tctx ty sctx =
  case (ty, sctx) of
    (TyInt, (SType TyInt : [])) -> TyInt
    (TyFloat, (SType TyFloat : [])) -> TyInt
    (TyTop, (SType TyTop : [])) -> TyInt
    (_, []) -> ty
    (TyArrow ty11 ty12, (SType (TyArrow ty21 ty22) : [])) ->
      case supertype tctx ty21 (SType ty11 : []) of
        TyError e -> TyError ("| supertype CASArr: failed to supertype the left side C ≡ " ++ showType' ty21 ++ " <: A ≡ " ++ "[" ++ showType' ty11 ++ "]" ++ " of the arrow" ++ "\n" ++ e)
        _ ->
          case supertype tctx ty12 (SType ty22 : []) of
            TyError e -> TyError ("| supertype CASArr: failed to supertype the right side B ≡ " ++ showType' ty12 ++ " <: D ≡ " ++ "[" ++ showType' ty22 ++ "]" ++ " of the arrow" ++ "\n" ++ e)
            _ -> TyArrow ty21 ty22
    (TyArrow ty1 ty2, (STerm t1 : sctx')) ->
      case infer tctx (SType ty1 : []) t1 of
        TyError e -> TyError ("| supertype CASTerm: failed to infer the contextual term's e ≡ " ++ showTerm (map fst tctx) t1 ++ " assuming the type A ≡ " ++ "[" ++ showType' ty1 ++ "]" ++ " as the surrounding context Σ" ++ "\n" ++ e)
        _ ->
          case supertype tctx ty2 sctx' of
            TyError e -> TyError ("| supertype CASTerm: failed to supertype the right side B ≡ " ++ showType' ty2 ++ " <: Σ ≡ " ++ showStringList (map (showSurroundingInfo (map fst tctx)) sctx') ++ " of the arrow" ++ "\n" ++ e)
            ty3 -> TyArrow ty1 ty3
    (TyRec x1 ty1, (SType (TyRec x2 ty2) : []))
      | x1 == x2 ->
          case supertype tctx ty1 (SType ty2 : []) of
            TyError e -> TyError ("| supertype CASRcd: failed to supertype the type within the record A ≡ " ++ showType' ty1 ++ " <: B ≡ " ++ "[" ++ showType' ty2 ++ "]" ++ "\n" ++ e)
            _ -> TyRec x2 ty2
    (TyRec x1 ty1, (SLabel x2 : sctx')) ->
      if x1 == x2
        then case supertype tctx ty1 sctx' of
          TyError e -> TyError ("| supertype CASLabel: failed to supertype the type within the record A ≡ " ++ showType' ty1 ++ " <: Σ ≡ " ++ showStringList (map (showSurroundingInfo (map fst tctx)) sctx') ++ "\n" ++ e)
          ty2 -> TyRec x2 ty2
        else TyError ("| supertype CASLabel: non-matching labels " ++ x1 ++ " and " ++ x2)
    (TyInter ty1 ty2, _)
      | sctx /= [] ->
          case supertype tctx ty1 sctx of
            TyError e1 ->
              case supertype tctx ty2 sctx of
                TyError e2 ->
                  case sctx of
                    (SType (TyInter ty3 ty4) : []) ->
                      case _CASAnd ty3 ty4 of
                        TyError e3 -> TyError ("| supertype CASAndL, CASAndR and CASAnd: failed to supertype both sides of the intersection, as well as the intersection" ++ "\n" ++ "{-------------------backtrack_start------------------" ++ "\n" ++ e1 ++ "\n" ++ "-----------------------------------------------------" ++ "\n" ++ e2 ++ "\n" ++ "-----------------------------------------------------" ++ "\n" ++ e3 ++ "\n" ++ "--------------------backtrack_end-------------------}")
                        ty5 -> ty5
                    _ -> TyError ("| supertype No rules apply: the environment Γ ≡ " ++ showStringList (map (\(a, b) -> a ++ " : " ++ showType' b) tctx) ++ ", the term e ≡ " ++ showType' ty ++ " and the surrounding context Σ ≡ " ++ showStringList (map (showSurroundingInfo (map fst tctx)) sctx))
                ty3 -> ty3
            ty3 -> ty3
    (_, (SType (TyInter ty1 ty2) : [])) -> _CASAnd ty1 ty2
    (_, _) -> TyError ("| supertype No rules apply: the environment Γ ≡ " ++ showStringList (map (\(a, b) -> a ++ " : " ++ showType' b) tctx) ++ ", the term e ≡ " ++ showType' ty ++ " and the surrounding context Σ ≡ " ++ showStringList (map (showSurroundingInfo (map fst tctx)) sctx))
  where
    _CASAnd ty1 ty2 =
      case supertype tctx ty (SType ty1 : []) of
        TyError e -> TyError ("| supertype CASAnd: failed to supertype the left side of the intersection A ≡ " ++ showType' ty ++ " <: B ≡ " ++ "[" ++ showType' ty1 ++ "]" ++ "\n" ++ e)
        _ ->
          case supertype tctx ty (SType ty2 : []) of
            TyError e -> TyError ("| supertype CASAnd: failed to supertype the right side of the intersection A ≡ " ++ showType' ty ++ " <: C ≡ " ++ "[" ++ showType' ty2 ++ "]" ++ "\n" ++ e)
            _ -> TyInter ty1 ty2
