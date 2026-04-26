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
    ([], TmInt _) -> TyInt
    ([], TmVar k _ x)
      | k < length tctx ->
          case map snd tctx !? k of
            Just ty -> ty
            Nothing -> TyError ("| infer AVar: index out of bounds for " ++ x ++ " of the context Γ ≡ " ++ showStringList (map (\(a, b) -> a ++ " : " ++ showType' b) tctx))
    (_, TmApp t1 t2) ->
      case infer tctx (STerm t2 : sctx) t1 of
        TyArrow _ ty2 -> ty2
        TyError e -> TyError ("| infer AApp: failed to infer the term e1 ≡ " ++ showTerm (map fst tctx) t1 ++ " assuming the term e2 ≡ " ++ showTerm (map fst tctx) t2 ++ " at the top of the surrounding context Σ ≡ " ++ showStringList (map (showSurroundingInfo (map fst tctx)) sctx) ++ "\n" ++ e)
        ty -> TyError ("| infer AApp: arrow type expected but got: " ++ "\n" ++ showType' ty)
    ((SType (TyArrow ty1 ty2) : []), TmAbs x t1) ->
      case infer ((x, ty1) : tctx) [SType ty2] t1 of
        TyError e -> TyError ("| infer ALam1: failed to infer e ≡ " ++ showTerm (map fst ((x, ty1) : tctx)) t1 ++ " assuming " ++ x ++ " assigned to the type A ≡ " ++ showType' ty1 ++ " at the top of the environment Γ ≡ " ++ showStringList (map (\(a, b) -> a ++ " : " ++ showType' b) tctx) ++ " and the type B ≡ " ++ showType' ty2 ++ " as the surrounding context Σ" ++ "\n" ++ e)
        ty3 -> TyArrow ty1 ty3
    ((STerm t2 : sctx'), TmAbs x t1) ->
      case infer tctx [] t2 of
        TyError e -> TyError ("| infer ALam2: failed to infer the contextual argument e2 ≡ " ++ showTerm (map fst tctx) t2 ++ "\n" ++ e)
        ty1 ->
          case infer ((x, ty1) : tctx) (map (\s -> case s of STerm s' -> STerm (shift' 0 1 s'); _ -> s) sctx') t1 of
            TyError e -> TyError ("| infer ALam2: failed to infer the term e ≡ " ++ showTerm (map fst ((x, ty1) : tctx)) t1 ++ " assuming " ++ x ++ " assigned to the type A ≡ " ++ showType' ty1 ++ " at the top of the environment Γ ≡ " ++ showStringList (map (\(a, b) -> a ++ " : " ++ showType' b) tctx) ++ " and the smaller surrounding context Σ ≡ " ++ showStringList (map (showSurroundingInfo (map fst tctx)) sctx') ++ "\n" ++ e)
            ty -> TyArrow ty1 ty
    ([], TmAnno t1 ty1) ->
      case infer tctx (SType ty1 : []) t1 of
        TyError e -> TyError ("| infer AAnn: failed to infer the term e ≡ " ++ showTerm (map fst tctx) t1 ++ " using the annotation of type A ≡ " ++ showType' ty1 ++ " as the surrounding context Σ" ++ "\n" ++ e)
        _ -> ty1
    (_, _)
      | isGenericConsumer t && sctx /= [] ->
          case infer tctx [] t of
            TyError e -> TyError ("| infer ASub: failed to infer the term g ≡ " ++ showTerm (map fst tctx) t ++ "\n" ++ e)
            ty1 ->
              case match tctx ty1 sctx of
                Just e -> TyError ("| infer ASub: failed to match the type g ≡ " ++ showTerm (map fst tctx) t ++ " inferred type A ≡ " ++ showType' ty1 ++ "\n" ++ e)
                Nothing -> ty1
    (_, _) -> TyError ("| infer No rules apply: the environment Γ ≡ " ++ showStringList (map (\(a, b) -> a ++ " : " ++ showType' b) tctx) ++ ", the surrounding context Σ ≡ " ++ showStringList (map (showSurroundingInfo (map fst tctx)) sctx) ++ " and the term e ≡ " ++ showTerm (map fst tctx) t)

match :: TypeContext -> Type -> SurroundingContext -> Maybe String
match tctx ty sctx =
  case (ty, sctx) of
    (_, []) -> Nothing
    (_, [SType ty']) | ty == ty' -> Nothing
    (TyArrow ty1 ty2, (STerm t : sctx')) ->
      case infer tctx [SType ty1] t of
        TyError e -> Just ("| match SubTerm: failed to infer the term e ≡ " ++ showTerm (map fst tctx) t ++ " assuming the type A ≡ " ++ "[" ++ showType' ty1 ++ "]")
        _ ->
          case match tctx ty2 sctx' of
            Just e -> Just ("| match SubTerm: failed to match the type B ≡ " ++ showType' ty2 ++ " with the surrounding context Σ ≡ " ++ showStringList (map (showSurroundingInfo (map fst tctx)) sctx') ++ "\n" ++ e)
            Nothing -> Nothing
    (_, _) -> Just ("| match No rules apply: the environment Γ ≡ " ++ showStringList (map (\(a, b) -> a ++ " : " ++ showType' b) tctx) ++ ", the type A ≡ " ++ showType' ty ++ " and the surrounding context Σ ≡ " ++ showStringList (map (showSurroundingInfo (map fst tctx)) sctx))
