module Typing where

import           Data.List
import           Display
import           Syntax

infer' :: TermNode -> Type
infer' t = infer [] [] t

infer :: TypeContext -> ApplicationStack -> TermNode -> Type
infer ctx appstack t =
  case (getTm t, appstack) of
    (TmInt _, []) -> TyInt
    (TmVar k _ x, [])
      | k < length ctx ->
          case map snd ctx !? k of
            Just ty -> ty
            Nothing -> TyError ("| infer CAVar: index out of bounds for " ++ x ++ " of the context Γ ≡ " ++ showStringList (map (\(a, b) -> a ++ " : " ++ showType' b) ctx))
    (TmApp t1 t2, _) ->
      case infer ctx [] t2 of
        TyError e -> TyError ("| infer AppS: failed to infer the term e2 ≡ " ++ showTerm (map fst ctx) t2 ++ "\n" ++ e)
        ty ->
          case infer ctx (ty : appstack) t1 of
            TyError e -> TyError ("| infer AppS: failed to infer the term e1 ≡ " ++ showTerm (map fst ctx) t1 ++ " assuming the type A = " ++ showType' ty ++ " at the top of the application stack Ψ ≡ " ++ showStringList (map showType' appstack) ++ "\n" ++ e)
            TyArrow ty1 ty2 | ty == ty1 -> ty2
            TyArrow ty1 _ -> TyError ("| infer AppS: the type of the term e2 ≡ " ++ showTerm (map fst ctx) t2 ++ " is not the same as the type to the left of the arrow type of the term e1 ≡ " ++ showTerm (map fst ctx) t1 ++ ": expected: " ++ showType' ty ++ " but got: " ++ showType' ty1)
            ty' -> TyError ("| infer AppS: expected arrow type but got: " ++ showType' ty')
    (TmAbs x t1, (ty : appstack')) ->
      case infer ((x, ty) : ctx) appstack' t1 of
        TyError e -> TyError ("| infer Lam: failed to infer the type of the term e ≡ " ++ showTerm (map fst ((x, ty) : ctx)) t1 ++ " assuming " ++ x ++ " assigned to the type A ≡ " ++ showType' ty ++ " at the top of the context Γ ≡ " ++ showStringList (map (\(a, b) -> a ++ " : " ++ showType' b) ctx) ++ " and the smaller application stack Ψ ≡ " ++ showStringList (map showType' appstack') ++ "\n" ++ e)
        ty' -> TyArrow ty ty'
    (_, _) -> TyError ("| infer No rules apply: the context Γ ≡ " ++ showStringList (map (\(a, b) -> a ++ " : " ++ showType' b) ctx) ++ ", the application stack Ψ ≡ " ++ showStringList (map showType' appstack) ++ " and the term e ≡ " ++ showTerm (map fst ctx) t)
