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
    ([], TmInt _) -> TyInt
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
      case infer (TyVarBind x2 : tctx) [SType (tySubst 0 0 (TyVar 1 1 x2) ty1)] t1 of
        TyError e -> TyError ("| infer AT-TLam2: failed to infer the term e ≡ " ++ showTerm (x2 : nctx) t1 ++ " assuming the type B ≡ " ++ showType (x2 : nctx) ty1 ++ " as the surrounding context Σ and the type variable α ≡ " ++ x2 ++ " at the top of the typing environment" ++ "\n" ++ e)
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
    (_, _)
      | isGenericConsumer t ->
          case infer tctx [] t of
            TyError e -> TyError ("| infer AT-Sub: failed to infer the term g ≡ " ++ showTerm nctx t ++ "\n" ++ e)
            ty1 ->
              case subtypeInfer tctx [] ty1 sctx of
                (_, TyError e) -> TyError ("| infer AT-Sub: failed to subtype infer the term's g ≡ " ++ showTerm nctx t ++ " inferred type A ≡ " ++ showType nctx ty1 ++ "\n" ++ e)
                (Just [], ty2) -> ty2
                (Just stctx, _) -> TyError ("| infer AT-Sub: subtype infer returned a subtyping environment Δ expected to be empty, but got ≡ " ++ showSubtypingEnvironment nctx stctx)
                (Nothing, _) -> TyError ("| infer AT-Sub: subtype infer returned a subtyping environment Δ expected to be empty, but got nothing")
    (_, _) -> TyError ("| infer No rules apply: the typing environment Γ ≡ " ++ showTypingEnvironment nctx tctx ++ ", the surrounding context Σ ≡ " ++ showSurroundingContext nctx sctx ++ " and the term e ≡ " ++ showTerm nctx t)
  where
    nctx = map getNameTy tctx

collectFreeTyVars :: Type -> [Index]
collectFreeTyVars ty = collectFreeTyVars' [] ty

collectFreeTyVars' :: NameContext -> Type -> [Index]
collectFreeTyVars' ctx ty =
  case ty of
    TyInt           -> []
    TyVarRaw _      -> []
    TyVar k _ _     -> if k < length ctx then [] else [k - length ctx]
    TyForAll x ty1  -> collectFreeTyVars' (x : ctx) ty1
    TyArrow ty1 ty2 -> collectFreeTyVars' ctx ty1 ++ collectFreeTyVars' ctx ty2
    TyError _       -> []

isClosedType :: SubtypingEnvironment -> Type -> Bool
isClosedType ctx ty = all (\j -> case j of Just s -> isSolved s; Nothing -> False) svars
  where
    fvars = collectFreeTyVars ty
    svars = map (\k -> ctx !? k) fvars

isSolved :: SubTyEnvBinding -> Bool
isSolved (SolvedTyVar _ _) = True
isSolved _                 = False

isUnsolved :: SubTyEnvBinding -> Bool
isUnsolved (UnsolvedTyVar _) = True
isUnsolved _                 = False

findSolution :: SubtypingEnvironment -> Name -> Index -> Maybe Type
findSolution ctx x k =
  case ctx !? k of
    Just (SolvedTyVar x' ty') | x == x' -> Just ty'
    _                                   -> Nothing

substCtxToTy :: SubtypingEnvironment -> Type -> Type
substCtxToTy ctx ty =
  case ty of
    TyInt -> ty
    TyVarRaw _ -> ty
    TyVar k _ x ->
      case findSolution ctx x k of
        Just ty' -> (tyShift 0 k ty')
        Nothing  -> ty
    TyForAll x ty1 -> TyForAll x (substCtxToTy (UniversalTyVar x : ctx) ty1)
    TyArrow ty1 ty2 -> TyArrow (substCtxToTy ctx ty1) (substCtxToTy ctx ty2)
    TyError _ -> ty

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
    (TyVar k1 _ x1, _, TyVar k2 _ x2)
      | x1 == x2 && k1 == k2 ->
          if ((k1 < length tctx && elem x1 ntctx) || (k1 < length stctx && elem x1 nstctx))
            then (Just stctx, Nothing)
            else (Nothing, Just ("| subtype check AS-UVar: α ≡ " ++ x1 ++ " is either out-of-scope or somehow does not belong to the typing environment Γ ≡ " ++ showTypingEnvironment ntctx tctx ++ " and to the Δ ≡ " ++ showSubtypingEnvironment ntctx stctx))
    (TyVar k _ x, PositivePolarity, _)
      | k < length stctx && (case stctx !? k of Just s -> isUnsolved s; Nothing -> False) ->
          case drop (k - 1) stctx of
            (UnsolvedTyVar x' : stctx') | x == x' -> (Just (take (k - 1) stctx ++ (SolvedTyVar x' (tyShift 0 (-(length stctx)) ty2) : stctx')), Nothing)
            (UnsolvedTyVar x' : _) -> (Nothing, Just ("| subtype check AS-MVar-L: expected unsolved α ≡ " ++ x ++ " but got unsolved α ≡ " ++ x'))
            (_ : _) -> (Nothing, Just ("| subtype check AS-MVar-L: expected unsolved type variable for α ≡ " ++ x ++ " in the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx ++ " but didn't get it"))
            [] -> (Nothing, Just ("| subtype check AS-MVar-L: index out of bounds for " ++ x ++ " in the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx))
    (_, NegativePolarity, TyVar k _ x)
      | k < length stctx && (case stctx !? k of Just s -> isUnsolved s; Nothing -> False) ->
          case drop (k - 1) stctx of
            (UnsolvedTyVar x' : stctx') | x == x' -> (Just (take (k - 1) stctx ++ (SolvedTyVar x' (tyShift 0 (-(length stctx)) ty1) : stctx')), Nothing)
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
      case subtypeCheck tctx (UniversalTyVar x2 : stctx) (tySubst 0 0 (TyVar 1 1 x2) ty11) pol ty21 of
        (_, Just e) -> (Nothing, Just ("| subtype check AS-Arr: failed to subtype check the type A ≡ " ++ showType (x2 : nctx) ty11 ++ " against the type B ≡ " ++ showType (x2 : nctx) ty21 ++ " assuming the universal type variable α ≡ " ++ x2 ++ " at the top of the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx ++ "\n" ++ e))
        (Just stctx', Nothing) ->
          case stctx' of
            (var : stctx'') | getNameSubTy var == x2 -> (Just stctx'', Nothing)
            (_ : _) -> (Nothing, Just ("| subtype check AS-∀: expected the top of Δ' to be a variable binding of α ≡ " ++ x2 ++ " but got another name"))
            [] -> (Nothing, Just ("| subtype check AS-∀: the subtyping environment Δ' is empty and shouldn't be"))
        (Nothing, _) -> (Nothing, Just ("| subtype check AS-∀: expected subtyping environment Δ' but got nothing"))
    (_, _, _) -> (Nothing, Just ("| subtype check No rules apply: the typing environment Γ ≡ " ++ showTypingEnvironment ntctx tctx ++ ", the subtyping environment Δ ≡ " ++ showSubtypingEnvironment ntctx stctx ++ ", the type A ≡ " ++ showType nctx ty1 ++ ", the polarity is " ++ showPolarity pol ++ " and the type B ≡ " ++ showType nctx ty2))
  where
    nctx = nstctx ++ ntctx
    ntctx = map getNameTy tctx
    nstctx = map getNameSubTy stctx
