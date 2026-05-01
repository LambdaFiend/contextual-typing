module Helper where

import           Data.List
import           Syntax

newtype UpdatedTmArrTm = UpdatedTmArrTm
  {updateTmArrTm :: (TermNode, TermNode -> UpdatedTmArrTm, TermNode -> UpdatedTmArrTm, Type -> Type)}

traverseDownTm :: (TermNode -> UpdatedTmArrTm) -> TermNode -> TermNode
traverseDownTm f t = TermNode fi $
  case tm of
    TmInt _           -> tm
    TmVar _ _ _       -> tm
    TmVarRaw _        -> tm
    TmAbs x t1        -> TmAbs x (traverseTm' t1)
    TmApp t1 t2       -> TmApp (traverseTm' t1) (traverseTm' t2)
    TmTyAbs x t1      -> TmTyAbs x $ traverseTm' t1
    TmTyApp t1 ty     -> TmTyApp (traverseTm' t1) (fTy ty)
    TmAnno t1 ty      -> TmAnno (traverseTm' t1) (fTy ty)
    TmAbsAnno x ty t1 -> TmAbsAnno x (fTy ty) (traverseTm' t1)
    TmError _         -> tm
  where
    tm = getTm t'
    fi = getFI t'
    traverseTm' = traverseDownTm f'
    (t', f', _, fTy) = updateTmArrTm $ f t

isVal :: TermNode -> Bool
isVal t =
  case getTm t of
    TmInt _                -> True
    TmAbs _ _              -> True
    TmTyAbs _ _            -> True
    TmAnno t1 _ | isVal t1 -> True
    TmAbsAnno _ _ _        -> True
    _                      -> False

typingEvalSubst :: Type -> Type -> Type
typingEvalSubst s t = tyShift' (-1) (tySubst' 0 (tyShift' 1 s) t)

evalSubst :: TermNode -> TermNode -> TermNode
evalSubst s t = shift' 0 (-1) (subst' 0 (shift' 0 1 s) t)

evalTyTermSubst :: Type -> TermNode -> TermNode
evalTyTermSubst s t = shift' 0 (-1) (tyTermSubst' 0 (tyShift' 1 s) t)

tyTermSubst' :: Index -> Type -> TermNode -> TermNode
tyTermSubst' j s t = traverseDownTm (tyTermSubst 0 j s) t

tyTermSubst :: Index -> Index -> Type -> TermNode -> UpdatedTmArrTm
tyTermSubst c j s t =
  UpdatedTmArrTm $
    case getTm t of
      TmAbs _ _ -> (t, tyTermSubst (c + 1) j s, tyTermSubst c j s, tySubst' (c + j) s)
      TmTyAbs _ _ -> (t, tyTermSubst (c + 1) j s, tyTermSubst c j s, tySubst' (c + j) s)
      TmAbsAnno _ _ _ -> (t, tyTermSubst (c + 1) j s, tyTermSubst c j s, tySubst' (c + j) s)
      _ -> (t, tyTermSubst c j s, tyTermSubst c j s, tySubst' (c + j) s)

tyShift' :: Index -> Type -> Type
tyShift' d ty = tyShift 0 d ty

tyShift :: Index -> Index -> Type -> Type
tyShift c d ty =
  case ty of
    TyInt           -> TyInt
    TyVar k l x     -> TyVar (if k < c then k else k + d) (l + d) x
    TyForAll x ty1  -> TyForAll x (tyShift (c + 1) d ty1)
    TyArrow ty1 ty2 -> TyArrow (tyShift c d ty1) (tyShift c d ty2)
    _               -> ty

tySubst' :: Index -> Type -> Type -> Type
tySubst' j s t = tySubst 0 j s t

tySubst :: Index -> Index -> Type -> Type -> Type
tySubst c j s ty =
  case ty of
    TyInt           -> TyInt
    TyVar k _ _     -> if k == j + c then tyShift' (j + c) s else ty
    TyForAll x ty1  -> TyForAll x $ tySubst (c + 1) j s ty1
    TyArrow ty1 ty2 -> TyArrow (tySubst c j s ty1) (tySubst c j s ty2)
    _               -> ty

shift' :: Index -> Index -> TermNode -> TermNode
shift' c d t = traverseDownTm (shift c d) t

shift :: Index -> Index -> TermNode -> UpdatedTmArrTm
shift c d t =
  UpdatedTmArrTm $
    case getTm t of
      TmVar k l x -> (TermNode (getFI t) (TmVar (if k < c then k else k + d) (l + d) x), id', id', tyShift c d)
      TmAbs _ _ -> (t, shift (c + 1) d, shift c d, tyShift c d)
      TmTyAbs _ _ -> (t, shift (c + 1) d, shift c d, tyShift c d)
      TmAbsAnno _ _ _ -> (t, shift (c + 1) d, shift c d, tyShift c d)
      _ -> (t, shift c d, shift c d, tyShift c d)

subst' :: Index -> TermNode -> TermNode -> TermNode
subst' j s t = traverseDownTm (subst 0 j s) t

subst :: Index -> Index -> TermNode -> TermNode -> UpdatedTmArrTm
subst c j s t =
  UpdatedTmArrTm $
    case getTm t of
      TmVar k _ _ -> (if k == j + c then shift' 0 (j + c) s else t, id', id', id :: Type -> Type)
      TmAbs _ _ -> (t, subst (c + 1) j s, subst c j s, id :: Type -> Type)
      TmTyAbs _ _ -> (t, subst (c + 1) j s, subst c j s, id :: Type -> Type)
      TmAbsAnno _ _ _ -> (t, subst (c + 1) j s, subst c j s, id :: Type -> Type)
      _ -> (t, subst c j s, subst c j s, id :: Type -> Type)

genIndex' :: TermNode -> TermNode
genIndex' t = traverseDownTm (genIndex []) t

genIndex :: NameContext -> TermNode -> UpdatedTmArrTm
genIndex ctx t =
  UpdatedTmArrTm $
    case getTm t of
      TmVarRaw x | elem x ctx -> (TermNode (getFI t) $ TmVar (length $ takeWhile (/= x) ctx) (length ctx) x, genIndex ctx, genIndex ctx, id :: Type -> Type)
      TmVarRaw x -> (TermNode (getFI t) $ TmError ("Free variables are not allowed: " ++ x), genIndex ctx, genIndex ctx, id :: Type -> Type)
      TmAbs x _ -> (t, genIndex (x : ctx), genIndex ctx, id)
      TmTyAbs x _ -> (t, genIndex (x : ctx), genIndex ctx, genIndexType ctx)
      TmAbsAnno x _ _ -> (t, genIndex (x : ctx), genIndex ctx, genIndexType ctx)
      _ -> (t, genIndex ctx, genIndex ctx, genIndexType ctx)

genIndexType :: NameContext -> Type -> Type
genIndexType ctx ty =
  case ty of
    TyVarRaw x | elem x ctx -> TyVar (length $ takeWhile (/= x) ctx) (length ctx) x
    TyVarRaw x -> TyError ("Free variables are not allowed: " ++ x)
    TyForAll x ty1 -> TyForAll x (genIndexType (x : ctx) ty1)
    TyArrow ty1 ty2 -> TyArrow (genIndexType ctx ty1) (genIndexType ctx ty2)
    _ -> ty

shiftSurroundingContext :: SurroundingContext -> Index -> SurroundingContext
shiftSurroundingContext ctx n = map (\s -> case s of STerm e -> STerm (shift' 0 n e); SType ty -> SType (tyShift 0 n ty)) ctx

shiftTypingEnvironment :: TypingEnvironment -> Index -> TypingEnvironment
shiftTypingEnvironment ctx n = map (\s -> case s of TmVarBind x ty -> TmVarBind x (tyShift 0 n ty); _ -> s) ctx

shiftSubtypingEnvironment :: SubtypingEnvironment -> Index -> SubtypingEnvironment
shiftSubtypingEnvironment ctx n = map (\s -> case s of SolvedTyVar x ty -> SolvedTyVar x (tyShift 0 n ty); _ -> s) ctx

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

id' :: TermNode -> UpdatedTmArrTm
id' t = UpdatedTmArrTm (t, id', id', id :: Type -> Type)

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
    TyInt           -> []
    TyVar _ _ _     -> []
    TyVarRaw x      -> ["Found TyVarRaw: " ++ x]
    TyForAll _ ty   -> findTypeErrors ty
    TyArrow ty1 ty2 -> findTypeErrors ty1 ++ findTypeErrors ty2
    TyError e       -> [e]

findTermErrors' :: TermNode -> String
findTermErrors' t = intercalate "\n" $ findTermErrors t

findTermErrors :: TermNode -> [String]
findTermErrors t =
  case getTm t of
    TmInt _            -> []
    TmVar _ _ _        -> []
    TmVarRaw x         -> ["Found TmVarRaw: " ++ x]
    TmAbs _ t1         -> findTermErrors t1
    TmApp t1 t2        -> findTermErrors t1 ++ findTermErrors t2
    TmTyAbs _ t1       -> findTermErrors t1
    TmTyApp t1 ty      -> findTermErrors t1 ++ findTypeErrors ty
    TmAnno t1 ty       -> findTermErrors t1 ++ findTypeErrors ty
    TmAbsAnno _ ty1 t1 -> findTypeErrors ty1 ++ findTermErrors t1
    TmError e          -> [e]
