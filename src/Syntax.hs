module Syntax where

import           Lexer

type Index = Int

type Name = String

type FileInfo = AlexPosn

type NameContext = [Name]

type TypeContext = [(Name, Type)]

type SurroundingContext = [SurroundingInfo]

data SurroundingInfo
  = SType Type
  | STerm TermNode
  | SLabel Name
  deriving (Eq, Show)

data TermNode = TermNode
  { getFI :: FileInfo,
    getTm :: Term
  }
  deriving (Eq, Show)

data ConstInfo
  = ConstInt Int
  | ConstFloat Float
  | ConstPlus
  | ConstPlusInt Int
  | ConstPlusFloat Float
  deriving (Eq, Show)

data Term
  = TmConst ConstInfo
  | TmVarRaw Name
  | TmVar Index Index Name
  | TmAbs Name TermNode
  | TmApp TermNode TermNode
  | TmAnno TermNode Type
  | TmRec [Name] [TermNode]
  | TmProj TermNode Name
  | TmError String
  deriving (Eq, Show)

data Type
  = TyInt
  | TyFloat
  | TyTop
  | TyArrow Type Type
  | TyInter Type Type
  | TyRec Name Type
  | TyError String
  deriving (Eq, Show)

noPos :: FileInfo
noPos = AlexPn (-1) (-1) (-1)

fromMaybe :: Maybe a -> a
fromMaybe (Just x) = x
fromMaybe Nothing  = error "fromMaybe, in Syntax.hs"

isGenericConsumer :: TermNode -> Bool
isGenericConsumer t =
  case getTm t of
    TmConst _   -> True
    TmVar _ _ _ -> True
    TmAnno _ _  -> True
    TmRec _ _   -> True
    _           -> False

constToType :: ConstInfo -> Type
constToType (ConstInt _) = TyInt
constToType (ConstFloat _) = TyFloat
constToType ConstPlus = TyInter (TyArrow TyInt (TyArrow TyInt TyInt)) (TyArrow TyFloat (TyArrow TyFloat TyFloat))
constToType (ConstPlusInt _) = TyArrow TyInt TyInt
constToType (ConstPlusFloat _) = TyArrow TyFloat TyFloat
