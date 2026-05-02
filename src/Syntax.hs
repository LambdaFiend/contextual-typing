module Syntax where

import           Lexer

type Index = Int

type Name = String

type FileInfo = AlexPosn

type NameContext = [Name]

type TypeContext = [(Name, Type)]

type SubtypingEnvironment = [SubTyEnvBinding]

data SubTyEnvBinding
  = UniversalTyVar {getNameSubTy :: Name}
  | UnsolvedTyVar {getNameSubTy :: Name}
  | SolvedTyVar {getNameSubTy :: Name, getTypeSubTy :: Type}
  deriving (Eq, Show)

type TypingEnvironment = [TyEnvBinding]

data TyEnvBinding
  = TmVarBind {getNameTy :: Name, getTypeTy :: Type}
  | TyVarBind {getNameTy :: Name}
  deriving (Eq, Show)

type SurroundingContext = [SurroundingInfo]

data SurroundingInfo
  = SType Type
  | STerm TermNode
  deriving (Eq, Show)

data Polarity
  = PositivePolarity
  | NegativePolarity
  deriving (Eq, Show)

data ConstInfo
  = ConstInt Int
  | ConstFloat Float
  | ConstPlusI
  | ConstPlusF
  | ConstPlusInt Int
  | ConstPlusFloat Float
  deriving (Eq, Show)

data TermNode = TermNode
  { getFI :: FileInfo,
    getTm :: Term
  }
  deriving (Eq, Show)

data Term
  = TmConst ConstInfo
  | TmVarRaw Name
  | TmVar Index Index Name
  | TmAbs Name TermNode
  | TmApp TermNode TermNode
  | TmTyAbs Name TermNode
  | TmTyApp TermNode Type
  | TmAnno TermNode Type
  | TmAbsAnno Name Type TermNode
  | TmError String
  deriving (Eq, Show)

data Type
  = TyInt
  | TyFloat
  | TyVarRaw Name
  | TyVar Index Index Name
  | TyArrow Type Type
  | TyForAll Name Type
  | TyError String
  deriving (Eq, Show)

fromMaybe :: Maybe a -> a
fromMaybe (Just x) = x
fromMaybe Nothing  = error "fromMaybe, in Syntax.hs"

noPos :: FileInfo
noPos = AlexPn (-1) (-1) (-1)

isGenericConsumer :: TermNode -> Bool
isGenericConsumer t =
  case getTm t of
    TmConst _   -> True
    TmVar _ _ _ -> True
    TmAnno _ _  -> True
    TmTyAbs _ _ -> True
    _           -> False

negatePolarity :: Polarity -> Polarity
negatePolarity PositivePolarity = NegativePolarity
negatePolarity NegativePolarity = PositivePolarity
