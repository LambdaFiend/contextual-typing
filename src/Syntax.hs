module Syntax where

import           Lexer

type Index = Int

type Name = String

type FileInfo = AlexPosn

type NameContext = [Name]

type TypeContext = [(Name, Type)]

type ApplicationStack = [Type]

data TermNode = TermNode
  { getFI :: FileInfo,
    getTm :: Term
  }
  deriving (Eq, Show)

data Term
  = TmInt Int
  | TmVarRaw Name
  | TmVar Index Index Name
  | TmAbs Name TermNode
  | TmApp TermNode TermNode
  | TmError String
  deriving (Eq, Show)

data Type
  = TyInt
  | TyArrow Type Type
  | TyError String
  deriving (Eq, Show)

noPos :: FileInfo
noPos = AlexPn (-1) (-1) (-1)

fromMaybe :: Maybe a -> a
fromMaybe (Just x) = x
fromMaybe Nothing  = error "fromMaybe, in Syntax.hs"
