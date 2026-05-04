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
  | SProj Int
  deriving (Eq, Show)

data Polarity
  = PositivePolarity
  | NegativePolarity
  deriving (Eq, Show)

data NumOp
  = PlusOp
  | MinusOp
  | MultOp
  | DivOp
  deriving (Eq, Show)

data BoolOp
  = AndOp
  | OrOp
  | EqOpB
  | NEOpB
  deriving (Eq, Show)

data BoolBoolOp
  = LTOp
  | GTOp
  | LEOp
  | GEOp
  | EqOp
  | NEOp
  deriving (Eq, Show)

data ConstInfo
  = ConstInt Int
  | ConstFloat Float
  | ConstBool Bool
  | ConstUnit
  | ConstOpI NumOp
  | ConstOpF NumOp
  | ConstOpInt NumOp Int
  | ConstOpFloat NumOp Float
  | ConstOpB BoolOp
  | ConstOpBool BoolOp Bool
  | ConstNot
  | ConstOpIB BoolBoolOp
  | ConstOpIntB BoolBoolOp Int
  | ConstOpFB BoolBoolOp
  | ConstOpFloatB BoolBoolOp Float
  | ConstOpU
  | ConstOpUnit
  | ConstOpNU
  | ConstOpNUnit
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
  | TmTuple [TermNode]
  | TmProj TermNode Int
  | TmIf TermNode TermNode TermNode
  | TmAbsUnc [Name] TermNode
  | TmAbsUncAnno [Name] [Type] TermNode
  | TmFix TermNode
  | TmError String
  deriving (Eq, Show)

data Type
  = TyInt
  | TyFloat
  | TyBool
  | TyUnit
  | TyVarRaw Name
  | TyVar Index Index Name
  | TyArrow Type Type
  | TyForAll Name Type
  | TyTuple [Type]
  | TyError String
  deriving (Show)

instance Eq (Type) where
  TyInt == TyInt                             = True
  TyFloat == TyFloat                         = True
  TyBool == TyBool                           = True
  TyUnit == TyUnit                           = True
  (TyVarRaw x1) == (TyVarRaw x2)             = x1 == x2
  (TyVar k1 l1 _) == (TyVar k2 l2 _)         = k1 == k2 && l1 == l2
  (TyArrow ty11 ty12) == (TyArrow ty21 ty22) = ty11 == ty21 && ty12 == ty22
  (TyForAll _ ty11) == (TyForAll _ ty21)     = ty11 == ty21
  (TyTuple tys1) == (TyTuple tys2)           = tys1 == tys2
  (TyError e1) == (TyError e2)               = e1 == e2
  _ == _                                     = False

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
    TmFix _     -> True
    _           -> False

negatePolarity :: Polarity -> Polarity
negatePolarity PositivePolarity = NegativePolarity
negatePolarity NegativePolarity = PositivePolarity

numOpToOp :: NumOp -> (Int -> Int -> Int)
numOpToOp op =
  case op of
    PlusOp  -> (+)
    MinusOp -> (-)
    MultOp  -> (*)
    DivOp   -> (div)

fracOpToOp :: NumOp -> (Float -> Float -> Float)
fracOpToOp op =
  case op of
    PlusOp  -> (+)
    MinusOp -> (-)
    MultOp  -> (*)
    DivOp   -> (/)

boolOpToOp :: BoolOp -> (Bool -> Bool -> Bool)
boolOpToOp op =
  case op of
    AndOp -> (&&)
    OrOp  -> (||)
    EqOpB -> (==)
    NEOpB -> (/=)

numBoolOpToOp :: BoolBoolOp -> (Int -> Int -> Bool)
numBoolOpToOp op =
  case op of
    LTOp -> (<)
    GTOp -> (>)
    LEOp -> (<=)
    GEOp -> (>=)
    EqOp -> (==)
    NEOp -> (/=)

fracBoolOpToOp :: BoolBoolOp -> (Float -> Float -> Bool)
fracBoolOpToOp op =
  case op of
    LTOp -> (<)
    GTOp -> (>)
    LEOp -> (<=)
    GEOp -> (>=)
    EqOp -> (==)
    NEOp -> (/=)
