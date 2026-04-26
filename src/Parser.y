{
module Parser where

import Lexer
import Syntax
}

%monad { Either String } { (>>=) } { return }
%name parser
%tokentype { Token }
%error { parseError }

%token

"\\"    { Token pos LAMBDA }
tyint   { Token pos TYINT }
tyfloat { Token pos TYFLOAT }
tytop   { Token pos TYTOP }
"="     { Token pos ASSIGN }
"&"     { Token pos ANDSYM }
"+"     { Token pos PLUS }
"."     { Token pos DOT }
","     { Token pos COMMA }
":"     { Token pos COLON }
"("     { Token pos LPAREN }
")"     { Token pos RPAREN }
"{"     { Token pos LBRACK }
"}"     { Token pos RBRACK }
"->"    { Token pos ARROW }
tmint   { Token pos (TMINT s) }
tmfloat { Token pos (TMFLOAT s) }
id      { Token pos (ID s) }

%%

Term
  : Abs { $1 }
  | App { $1 }

Abs : "\\" Name "." Term { TermNode (tokenPos $1) (TmAbs (snd $2) $4) }

App
  : App Anno { TermNode (getFI $1) (TmApp $1 $2) }
  | Anno     { $1 }

Anno
  : Proj ":" Type { TermNode (getFI $1) (TmAnno $1 $3) }
  | Proj          { $1 }

Proj
  : Proj "." Name { TermNode (getFI $1) (TmProj $1 (snd $3)) }
  | Atom          { $1 }

Atom
  : Value         { $1 }
  | "{" Rec "}"   { TermNode (tokenPos $1) ((\(l, t) -> (TmRec l t)) $2) }
  | "(" Term ")"  { $2 }

Value
  : Name       { TermNode (fst $1) (TmVarRaw (snd $1)) }
  | Const      { $1 }
  | "{" "}"    { TermNode (tokenPos $1) (TmRec [] []) }

Const
  : tmint   { TermNode (tokenPos $1) (TmConst (ConstInt ((\(TMINT s) -> s) (tokenDat $1)))) }
  | tmfloat { TermNode (tokenPos $1) (TmConst (ConstFloat ((\(TMFLOAT s) -> s) (tokenDat $1)))) }
  | "+"     { TermNode (tokenPos $1) (TmConst ConstPlus) }

Rec
  : Name "=" Term "," Rec { (\(x1, x2) -> (snd $1 : x1, $3 : x2)) $5 }
  | Name "=" Term         { ([snd $1], [$3]) }

Name : id { (tokenPos $1, (\(ID s) -> s) (tokenDat $1)) }

Type : TypeArrow { $1 }

TypeArrow
  : TypeInter "->" TypeArrow { TyArrow $1 $3 }
  | TypeInter                { $1 }

TypeInter
  : TypeInter "&" TypeAtom { TyInter $1 $3 }
  | TypeAtom           { $1 }

TypeAtom
  : tyint                 { TyInt }
  | tyfloat               { TyFloat }
  | tytop                 { TyTop }
  | "{" TypeRec "}"       { $2 }
  | "(" Type ")"          { $2 }

TypeRec
  : TypeRec "," Name ":" Type { TyInter $1 (TyRec (snd $3) $5) }
  | Name ":" Type             { TyRec (snd $1) $3 }


{
parseError :: [Token] -> Either String a
parseError [] = Left ("Parsing error near the end of the file")
parseError ((Token fi _):tokens) = Left ("Parsing error at:" ++ showFileInfoHappy fi)
parseError (x:xs) = Left "Parsing error"

showFileInfoHappy :: AlexPosn -> String
showFileInfoHappy (AlexPn p l c) =
  "\n" ++"Absolute Offset: " ++ show p ++ "\n"
  ++ "Line: " ++ show l ++ "\n"
  ++ "Column: " ++ show c
}
