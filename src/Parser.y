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
"."     { Token pos DOT }
":"     { Token pos COLON }
"("     { Token pos LPAREN }
")"     { Token pos RPAREN }
"->"    { Token pos ARROW }
tmint   { Token pos (TMINT s) }
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
  : Atom ":" Type { TermNode (getFI $1) (TmAnno $1 $3) }
  | Atom          { $1 }

Atom
  : Value         { $1 }
  | "(" Term ")"  { $2 }

Value
  : Name       { TermNode (fst $1) (TmVarRaw (snd $1)) }
  | tmint      { TermNode (tokenPos $1) (TmInt ((\(TMINT s) -> s) (tokenDat $1))) }

Name : id { (tokenPos $1, (\(ID s) -> s) (tokenDat $1)) }

Type : TypeArrow { $1 }

TypeArrow
  : TypeAtom "->" TypeArrow { TyArrow $1 $3 }
  | TypeAtom                { $1 }

TypeAtom
  : tyint                 { TyInt }
  | "(" Type ")"          { $2 }

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
