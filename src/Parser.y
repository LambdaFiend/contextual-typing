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

"λ"     { Token pos LAMBDA }
"∀"     { Token pos FORALL }
"→"     { Token pos ARROW }
"@"     { Token pos APPLY }
"."     { Token pos DOT }
":"     { Token pos COLON }
"("     { Token pos LPAREN }
")"     { Token pos RPAREN }
tyint   { Token pos TYINT }
tmint   { Token pos (TMINT n) }
idLower { Token pos (IDLower s) }
idUpper { Token pos (IDUpper s) }

%%

Term
  : App { $1 }
  | Abs { $1 }

Abs
  : "λ" NameLower "." Term { TermNode (tokenPos $1) (TmAbs (snd $2) $4) }
  | "λ" NameUpper "." Term { TermNode (tokenPos $1) (TmTyAbs (snd $2) $4) }

App
  : App Anno     { TermNode (getFI $1) (TmApp $1 $2) }
  | App "@" Type { TermNode (getFI $1) (TmTyApp $1 $3) }
  | Anno         { $1 }

Anno
  : Atom ":" Type { TermNode (getFI $1) (TmAnno $1 $3) }
  | Atom          { $1 }

Atom
  : Value        { $1 }
  | "(" Term ")" { $2 }

Value
  : NameLower { TermNode (fst $1) $ TmVarRaw (snd $1) }
  | tmint     { TermNode (tokenPos $1) (TmInt ((\(TMINT s) -> s) (tokenDat $1))) }

NameLower : idLower { (tokenPos $1, (\(IDLower s) -> s) $ tokenDat $1) }

NameUpper : idUpper { (tokenPos $1, (\(IDUpper s) -> s) $ tokenDat $1) }

Type
  : TypeForAll { $1 }
  | TypeArrow  { $1 }

TypeForAll : "∀" NameUpper "." Type { TyForAll (snd $2) $4 }

TypeArrow
  : TypeAtom "→" TypeArrow { TyArrow $1 $3 }
  | TypeAtom               { $1 }

TypeAtom
  : NameUpper    { TyVarRaw (snd $1) }
  | tyint        { TyInt }
  | "(" Type ")" { $2 }

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
