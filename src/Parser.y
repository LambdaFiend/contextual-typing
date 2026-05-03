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

"fst"   { Token pos FST }
"snd"   { Token pos SND }
"λ"     { Token pos LAMBDA }
"∀"     { Token pos FORALL }
"→"     { Token pos ARROW }
"@"     { Token pos APPLY }
","     { Token pos COMMA }
"."     { Token pos DOT }
":"     { Token pos COLON }
"("     { Token pos LPAREN }
")"     { Token pos RPAREN }
"="     { Token pos ASSIGN }
"&&"    { Token pos AND }
"||"    { Token pos OR }
"not"   { Token pos NOT }
"+F"    { Token pos PLUSFLOAT }
"+I"    { Token pos PLUSINT }
"-F"    { Token pos MINUSFLOAT }
"-I"    { Token pos MINUSINT }
"*F"    { Token pos MULTFLOAT }
"*I"    { Token pos MULTINT }
"/F"    { Token pos DIVFLOAT }
"/I"    { Token pos DIVINT }
let     { Token pos LET }
in      { Token pos IN }
tyfloat { Token pos TYFLOAT }
tyint   { Token pos TYINT }
tybool  { Token pos TYBOOL }
true    { Token pos TRUE }
false   { Token pos FALSE }
if      { Token pos IF }
then    { Token pos THEN }
else    { Token pos ELSE }
tmfloat { Token pos (TMFLOAT u) }
tmint   { Token pos (TMINT n) }
idLower { Token pos (IDLower s) }
idUpper { Token pos (IDUpper s) }

%%

Term
  : App { $1 }
  | Abs { $1 }
  | Let { $1 }
  | If  { $1 }

If : if Term then Term else Term { TermNode (tokenPos $1) (TmIf $2 $4 $6) }

Let
  : let NameLower "=" Term in Term          { TermNode (tokenPos $1) (TmApp (TermNode (tokenPos $3) (TmAbs (snd $2) $6)) $4) }
  | let NameLower ":" Type "=" Term in Term { TermNode (tokenPos $1) (TmApp (TermNode (tokenPos $5) (TmAbsAnno (snd $2) $4 $8)) (TermNode (tokenPos $3) (TmAnno $6 $4))) }

Abs
  : "λ" ManyLowerAbs { $2 }
  | "λ" ManyUpperAbs { $2 }

ManyLowerAbs
  : NameLower ManyLowerAbs          { TermNode (fst $1) (TmAbs (snd $1) $2) }
  | NameLower "." Term              { TermNode (fst $1) (TmAbs (snd $1) $3) }
  | NameLower ":" Type ManyLowerAbs { TermNode (fst $1) (TmAbsAnno (snd $1) $3 $4) }
  | NameLower ":" Type "." Term     { TermNode (fst $1) (TmAbsAnno (snd $1) $3 $5) }

ManyUpperAbs
  : NameUpper ManyUpperAbs { TermNode (fst $1) (TmTyAbs (snd $1) $2) }
  | NameUpper "." Term     { TermNode (fst $1) (TmTyAbs (snd $1) $3) }

App
  : App Anno     { TermNode (getFI $1) (TmApp $1 $2) }
  | App "@" Type { TermNode (getFI $1) (TmTyApp $1 $3) }
  | "fst" Anno   { TermNode (tokenPos $1) (TmFst $2) }
  | "snd" Anno   { TermNode (tokenPos $1) (TmSnd $2) }
  | Anno         { $1 }

Anno
  : Atom ":" Type { TermNode (getFI $1) (TmAnno $1 $3) }
  | Atom          { $1 }

Atom
  : Value                 { $1 }
  | "(" Term "," Term ")" { TermNode (tokenPos $1) (TmPair $2 $4) }
  | "(" Term ")"          { $2 }

Value
  : NameLower { TermNode (fst $1) $ TmVarRaw (snd $1) }
  | tmfloat   { TermNode (tokenPos $1) (TmConst (ConstFloat ((\(TMFLOAT s) -> s) (tokenDat $1)))) }
  | tmint     { TermNode (tokenPos $1) (TmConst (ConstInt ((\(TMINT s) -> s) (tokenDat $1)))) }
  | "+F"      { TermNode (tokenPos $1) (TmConst (ConstOpF PlusOp)) }
  | "+I"      { TermNode (tokenPos $1) (TmConst (ConstOpI PlusOp)) }
  | "-F"      { TermNode (tokenPos $1) (TmConst (ConstOpF MinusOp)) }
  | "-I"      { TermNode (tokenPos $1) (TmConst (ConstOpI MinusOp)) }
  | "*F"      { TermNode (tokenPos $1) (TmConst (ConstOpF MultOp)) }
  | "*I"      { TermNode (tokenPos $1) (TmConst (ConstOpI MultOp)) }
  | "/F"      { TermNode (tokenPos $1) (TmConst (ConstOpF DivOp)) }
  | "/I"      { TermNode (tokenPos $1) (TmConst (ConstOpI DivOp)) }
  | "&&"      { TermNode (tokenPos $1) (TmConst (ConstOpB AndOp)) }
  | "||"      { TermNode (tokenPos $1) (TmConst (ConstOpB OrOp)) }
  | true      { TermNode (tokenPos $1) (TmConst (ConstBool True)) }
  | false     { TermNode (tokenPos $1) (TmConst (ConstBool False)) }
  | "not"     { TermNode (tokenPos $1) (TmConst ConstNot) }

NameLower : idLower { (tokenPos $1, (\(IDLower s) -> s) $ tokenDat $1) }

NameUpper : idUpper { (tokenPos $1, (\(IDUpper s) -> s) $ tokenDat $1) }

Type
  : TypeForAll { $1 }
  | TypeArrow  { $1 }

TypeForAll : "∀" ManyTypeForAll { $2 }

ManyTypeForAll
  : NameUpper ManyTypeForAll { TyForAll (snd $1) $2 }
  | NameUpper "." Type       { TyForAll (snd $1) $3 }

TypeArrow
  : TypeAtom "→" TypeArrow { TyArrow $1 $3 }
  | TypeAtom               { $1 }

TypeAtom
  : NameUpper             { TyVarRaw (snd $1) }
  | tyfloat               { TyFloat }
  | tyint                 { TyInt }
  | tybool                { TyBool }
  | "(" Type ")"          { $2 }
  | "(" Type "," Type ")" { TyProduct $2 $4 }

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
