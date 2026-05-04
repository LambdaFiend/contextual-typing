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
","     { Token pos COMMA }
"."     { Token pos DOT }
"::"    { Token pos DOUBLECOLON }
":"     { Token pos COLON }
"("     { Token pos LPAREN }
")"     { Token pos RPAREN }
"["     { Token pos LSBRACK }
"]"     { Token pos RSBRACK }
"="     { Token pos ASSIGN }
"&&"    { Token pos AND }
"||"    { Token pos OR }
"not"   { Token pos NOT }
"fix"   { Token pos FIX }
"+F"    { Token pos PLUSFLOAT }
"+I"    { Token pos PLUSINT }
"-F"    { Token pos MINUSFLOAT }
"-I"    { Token pos MINUSINT }
"*F"    { Token pos MULTFLOAT }
"*I"    { Token pos MULTINT }
"/F"    { Token pos DIVFLOAT }
"/I"    { Token pos DIVINT }
let     { Token pos LET }
letrec  { Token pos LETREC }
in      { Token pos IN }
tyfloat { Token pos TYFLOAT }
tyint   { Token pos TYINT }
tybool  { Token pos TYBOOL }
tytop   { Token pos TYTOP }
tybot   { Token pos TYBOT }
tychar  { Token pos TYCHAR }
true    { Token pos TRUE }
false   { Token pos FALSE }
if      { Token pos IF }
then    { Token pos THEN }
else    { Token pos ELSE }
tmfloat { Token pos (TMFLOAT u) }
tmint   { Token pos (TMINT n) }
tmchar  { Token pos (TMCHAR c) }
"<F"    { Token pos LTFLOAT }
"<I"    { Token pos LTINT }
"<C"    { Token pos LTCHAR }
">F"    { Token pos GTFLOAT }
">I"    { Token pos GTINT }
">C"    { Token pos GTCHAR }
"<=F"	{ Token pos LEFLOAT }
"<=I"	{ Token pos LEINT }
"<=C"	{ Token pos LECHAR }
">=F"	{ Token pos GEFLOAT }
">=I"	{ Token pos GEINT }
">=C"	{ Token pos GECHAR }
"==F"   { Token pos EQFLOAT }
"==I"   { Token pos EQINT }
"==B"   { Token pos EQBOOL }
"==U"   { Token pos EQUNIT }
"==C"   { Token pos EQCHAR }
"/=F"   { Token pos NEFLOAT }
"/=I"   { Token pos NEINT }
"/=B"   { Token pos NEBOOL }
"/=U"   { Token pos NEUNIT }
"/=C"   { Token pos NECHAR }
"head"  { Token pos HEAD }
"tail"  { Token pos TAIL }
"empty" { Token pos EMPTY }
"0"     { Token pos ZERO }
quote   { Token pos (QUOTE s) }
idLower { Token pos (IDLower s) }
idUpper { Token pos (IDUpper s) }

%%

Term
  : Abs      { $1 }
  | Let      { $1 }
  | If       { $1 }
  | ConsList { $1 }

If : if Term then Term else Term { TermNode (tokenPos $1) (TmIf $2 $4 $6) }

Let
  : let NameLower "=" Term in Term                     { TermNode (tokenPos $1) (TmApp (TermNode (tokenPos $3) (TmAbs (snd $2) $6)) $4) }
  | let NameLower ":" Type "=" Term in Term            { TermNode (tokenPos $1) (TmApp (TermNode (tokenPos $5) (TmAbsAnno (snd $2) $4 $8)) (TermNode (tokenPos $3) (TmAnno $6 $4))) }
  | let NameLower LetMany "=" Term in Term             { TermNode (tokenPos $1) (TmApp (TermNode (tokenPos $4) (TmAbs (snd $2) $7)) ($3 $5)) }
  | let NameLower ":" Type LetMany "=" Term in Term    { TermNode (tokenPos $1) (TmApp (TermNode (tokenPos $6) (TmAbsAnno (snd $2) $4 $9)) (TermNode (tokenPos $3) (TmAnno ($5 $7) $4))) }
  | letrec NameLower "=" Term in Term                  { TermNode (tokenPos $1) (TmApp (TermNode (tokenPos $3) (TmAbs (snd $2) $6)) (TermNode (tokenPos $3) (TmFix (TermNode (tokenPos $3) (TmAbs (snd $2) $4))))) }
  | letrec NameLower ":" Type "=" Term in Term         { TermNode (tokenPos $1) (TmApp (TermNode (tokenPos $3) (TmAbsAnno (snd $2) $4 $8)) (TermNode (tokenPos $3) (TmAnno (TermNode (tokenPos $3) (TmFix (TermNode (tokenPos $3) (TmAbsAnno (snd $2) $4 $6)))) $4))) }
  | letrec NameLower LetMany "=" Term in Term          { TermNode (tokenPos $1) (TmApp (TermNode (tokenPos $4) (TmAbs (snd $2) $7)) (TermNode (tokenPos $4) (TmFix (TermNode (tokenPos $4) (TmAbs (snd $2) ($3 $5)))))) }
  | letrec NameLower ":" Type LetMany "=" Term in Term { TermNode (tokenPos $1) (TmApp (TermNode (tokenPos $3) (TmAbsAnno (snd $2) $4 $9)) (TermNode (tokenPos $3) (TmAnno (TermNode (tokenPos $3) (TmFix (TermNode (tokenPos $3) (TmAbsAnno (snd $2) $4 ($5 $7))))) $4))) }

LetMany :: { TermNode -> TermNode }
  : NameLower LetMany                                       { \x -> TermNode (fst $1) (TmAbs (snd $1) ($2 x)) }
  | NameLower                                               { \x -> TermNode (fst $1) (TmAbs (snd $1) x) }
  | "(" NameLower "," UncurriedAbs ")" LetMany              { \x -> TermNode (tokenPos $1) (TmAbsUnc ((snd $2) : $4) ($6 x)) }
  | "(" NameLower "," UncurriedAbs ")"                      { \x -> TermNode (tokenPos $1) (TmAbsUnc ((snd $2) : $4) x) }
  | NameLower ":" Type LetMany                              { \x -> TermNode (fst $1) (TmAbsAnno (snd $1) $3 ($4 x)) }
  | NameLower ":" Type                                      { \x -> TermNode (fst $1) (TmAbsAnno (snd $1) $3 x) }
  | "(" NameLower ":" Type "," UncurriedAbsAnno ")" LetMany { \x -> TermNode (tokenPos $1) (TmAbsUncAnno ((snd $2) : (fst $6)) ($4 : (snd $6)) ($8 x)) }
  | "(" NameLower ":" Type "," UncurriedAbsAnno ")"         { \x -> TermNode (tokenPos $1) (TmAbsUncAnno ((snd $2) : (fst $6)) ($4 : (snd $6)) x) }
  | "λ" NameUpper LetMany                                   { \x -> TermNode (fst $2) (TmTyAbs (snd $2) ($3 x)) }
  | "λ" NameUpper                                           { \x -> TermNode (fst $2) (TmTyAbs (snd $2) x) }

Abs
  : "λ" ManyLowerAbs                                             { $2 }
  | "λ" ManyUpperAbs                                             { $2 }
  | "λ" "(" NameLower ")" "." Term                               { TermNode (tokenPos $1) (TmAbs (snd $3) $6) }
  | "λ" "(" NameLower ":" Type ")" "." Term                      { TermNode (tokenPos $1) (TmAbsAnno (snd $3) $5 $8) }
  | "λ" "(" NameLower "," UncurriedAbs ")" "." Term              { TermNode (tokenPos $1) (TmAbsUnc ((snd $3) : $5) $8) }
  | "λ" "(" NameLower ":" Type "," UncurriedAbsAnno ")" "." Term { TermNode (tokenPos $1) (TmAbsUncAnno ((snd $3) : (fst $7)) ($5 : (snd $7)) $10) }

UncurriedAbsAnno
  : NameLower ":" Type "," UncurriedAbsAnno { ((snd $1) : fst $5, $3 : snd $5) }
  | NameLower ":" Type                      { ((snd $1) : [], $3 : []) }

UncurriedAbs
  : NameLower "," UncurriedAbs { (snd $1) : $3 }
  | NameLower                  { (snd $1) : [] }

ManyLowerAbs
  : NameLower ManyLowerAbs          { TermNode (fst $1) (TmAbs (snd $1) $2) }
  | NameLower "." Term              { TermNode (fst $1) (TmAbs (snd $1) $3) }
  | NameLower ":" Type ManyLowerAbs { TermNode (fst $1) (TmAbsAnno (snd $1) $3 $4) }
  | NameLower ":" Type "." Term     { TermNode (fst $1) (TmAbsAnno (snd $1) $3 $5) }

ManyUpperAbs
  : NameUpper ManyUpperAbs { TermNode (fst $1) (TmTyAbs (snd $1) $2) }
  | NameUpper "." Term     { TermNode (fst $1) (TmTyAbs (snd $1) $3) }

ConsList
  : App "::" ConsList { TermNode (tokenPos $2) (TmCons $1 $3) }
  | AppAbs            { $1 }

AppAbs
  : App Abs      { TermNode (getFI $1) (TmApp $1 $2) }
  | App          { $1 }

App
  : App Anno     { TermNode (getFI $2) (TmApp $1 $2) }
  | App "@" Type { TermNode (tokenPos $2) (TmTyApp $1 $3) }
  | Anno         { $1 }

Anno
  : Proj ":" Type { TermNode (tokenPos $2) (TmAnno $1 $3) }
  | Proj          { $1 }

Proj
  : Proj "." tmint { TermNode (tokenPos $2) (TmProj $1 ((\(TMINT s) -> s) (tokenDat $3))) }
  | Atom           { $1 }

Atom
  : Value                  { $1 }
  | "(" Term ")"           { $2 }
  | "(" Term "," Tuple ")" { TermNode (tokenPos $1) (TmTuple ($2 : $4)) }
  | "fix" "(" Term ")"     { TermNode (tokenPos $1) (TmFix $3) }
  | "[" ManyList "]"       { $2 }
  | quote                  { stringToCons ((\(QUOTE s) -> s) (tokenDat $1)) (tokenPos $1) }

ManyList
  : Term "," ManyList { TermNode (tokenPos $2) (TmCons $1 $3) }
  | Term              { TermNode (getFI $1) (TmCons $1 (TermNode (getFI $1) TmNil)) }

Tuple
  : Term "," Tuple { $1 : $3 }
  | Term           { $1 : [] }

Value
  : NameLower { TermNode (fst $1) (TmVarRaw (snd $1)) }
  | "empty"   { TermNode (tokenPos $1) (TmConst ConstEmpty) }
  | "head"    { TermNode (tokenPos $1) (TmConst ConstHead) }
  | "tail"    { TermNode (tokenPos $1) (TmConst ConstTail) }
  | "(" ")"   { TermNode (tokenPos $1) (TmConst ConstUnit) }
  | "[" "]"   { TermNode (tokenPos $1) TmNil }
  | tmfloat   { TermNode (tokenPos $1) (TmConst (ConstFloat ((\(TMFLOAT s) -> s) (tokenDat $1)))) }
  | tmint     { TermNode (tokenPos $1) (TmConst (ConstInt ((\(TMINT s) -> s) (tokenDat $1)))) }
  | tmchar    { TermNode (tokenPos $1) (TmConst (ConstChar ((\(TMCHAR s) -> s) (tokenDat $1)))) }
  | "0"       { TermNode (tokenPos $1) (TmConst (ConstInt 0)) }
  | "+F"      { TermNode (tokenPos $1) (TmConst (ConstOpF PlusOp)) }
  | "+I"      { TermNode (tokenPos $1) (TmConst (ConstOpI PlusOp)) }
  | "-F"      { TermNode (tokenPos $1) (TmConst (ConstOpF MinusOp)) }
  | "-I"      { TermNode (tokenPos $1) (TmConst (ConstOpI MinusOp)) }
  | "*F"      { TermNode (tokenPos $1) (TmConst (ConstOpF MultOp)) }
  | "*I"      { TermNode (tokenPos $1) (TmConst (ConstOpI MultOp)) }
  | "/F"      { TermNode (tokenPos $1) (TmConst (ConstOpF DivOp)) }
  | "/I"      { TermNode (tokenPos $1) (TmConst (ConstOpI DivOp)) }
  | "<F"      { TermNode (tokenPos $1) (TmConst (ConstOpFB LTOp)) }
  | "<I"      { TermNode (tokenPos $1) (TmConst (ConstOpIB LTOp)) }
  | "<C"      { TermNode (tokenPos $1) (TmConst (ConstOpCB LTOp)) }
  | ">F"      { TermNode (tokenPos $1) (TmConst (ConstOpFB GTOp)) }
  | ">I"      { TermNode (tokenPos $1) (TmConst (ConstOpIB GTOp)) }
  | ">C"      { TermNode (tokenPos $1) (TmConst (ConstOpCB GTOp)) }
  | "<=F"     { TermNode (tokenPos $1) (TmConst (ConstOpFB LEOp)) }
  | "<=I"     { TermNode (tokenPos $1) (TmConst (ConstOpIB LEOp)) }
  | "<=C"     { TermNode (tokenPos $1) (TmConst (ConstOpCB LEOp)) }
  | ">=F"     { TermNode (tokenPos $1) (TmConst (ConstOpFB GEOp)) }
  | ">=I"     { TermNode (tokenPos $1) (TmConst (ConstOpIB GEOp)) }
  | ">=C"     { TermNode (tokenPos $1) (TmConst (ConstOpCB GEOp)) }
  | "==F"     { TermNode (tokenPos $1) (TmConst (ConstOpFB EqOp)) }
  | "==I"     { TermNode (tokenPos $1) (TmConst (ConstOpIB EqOp)) }
  | "==B"     { TermNode (tokenPos $1) (TmConst (ConstOpB EqOpB)) }
  | "==U"     { TermNode (tokenPos $1) (TmConst ConstOpU) }
  | "==C"     { TermNode (tokenPos $1) (TmConst (ConstOpCB EqOp)) }
  | "/=F"     { TermNode (tokenPos $1) (TmConst (ConstOpFB NEOp)) }
  | "/=I"     { TermNode (tokenPos $1) (TmConst (ConstOpIB NEOp)) }
  | "/=B"     { TermNode (tokenPos $1) (TmConst (ConstOpB NEOpB)) }
  | "/=U"     { TermNode (tokenPos $1) (TmConst ConstOpNU) }
  | "/=C"     { TermNode (tokenPos $1) (TmConst (ConstOpCB NEOp)) }
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
  : NameUpper                  { TyVarRaw (snd $1) }
  | tyfloat                    { TyFloat }
  | tyint                      { TyInt }
  | tybool                     { TyBool }
  | tytop                      { TyTop }
  | tybot                      { TyBot }
  | tychar                     { TyChar }
  | "[" Type "]"               { TyList $2 }
  | "(" ")"                    { TyUnit }
  | "(" Type ")"               { $2 }
  | "(" Type "," TypeTuple ")" { TyTuple ($2 : $4) }

TypeTuple
  : Type "," TypeTuple { $1 : $3 }
  | Type               { $1 : [] }

{
stringToCons :: String -> AlexPosn -> TermNode
stringToCons [] pos = TermNode pos TmNil
stringToCons (c:cs) pos = TermNode pos (TmCons (TermNode pos (TmConst (ConstChar c))) (stringToCons cs pos))

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
