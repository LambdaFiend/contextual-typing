{
module Lexer where
}

%wrapper "posn"

$white = [\ \t\n\r\b]
$digit = [0-9]
$lower = [a-z]
$upper = [A-Z]
$alpha = [a-zA-Z]
$digit1 = [1-9]
$text = [a-zA-Z0-9\ ]

tokens :-

$white+                          ;
(\\|"λ"|"Λ"|"lambda"|"Lambda")   { \pos _ -> Token pos LAMBDA }
("->"|"→")                       { \pos _ -> Token pos ARROW }
("All"|"forall"|"∀")             { \pos _ -> Token pos FORALL }
"@"                              { \pos _ -> Token pos APPLY }
","                              { \pos _ -> Token pos COMMA }
"::"                             { \pos _ -> Token pos DOUBLECOLON }
":"                              { \pos _ -> Token pos COLON }
"("                              { \pos _ -> Token pos LPAREN }
")"                              { \pos _ -> Token pos RPAREN }
"["                              { \pos _ -> Token pos LSBRACK }
"]"                              { \pos _ -> Token pos RSBRACK }
"&&"                             { \pos _ -> Token pos AND }
"||"                             { \pos _ -> Token pos OR }
"not"                            { \pos _ -> Token pos NOT }
"fix"                            { \pos _ -> Token pos FIX }
"+F"                             { \pos _ -> Token pos PLUSFLOAT }
"+I"                             { \pos _ -> Token pos PLUSINT }
"-F"                             { \pos _ -> Token pos MINUSFLOAT }
"-I"                             { \pos _ -> Token pos MINUSINT }
"*F"                             { \pos _ -> Token pos MULTFLOAT }
"*I"                             { \pos _ -> Token pos MULTINT }
"/F"                             { \pos _ -> Token pos DIVFLOAT }
"/I"                             { \pos _ -> Token pos DIVINT }
"<F"                             { \pos _ -> Token pos LTFLOAT }
"<I"                             { \pos _ -> Token pos LTINT }
"<C"                             { \pos _ -> Token pos LTCHAR }
">F"                             { \pos _ -> Token pos GTFLOAT }
">I"                             { \pos _ -> Token pos GTINT }
">C"                             { \pos _ -> Token pos GTCHAR }
"<=F"                            { \pos _ -> Token pos LEFLOAT }
"<=I"                            { \pos _ -> Token pos LEINT }
"<=C"                            { \pos _ -> Token pos LECHAR }
">=F"                            { \pos _ -> Token pos GEFLOAT }
">=I"                            { \pos _ -> Token pos GEINT }
">=C"                            { \pos _ -> Token pos GECHAR }
"/=F"                            { \pos _ -> Token pos NEFLOAT }
"/=I"                            { \pos _ -> Token pos NEINT }
"/=B"                            { \pos _ -> Token pos NEBOOL }
"/=U"                            { \pos _ -> Token pos NEUNIT }
"/=C"                            { \pos _ -> Token pos NECHAR }
"==F"                            { \pos _ -> Token pos EQFLOAT }
"==I"                            { \pos _ -> Token pos EQINT }
"==B"                            { \pos _ -> Token pos EQBOOL }
"==U"                            { \pos _ -> Token pos EQUNIT }
"==C"                            { \pos _ -> Token pos EQCHAR }
"="                              { \pos _ -> Token pos ASSIGN }
"let"                            { \pos _ -> Token pos LET }
"letrec"                         { \pos _ -> Token pos LETREC }
"in"                             { \pos _ -> Token pos IN }
"Float"                          { \pos _ -> Token pos TYFLOAT }
"Int"                            { \pos _ -> Token pos TYINT }
"Bool"                           { \pos _ -> Token pos TYBOOL }
"Char"                           { \pos _ -> Token pos TYCHAR }
"Top"                            { \pos _ -> Token pos TYTOP }
"Bot"                            { \pos _ -> Token pos TYBOT }
"True"                           { \pos _ -> Token pos TRUE }
"False"                          { \pos _ -> Token pos FALSE }
"if"                             { \pos _ -> Token pos IF }
"then"                           { \pos _ -> Token pos THEN }
"else"                           { \pos _ -> Token pos ELSE }
"head"                           { \pos _ -> Token pos HEAD }
"tail"                           { \pos _ -> Token pos TAIL }
"empty"                          { \pos _ -> Token pos EMPTY }
($digit1)($digit)*(".")($digit)+ { \pos s -> Token pos (TMFLOAT (read s)) }
"0"(".")($digit)*                { \pos s -> Token pos (TMFLOAT (read s)) }
($digit1)($digit)*               { \pos s -> Token pos (TMINT (read s)) }
"0"                              { \pos _ -> Token pos ZERO }
($lower)($digit|$lower|\')*      { \pos s -> Token pos (IDLower s) }
($upper)($digit|$lower|\')*      { \pos s -> Token pos (IDUpper s) }
"."                              { \pos _ -> Token pos DOT }
\'$text\'                        { \pos s -> case s of ('\'':x:'\'':[]) -> Token pos (TMCHAR x); _ -> Token pos (ERROR ("Lexing error, bad char term: " ++ s)) }
\"($text*)\"                     { \pos s -> Token pos (QUOTE s) }
.                                { \pos s -> Token pos (ERROR ("Lexing error: " ++ s)) }

{
data Token = Token
  { tokenPos :: AlexPosn
  , tokenDat :: TokenData
  }
  deriving (Eq, Show)

data TokenData
  = LAMBDA
  | ARROW
  | FORALL
  | APPLY
  | COMMA
  | DOT
  | DOUBLECOLON
  | COLON
  | LPAREN
  | RPAREN
  | LSBRACK
  | RSBRACK
  | ASSIGN
  | AND
  | OR
  | NOT
  | FIX
  | PLUSFLOAT
  | PLUSINT
  | MINUSFLOAT
  | MINUSINT
  | MULTFLOAT
  | MULTINT
  | DIVFLOAT
  | DIVINT
  | LTFLOAT
  | LTINT
  | LTCHAR
  | GTFLOAT
  | GTINT
  | GTCHAR
  | LEFLOAT
  | LEINT
  | LECHAR
  | GEFLOAT
  | GEINT
  | GECHAR
  | NEFLOAT
  | NEINT
  | NEBOOL
  | NEUNIT
  | NECHAR
  | EQFLOAT
  | EQINT
  | EQBOOL
  | EQUNIT
  | EQCHAR
  | EMPTY
  | LET
  | LETREC
  | IN
  | TYFLOAT
  | TYINT
  | TYBOOL
  | TYTOP
  | TYBOT
  | TYCHAR
  | TRUE
  | FALSE
  | IF
  | THEN
  | ELSE
  | HEAD
  | TAIL
  | ZERO
  | TMFLOAT Float
  | TMINT Int
  | TMCHAR Char
  | QUOTE String
  | IDLower String
  | IDUpper String
  | ERROR String
  deriving (Eq, Show)
}
