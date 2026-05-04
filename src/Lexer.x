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

tokens :-

$white+                          ;
(\\|"λ"|"Λ"|"lambda"|"Lambda")   { \pos _ -> Token pos LAMBDA }
("->"|"→")                       { \pos _ -> Token pos ARROW }
("All"|"forall"|"∀")             { \pos _ -> Token pos FORALL }
"@"                              { \pos _ -> Token pos APPLY }
","                              { \pos _ -> Token pos COMMA }
":"                              { \pos _ -> Token pos COLON }
"("                              { \pos _ -> Token pos LPAREN }
")"                              { \pos _ -> Token pos RPAREN }
"&&"                             { \pos _ -> Token pos AND }
"||"                             { \pos _ -> Token pos OR }
"not"                            { \pos _ -> Token pos NOT }
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
">F"                             { \pos _ -> Token pos GTFLOAT }
">I"                             { \pos _ -> Token pos GTINT }
"<=F"                            { \pos _ -> Token pos LEFLOAT }
"<=I"                            { \pos _ -> Token pos LEINT }
">=F"                            { \pos _ -> Token pos GEFLOAT }
">=I"                            { \pos _ -> Token pos GEINT }
"/=F"                            { \pos _ -> Token pos NEFLOAT }
"/=I"                            { \pos _ -> Token pos NEINT }
"/=B"                            { \pos _ -> Token pos NEBOOL }
"/=U"                            { \pos _ -> Token pos NEUNIT }
"==F"                            { \pos _ -> Token pos EQFLOAT }
"==I"                            { \pos _ -> Token pos EQINT }
"==B"                            { \pos _ -> Token pos EQBOOL }
"==U"                            { \pos _ -> Token pos EQUNIT }
"="                              { \pos _ -> Token pos ASSIGN }
"let"                            { \pos _ -> Token pos LET }
"in"                             { \pos _ -> Token pos IN }
"Float"                          { \pos _ -> Token pos TYFLOAT }
"Int"                            { \pos _ -> Token pos TYINT }
"Bool"                           { \pos _ -> Token pos TYBOOL }
"True"                           { \pos _ -> Token pos TRUE }
"False"                          { \pos _ -> Token pos FALSE }
"if"                             { \pos _ -> Token pos IF }
"then"                           { \pos _ -> Token pos THEN }
"else"                           { \pos _ -> Token pos ELSE }
($digit1)($digit)*(".")($digit)+ { \pos s -> Token pos (TMFLOAT (read s)) }
"0"(".")($digit)*                { \pos s -> Token pos (TMFLOAT (read s)) }
($digit1)($digit)*               { \pos s -> Token pos (TMINT (read s)) }
"0"                              { \pos _ -> Token pos ZERO }
($lower)($digit|$lower)*(\')*    { \pos s -> Token pos $ IDLower s }
($upper)($digit|$lower)*(\')*    { \pos s -> Token pos $ IDUpper s }
"."                              { \pos _ -> Token pos DOT }
.                                { \pos s -> Token pos $ ERROR ("Lexing error: " ++ s) }

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
  | COLON
  | LPAREN
  | RPAREN
  | ASSIGN
  | AND
  | OR
  | NOT
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
  | GTFLOAT
  | GTINT
  | LEFLOAT
  | LEINT
  | GEFLOAT
  | GEINT
  | NEFLOAT
  | NEINT
  | NEBOOL
  | NEUNIT
  | EQFLOAT
  | EQINT
  | EQBOOL
  | EQUNIT
  | LET
  | IN
  | TYFLOAT
  | TYINT
  | TYBOOL
  | TRUE
  | FALSE
  | IF
  | THEN
  | ELSE
  | ZERO
  | TMFLOAT Float
  | TMINT Int
  | IDLower String
  | IDUpper String
  | ERROR String
  deriving (Eq, Show)
}
