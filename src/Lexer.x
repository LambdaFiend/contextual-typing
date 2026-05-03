{
module Lexer where
}

%wrapper "posn"

$white = [\ \t\n\r\b]
$digit = [0-9]
$lower = [a-z]
$upper = [A-Z]
$alpha = [a-zA-Z]

tokens :-

$white+                        ;
"fst"                          { \pos _ -> Token pos FST }
"snd"                          { \pos _ -> Token pos SND }
(\\|"λ"|"Λ"|"lambda"|"Lambda") { \pos _ -> Token pos LAMBDA }
("->"|"→")                     { \pos _ -> Token pos ARROW }
("All"|"forall"|"∀")           { \pos _ -> Token pos FORALL }
"@"                            { \pos _ -> Token pos APPLY }
","                            { \pos _ -> Token pos COMMA }
":"                            { \pos _ -> Token pos COLON }
"("                            { \pos _ -> Token pos LPAREN }
")"                            { \pos _ -> Token pos RPAREN }
"="                            { \pos _ -> Token pos ASSIGN }
"&&"                           { \pos _ -> Token pos AND }
"||"                           { \pos _ -> Token pos OR }
"not"                          { \pos _ -> Token pos NOT }
"+F"                           { \pos _ -> Token pos PLUSFLOAT }
"+I"                           { \pos _ -> Token pos PLUSINT }
"-F"                           { \pos _ -> Token pos MINUSFLOAT }
"-I"                           { \pos _ -> Token pos MINUSINT }
"*F"                           { \pos _ -> Token pos MULTFLOAT }
"*I"                           { \pos _ -> Token pos MULTINT }
"/F"                           { \pos _ -> Token pos DIVFLOAT }
"/I"                           { \pos _ -> Token pos DIVINT }
"let"                          { \pos _ -> Token pos LET }
"in"                           { \pos _ -> Token pos IN }
"Float"                        { \pos _ -> Token pos TYFLOAT }
"Int"                          { \pos _ -> Token pos TYINT }
"Bool"                         { \pos _ -> Token pos TYBOOL }
"Unit"                         { \pos _ -> Token pos TYUNIT }
"True"                         { \pos _ -> Token pos TRUE }
"False"                        { \pos _ -> Token pos FALSE }
"if"                           { \pos _ -> Token pos IF }
"then"                         { \pos _ -> Token pos THEN }
"else"                         { \pos _ -> Token pos ELSE }
($digit)+(".")($digit)+        { \pos s -> Token pos (TMFLOAT (read s)) }
($digit)+                      { \pos s -> Token pos (TMINT (read s)) }
($lower)($digit|$lower)*(\')*  { \pos s -> Token pos $ IDLower s }
($upper)($digit|$lower)*(\')*  { \pos s -> Token pos $ IDUpper s }
"."                            { \pos _ -> Token pos DOT }
.                              { \pos s -> Token pos $ ERROR ("Lexing error: " ++ s) }

{
data Token = Token
  { tokenPos :: AlexPosn
  , tokenDat :: TokenData
  }
  deriving (Eq, Show)

data TokenData
  = FST
  | SND
  | LAMBDA
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
  | LET
  | IN
  | TYFLOAT
  | TYINT
  | TYBOOL
  | TYUNIT
  | TRUE
  | FALSE
  | IF
  | THEN
  | ELSE
  | TMFLOAT Float
  | TMINT Int
  | IDLower String
  | IDUpper String
  | ERROR String
  deriving (Eq, Show)
}
