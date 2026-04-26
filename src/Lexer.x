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

$white+                       ;
(\\)|"λ"                      { \pos _ -> Token pos LAMBDA }
"Int"                         { \pos _ -> Token pos TYINT }
"Float"                       { \pos _ -> Token pos TYFLOAT }
"Top"                         { \pos _ -> Token pos TYTOP }
"="                           { \pos _ -> Token pos ASSIGN }
"&"                           { \pos _ -> Token pos ANDSYM }
"+"                           { \pos _ -> Token pos PLUS }
","                           { \pos _ -> Token pos COMMA }
":"                           { \pos _ -> Token pos COLON }
"("                           { \pos _ -> Token pos LPAREN }
")"                           { \pos _ -> Token pos RPAREN }
"{"                           { \pos _ -> Token pos LBRACK }
"}"                           { \pos _ -> Token pos RBRACK }
"->"|"→"                      { \pos _ -> Token pos ARROW }
($digit)+(".")($digit)+       { \pos s -> Token pos (TMFLOAT (read s)) }
($digit)+                     { \pos s -> Token pos (TMINT (read s)) }
($lower)($digit|$alpha)*(\')* { \pos s -> Token pos (ID s) }
"."                           { \pos _ -> Token pos DOT }
.                             { \pos s -> Token pos (ERROR ("Lexing error: " ++ s)) }

{
data Token = Token
  { tokenPos :: AlexPosn
  , tokenDat :: TokenData
  }
  deriving (Eq, Show)

data TokenData
  = LAMBDA
  | TYINT
  | TYFLOAT
  | TYTOP
  | ASSIGN
  | ANDSYM
  | PLUS
  | DOT
  | COMMA
  | COLON
  | LPAREN
  | RPAREN
  | LBRACK
  | RBRACK
  | ARROW
  | TMINT Int
  | TMFLOAT Float
  | ID String
  | ERROR String
  deriving (Eq, Show)
}
