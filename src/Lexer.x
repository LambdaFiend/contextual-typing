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
":"                           { \pos _ -> Token pos COLON }
"("                           { \pos _ -> Token pos LPAREN }
")"                           { \pos _ -> Token pos RPAREN }
"->"|"→"                      { \pos _ -> Token pos ARROW }
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
  | DOT
  | COLON
  | LPAREN
  | RPAREN
  | ARROW
  | TMINT Int
  | ID String
  | ERROR String
  deriving (Eq, Show)
}
