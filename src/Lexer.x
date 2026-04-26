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
"("                           { \pos _ -> Token pos LPAREN }
")"                           { \pos _ -> Token pos RPAREN }
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
  | DOT
  | LPAREN
  | RPAREN
  | TMINT Int
  | ID String
  | ERROR String
  deriving (Eq, Show)
}
