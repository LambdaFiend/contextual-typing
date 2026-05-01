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
(\\|"λ"|"Λ"|lambda|Lambda)    { \pos _ -> Token pos LAMBDA }
("->"|"→")                    { \pos _ -> Token pos ARROW }
(All|forall|"∀")              { \pos _ -> Token pos FORALL }
"@"                           { \pos _ -> Token pos APPLY }
"."                           { \pos _ -> Token pos DOT }
":"                           { \pos _ -> Token pos COLON }
"("                           { \pos _ -> Token pos LPAREN }
")"                           { \pos _ -> Token pos RPAREN }
"="                           { \pos _ -> Token pos ASSIGN }
let                           { \pos _ -> Token pos LET }
in                            { \pos _ -> Token pos IN }
Int                           { \pos _ -> Token pos TYINT }
($digit)+                     { \pos s -> Token pos (TMINT (read s)) }
($lower)($digit|$lower)*(\')* { \pos s -> Token pos $ IDLower s }
($upper)($digit|$lower)*(\')* { \pos s -> Token pos $ IDUpper s }
.                             { \pos s -> Token pos $ ERROR ("Lexing error: " ++ s) }

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
  | DOT
  | COLON
  | LPAREN
  | RPAREN
  | ASSIGN
  | LET
  | IN
  | TYINT
  | TMINT Int
  | IDLower String
  | IDUpper String
  | ERROR String
  deriving (Eq, Show)
}
