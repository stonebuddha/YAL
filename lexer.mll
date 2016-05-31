{
open Parser
}

let white = [' ' '\009' '\012']
let int = ['0'-'9']+
let id = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '_' '0'-'9' '\'']*

rule read =
  parse
  | white+            { read lexbuf }
  | white*("\r")?"\n" { read lexbuf }
  | int               { INTV (int_of_string (Lexing.lexeme lexbuf)) }
  | "true"            { TRUE }
  | "false"           { FALSE }
  | "if"              { IF }
  | "then"            { THEN }
  | "else"            { ELSE }
  | "let"             { LET }
  | "in"              { IN }
  | "fn"              { FN }
  | "fix"             { FIX }
  | "lam"             { LAM }
  | "int"             { INT }
  | "bool"            { BOOL }
  | "unit"            { UNIT }
  | "end"             { END }
  | id                { ID (Lexing.lexeme lexbuf) }
  | "->"              { RIGHTARROW }
  | "("               { LPAREN }
  | ")"               { RPAREN }
  | ","               { COMMA }
  | ":"               { COLON }
  | "="               { EQ }
  | "{"               { LCURLY }
  | "}"               { RCURLY }
  | "["               { LSQUARE }
  | "]"               { RSQUARE }
  | "+"               { PLUS }
  | "-"               { MINUS }
  | "/"               { DIV }
  | "~"               { TILDE }
  | "<="              { LEQ }
  | "<"               { LT }
  | ">"               { GT }
  | "&&"              { AND }
  | "||"              { OR }
  | "|"               { BAR }
  | "*"               { TIMES }
  | "."               { DOT }
