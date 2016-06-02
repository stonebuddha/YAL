{
open Elaparser
}

let white = [' ' '\009' '\012']
let float = ['0'-'9']+ '.' ['0'-'9']*
let int = ['0'-'9']+
let id = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '_' '0'-'9' '\'']*

rule read =
  parse
  | white+            { read lexbuf }
  | white*("\r")?"\n" { read lexbuf }
  | float             { FLOATV (float_of_string (Lexing.lexeme lexbuf)) }
  | int               { INTV (int_of_string (Lexing.lexeme lexbuf)) }
  | "true"            { TRUE }
  | "false"           { FALSE }
  | "if"              { IF }
  | "then"            { THEN }
  | "else"            { ELSE }
  | "let"             { LET }
  | "in"              { IN }
  | "val"             { VAL }
  | "sort"            { SORT }
  | "fun"             { FUN }
  | "type"            { TYPE }
  | "bool"            { BOOL }
  | "int"             { INT }
  | "float"           { FLOAT }
  | "fn"              { FN }
  | "rec"             { REC }
  | "end"             { END }
  | "mat"             { MATRIX }
  | "vec"             { VECTOR }
  | "declare"         { DECLARE }
  | "unit"            { UNIT }
  | id                { ID (Lexing.lexeme lexbuf) }
  | "->"              { RIGHTARROW }
  | "=>"              { DRIGHTARROW }
  | "+."              { PLUSDOT }
  | "-."              { MINUSDOT }
  | "*."              { TIMESDOT }
  | "/."              { DIVDOT }
  | "<=."             { LEQDOT }
  | "<."              { LTDOT }
  | ">=."             { GEQDOT }
  | ">."              { GTDOT }
  | "!=."             { NEQDOT }
  | "=."              { EQDOT }
  | "+"               { PLUS }
  | "-"               { MINUS }
  | "*"               { TIMES }
  | "/"               { DIV }
  | "&&"              { AND }
  | "||"              { OR }
  | "<="              { LEQ }
  | "<"               { LT }
  | ">="              { GEQ }
  | ">"               { GT }
  | "!="              { NEQ }
  | "="               { EQ }
  | "("               { LPAREN }
  | ")"               { RPAREN }
  | "{"               { LCURLY }
  | "}"               { RCURLY }
  | "["               { LSQUARE }
  | "]"               { RSQUARE }
  | ";"               { SEMI }
  | ":"               { COLON }
  | "|"               { BAR }
  | "~"               { TILDE }
  | "."               { DOT }
  | ","               { COMMA }
  | eof               { EOF }
