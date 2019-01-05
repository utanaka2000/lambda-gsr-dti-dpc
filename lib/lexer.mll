{
open Utils.Error

let reservedWords = [
  ("fun", fun r -> Parser.FUN r);
  ("true", fun r -> Parser.TRUE r);
  ("false", fun r ->  Parser.FALSE r);
  ("int", fun r ->  Parser.INT r);
  ("bool", fun r ->  Parser.BOOL r);
  ("unit", fun r ->  Parser.UNIT r);
  ("shift", fun r ->  Parser.SHIFT r);
  ("reset", fun r ->  Parser.RESET r);
  ("if", fun r ->  Parser.IF r);
  ("then", fun r ->  Parser.THEN r);
  ("else", fun r ->  Parser.ELSE r);
  ("pure", fun r ->  Parser.PURE r);
  ("let", fun r ->  Parser.LET r);
  ("in", fun r ->  Parser.IN r);
  ("rec", fun r -> Parser.REC r);
]

let range_of lexbuf =
  {
    start_p=Lexing.lexeme_start_p lexbuf;
    end_p=Lexing.lexeme_end_p lexbuf;
  }
}

rule main = parse
  [' ' '\t']+ { main lexbuf }
| [' ' '\t']* '\n' { Lexing.new_line lexbuf; main lexbuf }
| ['0'-'9']+
  {
    let value = int_of_string (Lexing.lexeme lexbuf) in
    let range = range_of lexbuf in
    Parser.INTV { value=value; range=range }
  }
| "(" { Parser.LPAREN (range_of lexbuf) }
| ")" { Parser.RPAREN (range_of lexbuf) }
| ":" { Parser.COLON (range_of lexbuf) }
| ";" { Parser.SEMI (range_of lexbuf) }
| ";;" { Parser.SEMISEMI (range_of lexbuf) }
| "->" { Parser.RARROW (range_of lexbuf) }
| "-" { Parser.MINUS (range_of lexbuf) }
| "/" { Parser.SLASH (range_of lexbuf) }
| "+" { Parser.PLUS (range_of lexbuf) }
| "*" { Parser.STAR (range_of lexbuf) }
| "?" { Parser.QUESTION (range_of lexbuf) }
| "^" { Parser.CARET (range_of lexbuf) }
| "#" { Parser.SHARP (range_of lexbuf) }
| "=" { Parser.EQUAL (range_of lexbuf) }
| ">" { Parser.GT (range_of lexbuf) }
| "<" { Parser.LT (range_of lexbuf) }

| ['a'-'z'] ['a'-'z' '0'-'9' '_' '\'']*
  {
    let id = Lexing.lexeme lexbuf in
    let range = range_of lexbuf in
    try
      (List.assoc id reservedWords) range
    with
    _ -> Parser.ID { value=id; range=range }
  }
| eof { exit 0 }
