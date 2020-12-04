{

  open Lexing
  open Parser

  let error lexbuf start_pos msg =
    LexerUtil.error stderr lexbuf start_pos msg

  let pp_location _ _ = ()

  (* A table of keywords. *)

  let string2keyword, keyword2string =
    LexerUtil.setup [
      "def", DEF;
      "val", VAL;
      "handle", HANDLE;
      "Print", PRINT;
      "false", FALSE;
      "true", TRUE;
      "if", IF;
      "else", ELSE;
    ]

}

let newline =
  ('\010' | '\013' | "\013\010")

let whitespace =
  [ ' ' '\t' ]

let digit =
  [ '0'-'9' ]

let integer =
  ( "0x" | "0o" | "0b" )? digit+

let lowercase =
  ['a'-'z' '\223'-'\246' '\248'-'\255' '_']

let uppercase =
  ['A'-'Z' '\192'-'\214' '\216'-'\222']

let identchar =
  ['A'-'Z' 'a'-'z' '_' '\192'-'\214' '\216'-'\246' '\248'-'\255' '\'' '0'-'9']

let vvar =
  lowercase identchar*

let bvar =
  uppercase identchar*

rule main = parse
| newline
    { LexerUtil.newline lexbuf; main lexbuf }
| whitespace+
    { main lexbuf }
| vvar as x
    { try string2keyword x with Not_found -> VVAR x }
| bvar as x
    { try string2keyword x with Not_found -> BVAR x }
| "="
    { EQ }
| ";"
    { SEMI }
| ","
    { COMMA }
| "("
    { LPAR }
| ")"
    { RPAR }
| "{"
    { LBRACE }
| "}"
    { RBRACE }
| "(*"
    { comment (lexeme_start_p lexbuf) lexbuf; main lexbuf }
| "\""
    { string_literal (lexeme_start_p lexbuf) (Buffer.create 128) lexbuf }
| eof
    { EOF }
| _
    { error lexbuf None "Unexpected character.\n" }

and comment start_pos = parse
| "(*"
    { comment (lexeme_start_p lexbuf) lexbuf; comment start_pos lexbuf }
| "*)"
    { () }
| newline
    { LexerUtil.newline lexbuf; comment start_pos lexbuf }
| eof
    { error lexbuf (Some start_pos) "Unterminated comment.\n" }
| _
    { comment start_pos lexbuf }

and string_literal start_pos buffer = parse
| "\""
    { lexbuf.lex_start_p <- start_pos;
      STRING (Buffer.contents buffer) }
| newline
    { error lexbuf (Some start_pos)
        "Unexpected end of line inside a string literal.\n" }
| eof
    { error lexbuf (Some start_pos)
        "Unterminated string literal.\n" }
| "\\n"
    { Buffer.add_char buffer '\n';
      string_literal start_pos buffer lexbuf }
| _ as c
    { Buffer.add_char buffer c;
      string_literal start_pos buffer lexbuf }
