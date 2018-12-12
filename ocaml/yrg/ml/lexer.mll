(* -*- tuareg -*- *)
{
  open Parser

  let next_line_and f lexbuf  =
    Lexing.new_line lexbuf;
    f lexbuf

}

let newline = ('\010' | '\013' | "\013\010")

let blank   = [' ' '\009' '\012']

let lowercase_alpha = ['a'-'z']

let uppercase_alpha = ['A'-'Z']

let digit = ['0'-'9']

let alpha = lowercase_alpha | uppercase_alpha

let alphanum = alpha | digit | '_'

let identifier = lowercase_alpha alphanum*

rule token = parse
  (** Layout *)
  | newline         { next_line_and token lexbuf }
  | blank+          { token lexbuf               }

  (** Keywords *)
  | "let"           { LET }
  | "in"            { IN }
  | "fun"           { FUN }

  (** Atoms *)
  | identifier as s { ID s }
  | digit+ as x     { INT (int_of_string x) }

  (** Punctuation *)
  | "("             { LPAREN }
  | ")"             { RPAREN }
  | "->"            { RARROW }
  | "="             { EQUAL  }

  | eof             { EOF }
  | _ as c          { failwith (Printf.sprintf "Invalid character: `%c'." c) }
