open Lexing
open Printf

let open_in filename =
  let lexbuf = from_channel (open_in filename) in
  lexbuf.lex_curr_p <- {
    pos_fname = filename;
    pos_lnum  = 1;
    pos_bol   = 0;
    pos_cnum  = 0
  };
  lexbuf

let newline lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { pos with
    pos_lnum = pos.pos_lnum + 1;
    pos_bol = pos.pos_cnum;
  }

open Hashtbl

let setup sts =
  let direct = create 123
  and reverse = create 123 in
  List.iter (fun (s, t) ->
    add direct s t;
    add reverse t s
  ) sts;
  find direct, find reverse

let is_dummy (pos1, pos2) =
  pos1 == Lexing.dummy_pos && pos2 == Lexing.dummy_pos

let print_range f ((pos1, pos2) as range) =
  if is_dummy range then
    fprintf f "At an unknown location:\n"
  else
    let file = pos1.pos_fname in
    let line = pos1.pos_lnum in
    let char1 = pos1.pos_cnum - pos1.pos_bol in
    let char2 = pos2.pos_cnum - pos1.pos_bol in (* yes, [pos1.pos_bol] *)
    fprintf f "File \"%s\", line %d, characters %d-%d:\n"
      file line char1 char2
      (* use [char1 + 1] and [char2 + 1] if *not* using Caml mode *)

let error f lexbuf start_pos msg =
  let start_pos, end_pos =
    Option.value start_pos ~default:(Lexing.lexeme_start_p lexbuf),
    Lexing.lexeme_end_p lexbuf
  in
  print_range f (start_pos, end_pos);
  fprintf f "%s" msg;
  exit 0
