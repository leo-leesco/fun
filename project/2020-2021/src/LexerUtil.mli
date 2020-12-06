open Lexing

(* [open_in filename] opens the specified file and produces a lexing buffer
   whose positions refer to [filename]. *)

val open_in: string -> lexbuf

(* [newline lexbuf] increments the line counter stored within [lexbuf]. *)

val newline: lexbuf -> unit

(* [setup sts] accepts a list of pairs of a string and a token. It sets up a
   pair of tables that translate (both ways) between strings and tokens, and
   returns functions that look up these tables (and can raise [Not_found]). *)

val setup: ('string * 'token) list -> ('string -> 'token) * ('token -> 'string)

(* [print_range f] prints a range (a pair of positions) on channel [f]. *)

val print_range: out_channel -> position * position -> unit

(* [error f lexbuf start_pos msg] reports a lexing error on channel [f] and
   exits with error code 1. The start position [start_pos] is optional; if
   absent, the start of the current lexeme is used. The end position is the
   end of the current lexeme. *)

val error: out_channel -> lexbuf -> position option -> string -> 'a
