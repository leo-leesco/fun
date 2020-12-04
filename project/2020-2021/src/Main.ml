open Printf

(* ------------------------------------------------------------------------- *)

(* Parse the command line. *)

let execute =
  ref false

let typecheck =
  ref false

let filename =
  ref None

let usage =
  sprintf "Usage: %s <options> <filename>\n" Sys.argv.(0)

let () =
  Arg.parse (Arg.align [
    "--execute", Arg.Set execute, " execute the program";
    "--typecheck", Arg.Set typecheck, " typecheck the program";
  ]) (fun name -> filename := Some name) usage

let execute =
  !execute

let typecheck =
  !typecheck

let filename =
  match !filename with
  | Some filename ->
      filename
  | None ->
      fprintf stderr "%s%!" usage;
      exit 1

(* ------------------------------------------------------------------------- *)

(* Reading, lexing and parsing a source file. *)

let read filename : SystemXi.statement =
  let lexbuf = LexerUtil.open_in filename in
  try
    Parser.phrase Lexer.main lexbuf
  with Parser.Error ->
    LexerUtil.error stderr lexbuf None "Syntax error.\n"

(* -------------------------------------------------------------------------- *)

(* The main program. *)

(* Our test system expects the program to terminate with exit code 0, so we
   always produce this exit code, even if an error occurred.

   The test system records what is printed on [stdout] and compares it with an
   expected output. What is printed on [stderr] is recorded but not compared
   against a reference.

   The interpreter sends the output of [print] instructions to [stdout]. If a
   runtime error occurs, then it sends the string [RUNTIME ERROR] to [stdout]
   and a description of the error to [stderr].

   The type-checker sends nothing to [stdout]. If a type error occurs, then it
   sends the string [TYPE ERROR] to [stdout] and a description of the error to
   [stderr]. *)

let () =
  try
    let s = read filename in
    if typecheck then
      TypeCheck.typecheck s;
    if execute then
      Interpret.execute (Translate.translate_statement s)
  with
  | e ->
      printf "%s\n" (Printexc.to_string e);
      Printexc.print_backtrace stdout;
      exit 0
