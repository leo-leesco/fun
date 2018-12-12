let filename = ref "in.ml"

let usage = "\
miniml [options] file.ml
"

let parse_command_line =
  Arg.(parse (align
    [
      "--debug", Set Options.debug,
      " Set debugging flag.";

      "--constraint", Set Options.use_constraints,
      " Use constraint-based inference"
    ]
  )) ( ( := ) filename) usage

let parse () =
  let cin = open_in !filename in
  let lexbuf = Lexing.from_channel cin in
  Parser.program Lexer.token lexbuf

let show ast =
  Printf.printf "Elaboration:\n%s\n" (Syntax.XTerm.string_of_xterm ast)

let elaborate p =
  if !Options.use_constraints then
    ConstraintElaboration.elaborate p
  else
    Elaboration.elaborate p

let main =
  parse () |> elaborate |> Typechecker.check |> show
