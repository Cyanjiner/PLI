(*  COMP 323 sample code:  standard driver.
*   
*   After building this driver, execute
*
*     $ ./driver
*
*   in the shell to get usage instructions.
*
*   N. Danner
*)

structure Main =
struct

  structure Toks = MLMinusTokens

  structure Lex : LEXER =
  struct
    type token = Toks.token

    type strm = MLMinusLexer.strm

    fun lex strm = 
      case MLMinusLexer.lex (AntlrStreamPos.mkSourcemap()) strm of
           (t, _, s) => (t, s)
  end
  structure Parse = ParseFn(Lex)

  structure I = CEKInterp

  structure T = TextIO

  val lex = Lex.lex

  (*  printnl s = ().
  *
  *   As a side-effect, s will be printed to the terminal followed by a newline.
  *)
  fun printnl(s : string) : unit =
    print (String.concat [s, "\n"])

  val printnls = printnl o String.concat

  (* doLex strm = ()
  *
  * Side-effect:  prints tokens from strm to terminal until EOF reached.
  *)
  fun doLex (strm : Lex.strm) : unit =
  let
    fun printTokens (strm : Lex.strm) : unit =
      case lex strm of
           (Toks.EOF, _) => printnl (Toks.toString Toks.EOF)
         | (t, strm) => print ((Toks.toString t) ^ " ") 
                           before printTokens strm
  in
    printTokens strm
  end

  (*  tokStreamToString n <t_0,...> 
  *     = String.concatWith " " [t_0,...,t_{n-1}], t_i <> EOF for i < n,
  *       String.concatWith " " [t_0,...,t_{j-1}], t_j = EOF for j < n.
  *)
  fun tokStreamToString (n : int) (strm : Lex.strm) : string =
    if n = 0 then "..."
    else 
      case lex strm of
           (Toks.EOF, _) => Toks.toString Toks.EOF
         | (t, strm) => (Toks.toString t) ^ " " ^ (tokStreamToString n strm)

  val doParseExp : Lex.strm -> unit =
    printnl o Ast.expToString o Parse.parseExp

  val doParsePgm : Lex.strm -> unit =
    printnl o Ast.pgmToString o Parse.parsePgm

  val doEval : Lex.strm -> unit =
  (
    CEKInterp.Store.makeStore(5) ;
    printnl o CEKInterp.valueToString o CEKInterp.evalExp o Parse.parseExp
  )

  fun doExec (s  : Lex.strm) : unit =
    let
      val _ = CEKInterp.Store.makeStore(1000)
      val _ = CEKInterp.enableGC := false
    in
      (CEKInterp.execPgm o Parse.parsePgm) s
    end

  fun doExecGC (s : Lex.strm) : unit =
    let
      val _ = CEKInterp.Store.makeStore(10)
      val _ = CEKInterp.enableGC := true
    in
      (CEKInterp.execPgm o Parse.parsePgm) s
    end

  val doCheckExp : Lex.strm -> unit =
    printnl o Type.typeToString o Type.typeOf o Type.checkExp o Parse.parseExp

  fun doCheckPgm (s : Lex.strm) : unit =
  let
    fun toIdsTyps (ss : Type.stm list) : (Ast.ident*Type.typ) list =
      case ss of
           [] => []
         | (Type.ValDec(id, t, _) | Type.FunDec(id, t, _, _)) :: ss => 
             (id, t) :: toIdsTyps ss
         | Type.DoDec _ :: ss => toIdsTyps ss

    val Type.Program ss = (Type.checkPgm o Parse.parsePgm) s
  in
    (printnl o 
    ListFormat.fmt {
      init="", sep="\n", final="",
      fmt=fn (x, t) => x ^ " : " ^ Type.typeToString t
    } o
    toIdsTyps) ss
  end

  fun doCompileExp (strm : Lex.strm) : unit =
  let
    val outs = T.openOut "C.j"
  in
      Compile.compileExp
        outs
        ((Type.checkExp o Parse.parseExp) strm) ;
      T.closeOut outs ;
      printnl "Compilation successful"
  end

  fun doCompilePgm (filename : string, strm : Lex.strm) : unit =
  let
    val dir = OS.Path.dir filename
    val fileBase = OS.Path.base filename
    val jFile = OS.Path.joinBaseExt {base=fileBase, ext=SOME "j"}
    val outs = T.openOut jFile
  in
    Compile.compilePgm
      outs
      ((Type.checkPgm o Parse.parsePgm) strm) ;
      T.closeOut outs ;
      printnl "Compilation successful"
  end



  structure M = SplayMapFn(
    struct type ord_key = string val compare = String.compare end : ORD_KEY)

  exception Usage
  val usage = String.concatWith "\n" [
    "driver cmd [--arg] s",
    "",
    "Process the file s according to cmd.  Possible values of cmd are:",
    "",
    "\tlex:       perform lexical analysis and print the token sequence.",
    "\tparseExp:  parse as expression and print the abstract syntax tree.",
    "\tparsePgm:  parse as program and print the abstract syntax tree.",
    "\teval:      evaluate as an expression and print the result.",
    "\texec:      execute as a program (without garbage collection).",
    "\texec-gc:   execute as a program (with garbage collection).",
    "\tcheckExp:  infer the type of an expression.",
    "\tcheckPgm:  type-check the program.",
    "\tcompileExp:compile expression to a program that computes the",
    "             expression.",
    "\tcompilePgm:compile program.",
    "",
    "Options:",
    "\t--arg:   process s itself; i.e., s does not name a file to read",
    "\n"
  ]

  fun main(arg0 : string, argv : string list) : int =
  let

    (*  A handler is a value of type (string * stream) -> unit, where 
    *  hdlr(s, st) processes the argument s, given that st is the contents of s
    *  as a stream.  We need s and st because while most handlers only care
    *  about st, the compilation handler will need s.
    *)
    val handlers = [
      ("lex", doLex o #2),
      ("parseExp", doParseExp o #2),
      ("parsePgm", doParsePgm o #2),
      ("eval", doEval o #2),
      ("exec", doExec o #2),
      ("exec-gc", doExecGC o #2),
      ("checkExp", doCheckExp o #2),
      ("checkPgm", doCheckPgm o #2),
      ("compileExp", doCompileExp o #2),
      ("compilePgm", doCompilePgm)
    ]

    val makeHandlerMap =
      foldr (fn ((cmd, hndlr), m) => M.insert(m, cmd, hndlr)) M.empty

    val streamFromFile = (MLMinusLexer.streamifyInstream o TextIO.openIn)
    val streamFromString = (MLMinusLexer.streamifyInstream o TextIO.openString)

    val stream = ref (streamFromFile)
    val handlerMap = makeHandlerMap handlers

    (*  handleOpt : handle a single option by setting stream or parser
    *   appropriately.
    *
    *   Pre-condition:  oa = "--" ^ oa'.
    *)
    fun handleOpt (oa : string) : unit =
    let
    in
      case String.substring(oa, 2, String.size oa - 2) of
           "arg" => stream := streamFromString
         | _ => raise Usage
    end

    (*  handleOpts : handle all options by calling handleOpt o for each option o
    *   on the command line.
    *)
    fun handleOpts (optsargs : string list) : string list =
    let
    in
      case optsargs of
           [] => raise Usage
         | [arg] => [arg]
         | oa :: oas =>
             if String.isPrefix "--" oa then (handleOpt oa ; handleOpts oas)
             else optsargs
    end

    val cmd :: optsArgs = 
      case argv of
           [] => raise Usage
         | _ => argv

    val [arg] = handleOpts optsArgs

    val hndlr = 
      valOf(M.find(handlerMap, cmd))
      handle Option => raise Usage

  in
    BackTrace.monitor (fn () => ((hndlr (arg, !stream arg)) ; 0))
  end
  handle 
    (* Usage errors *)
      Usage => (print usage ; 1)

    (* I/O errors *)
    | e as IO.Io {name=name, function=_, cause=cause} => 
        (printnl (String.concatWith " " [
          "I/O error reading",
          name,
          "(",
          exnMessage cause,
          ")"
        ]) ; 1)

    (* User-code errors *)
    | Parse.NoParse =>
        (printnl "Cannot parse!" ; 1)
    | Parse.ExtraTokens s =>
        (printnls ["Got extra tokens after parse: ",
                   tokStreamToString 10 s] ; 1)
    | Type.EqTypeError =>
        (printnl "Equality type error." ; 1)
    | Type.TypeError =>
        (printnl "Type error." ; 1)
    | Type.InvalidProgram s =>
        (printnl ("Invalid program:  " ^ s) ; 1)

end
