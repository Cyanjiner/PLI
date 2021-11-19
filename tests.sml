(*  Tests for COMP 323 Project 4.
*
*   N. Danner
*)

structure Main =
struct

  structure U = UnitTest
  structure TR = TestRunner

  structure Ast = Ast
  structure Toks = MLMinusTokens

  structure Lex =
  struct
    type token = Toks.token

    type strm = MLMinusLexer.strm

    fun lex strm = 
      case MLMinusLexer.lex (AntlrStreamPos.mkSourcemap()) strm of
           (t, _, s) => (t, s)
  end
  structure Parse = ParseFn(Lex)

  structure T = TextIO

  val lex = Lex.lex

  (*  assertPgmParses pgmfile is a test that succeeds if the contents of pgmfile
  *  succesfully parse.  To successfully parse means that Parse.parsePgm returns
  *  a stream that consists only of the EOF token.
  *)
  fun assertPgmParses (pgmfile : string) : U.test =
  let
    val name = pgmfile

    fun test() : unit =
    let
      val strm = MLMinusLexer.streamifyInstream (TextIO.openIn pgmfile)
      val _ = Parse.parsePgm strm
    in
      ()
    end
  in
    U.doIt(name, test)
  end

  fun assertPgmParsesCorrectly (pgmfile : string, exp : Ast.pgm) : U.test =
  let
    val name = pgmfile

    fun test() : Ast.pgm =
    let
      val strm = MLMinusLexer.streamifyInstream (TextIO.openIn pgmfile)
    in
      Parse.parsePgm strm
    end
  in
    U.makeTestEq(name, test, exp, Ast.pgmEq, Ast.pgmToString)
  end

  fun assertPgmFailsParse (pgmfile : string) : U.test =
  let
    val name = pgmfile

    val dummyStream = MLMinusLexer.streamifyInstream (TextIO.openString "")

    fun test() : unit =
    let
      val strm = MLMinusLexer.streamifyInstream (TextIO.openIn pgmfile)
      val _ = Parse.parsePgm strm
    in
      ()
    end
  in
    U.orTest(pgmfile, [
      U.assertExn("NoParse", test, Parse.NoParse),
      U.assertExn("ExtraTokens", test, Parse.ExtraTokens dummyStream)
    ])
  end


  fun testExec (storeSize : int, enableGC : bool) (pgmfile : string) : U.test =
  let
    val name = pgmfile

    val pgmOutFile = pgmfile ^ ".output"
    val pgmExpFile = pgmfile ^ ".expected"

    (*  trimLines s = concatWith "\n" [s_0,...,s_{n-1}], where
    *     s = s_0' ^ "\n" ^ ... ^ "\n" ^ s_{n-1}'
    *     s_i = s_i' with leading and trailing whitespace removed.
    *)
    fun trimLines (s : string) : string =
    let
      val lines = Substring.fields (fn c => c = #"\n") (Substring.full s)
      val isSpace = fn c => c = #" "
    in
      Substring.concatWith "\n"
        (map ((Substring.dropr isSpace) o (Substring.dropl isSpace)) lines)
    end

    (* Read the contents of the expected output file.
    *)
    val expectedIn = TextIO.openIn pgmExpFile
    val expectedOutput = trimLines (TextIO.inputAll expectedIn)
    val () = TextIO.closeIn expectedIn

    fun test() : string =
    let
      val pgmIn = TextIO.openIn pgmfile
      val strm = MLMinusLexer.streamifyInstream pgmIn
      val p = Parse.parsePgm strm
      val () = TextIO.closeIn pgmIn

      (*  Get the underlying stream for terminal output.
      *)
      val stdOutSaveStream = TextIO.getOutstream TextIO.stdOut
      val stdErrSaveStream = TextIO.getOutstream TextIO.stdErr

      (*  Open an output file for execution.
      *)
      val pgmOut = TextIO.openOut pgmOutFile

      (*  Get underlying stream for the output file.
      *)
      val pgmOutStream = TextIO.getOutstream pgmOut

      (*  Set the underlying stream for stdOut to the file.
      *)
      val () = TextIO.setOutstream (TextIO.stdOut, pgmOutStream)
      val () = TextIO.setOutstream (TextIO.stdErr, pgmOutStream)

      (*  Execute the program; output will go to the file instead of the
      *  terminal.
      *)
      val () = CEKInterp.Store.makeStore(storeSize)
      val () = CEKInterp.enableGC := enableGC
      val () = CEKInterp.execPgm p
               handle e => TextIO.output (
                             TextIO.stdErr, 
                             (String.concatWith "\n" 
                                (SMLofNJ.exnHistory e)^"\n")
                           )

      (*  Restore the underlying stream for stdOut to terminal output.
      *)
      val () = TextIO.flushOut TextIO.stdOut
      val () = TextIO.flushOut TextIO.stdErr
      val () = TextIO.setOutstream (TextIO.stdOut, stdOutSaveStream)
      val () = TextIO.setOutstream (TextIO.stdErr, stdErrSaveStream)

      (*  Close the output file.
      *)
      val () = TextIO.closeOut pgmOut

      (* Read the contents of the output file.
      *)
      val outputIn = TextIO.openIn pgmOutFile
      val pgmOutput = trimLines (TextIO.inputAll outputIn)
      val () = TextIO.closeIn outputIn
    in
      pgmOutput
    end

  in
    U.assertEq(name, test, expectedOutput, String.toString)
  end

  (*  checkCompilePgm f = t, where t is a test that succeeds if 
  *   Interp.exec p produces the output in f ^ ".output" when it is
  *   given input  in f ^ ".input".  
  *
  *   Side-effect:  output of p is in f ^ ".results".
  *
  *   See assignment description for details.
  *)
  fun testCompile (filename : string) : U.test =
  let
    val javadir = "java"
    val jasminJar = OS.Path.joinDirFile {dir=javadir, file="jasmin.jar"}
    val pgmfile = filename
    val fileBase = OS.Path.base filename
    val jFile = OS.Path.joinBaseExt {base=fileBase, ext=SOME "j"}

    val fileOut = filename ^ ".results"
    val fileExp = filename ^ ".expected"
    val fileErr = filename ^ ".errors"

    fun readFile(filename : string) : string =
    let
      val ins = T.openIn filename
      val s = Substring.string (
        Substring.dropr Char.isSpace (Substring.full (T.inputAll ins))
      )
      val () = T.closeIn ins
    in
      s
    end

    fun testCompile() : unit =
    let
      val outs = T.openOut jFile

      val pgmIn = TextIO.openIn pgmfile
      val strm = MLMinusLexer.streamifyInstream pgmIn
      val p = Parse.parsePgm strm
      val () = TextIO.closeIn pgmIn
    in
      (
        Compile.compilePgm outs (Type.checkPgm p) ;
        T.closeOut outs
      )
    end

    fun testAssm() : int =
    let
      val assembleCmd = String.concatWith " " [
        "java -jar " ^ jasminJar,
        "-d",
        javadir,
        jFile,
        " >/dev/null",
        " 2>",
        fileErr
      ]
    in
      OS.Process.system assembleCmd
    end

    fun testExecute() : string =
    let

      val runCmd = String.concatWith " " [
        "java -classpath",
        javadir,
        "C",
        ">",
        fileOut
      ]
      val _ = OS.Process.system runCmd

      val res = readFile fileOut
    in
      res
    end

    val exp = readFile fileExp
  in
    U.seqTest (filename, [
      U.doIt (filename ^ "(compiles)", testCompile),
      U.assertEqInt (filename ^ "(assembles)", testAssm, 0),
      U.assertEqStr (filename ^ "(executes correctly)", testExecute, exp)
    ])
  end


  val testfilesDir = "testfiles"

  (*  smlFiles dir = the list of sml files in dir.  Each file is a string of the
  *  form dir/f.sml.
  *)
  fun smlFiles (dir : string) : string list =
  let
    fun getSMLFiles (ds : OS.FileSys.dirstream) : string list =
      case OS.FileSys.readDir ds of
           NONE => []
         | SOME f =>
             case OS.Path.ext f of
                  SOME "sml" => f :: getSMLFiles ds
                | _ => getSMLFiles ds

    val dir = testfilesDir ^ "/" ^ dir
    val ds = OS.FileSys.openDir dir
  in
    map 
      (fn f => dir ^ "/" ^ f) 
      (ListMergeSort.sort op>= (getSMLFiles ds))
    before OS.FileSys.closeDir ds
  end

  fun smlFilesExpected (dir : string) : string list =
    List.filter 
      (fn f => OS.FileSys.access (f ^ ".expected", [OS.FileSys.A_READ])) 
      (smlFiles dir)


  fun all_tests() = [
    ("parseable/typeable/synth",
      map testCompile (smlFilesExpected "parseable/typeable/synth")),
    ("parseable/typeable/ranta",
      map testCompile (smlFilesExpected "parseable/typeable/ranta")),
    ("parseable/typeable/paulson",
      map testCompile (smlFilesExpected "parseable/typeable/paulson")),
    ("parseable/typeable/imperative/synth",
      map testCompile (smlFilesExpected "parseable/typeable/imperative/synth")),
    ("parseable/typeable/imperative/ranta",
      map testCompile (smlFilesExpected "parseable/typeable/imperative/paulson"))
  ]

  fun main(arg0 : string, argv : string list) : int =
    BackTrace.monitor(
      fn () => (TR.runTimedTestSuites (all_tests(), 30, true) ; 0))


end
