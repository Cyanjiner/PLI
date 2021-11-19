(*  COMP 323 Project 5:  Compilation.
*  Lucas Eras Paiva & Jiner Zheng
*  N. Danner
*)

structure Compile =
struct

  structure TIO = TextIO

  (*  **********
  *   Debugging and printing.
  *   **********
  *)

  val debug = false ;

  fun dbg_print (s : string) : unit =
    if debug then print s else ()

  fun dbg_printnl (s : string) : unit =
    dbg_print (s ^ "\n")

  fun printnl (s : string) : unit =
    print(s ^ "\n")


  (*  **********
  *   Compiler environment.
  *
  *   This is just a start.  You can change it however you like, and you'll
  *   certainly need to add to it.
  *   **********
  *)

  structure CompEnv = struct

    type env = {
      (*  rho(x) = store location for identifier x.
      *)
      rho : int Env.env,

      (*  nextLoc is the next location that is available in the store.
      *)
      nextLoc : int
    }

    exception NotFound of string

    (*  empty = an empty environment.
    *)
    fun empty() : env =
      {
        rho=Env.empty,
        nextLoc=0
      }

    (*  get {ρ,...} x = ρ(x).
    *)
    fun get ({rho,...} : env) (x : Ast.ident) : int =
      Env.get(rho, x)

    (*  insert {ρ,...} x = ({ρ{x → l},...}, l), where l is an unused location.
    *
    *  Side-effect:  all fresh locations for ρ will be > l.
    *)
    fun insert
        ({rho,nextLoc} : env)
        (x : Ast.ident) : env*int =
    (
      {
        rho=Env.update(rho, x, nextLoc),
        nextLoc=nextLoc + 1
      },
      nextLoc
    )

    (*  toString ρ = a string representation of ρ.
    *)
    fun toString ({rho,...} : env) : string =
      ListFormat.fmt {
        init="{", sep=", ", final="}",
        fmt=fn(x, y) => String.concat [
          x,
          " → ",
          Int.toString y
        ]
      }
      (Env.listItemsi rho)

  end

  type compile_env = CompEnv.env



  (*  **********
  *   Output functions.
  *
  *   You might find a few functions like these useful.
  *   **********
  *)

  (*  emit s emits s ^ "\n" to outs.
  *)
  fun emit (outs : TIO.outstream) (s : string) : unit = 
    TextIO.output(outs, s ^ "\n") before TextIO.flushOut(outs)

  (*  emitNoNL s emits s to outs.
  *)
  fun emitNoNL (outs : TIO.outstream) (s : string) : unit = 
    TextIO.output(outs, s) before TextIO.flushOut(outs)

  fun makeLbl (l : string) =
    l ^ ":"

  fun makeComment (c : string) =
    "; " ^ c

  val makeLine : string list -> string =
    String.concatWith " "


  

  fun compileExp' (outs : TextIO.outstream) (e : Type.ann_exp) : unit =
    let

    (*  Compilation environment data.
    *)
    type comp_env = int Env.env
    val nextLoc : int ref = ref 0

    fun emitHeader() =
    (
      TextIO.output(outs, String.concatWith "\n" [
                                                   ".class C",
                                                   ".super java/lang/Object",
                                                   ""
                                                 ]) ;
      TextIO.flushOut(outs)
    )

    fun emitMain(body : string list) : unit =
    (
      TextIO.output(
        outs,
        String.concatWith "\n"
        [
          ".method public static main([Ljava/lang/String;)V", 
          ".limit stack 1000",
          ".limit locals 1000",
          ""
        ]
      ) ;
      TextIO.output(outs, String.concatWith "\n" body) ;
      TextIO.output(outs, "\n") ;
      TextIO.output(outs, "invokestatic CSupport/printInt(I)V\n") ;
      TextIO.output(outs, "return\n") ;
      TextIO.output(outs, ".end method\n") ;
      TextIO.flushOut(outs)
    )

    (*  compileExp e = p, where
    *  p |- <0, S, Σ> ->* <..., S.v, Σ'>, where e ↓ v.
    *)
    fun compileExp'' (rho : comp_env) (e : Type.ann_exp) : string list =
      case e of
           (Type.Ident x, Type.IntTy) =>
             [
               "iload " ^ Int.toString (Env.get(rho, x)) 
             ]
        |  (Type.Ident x, Type.RealTy) =>
             [
               "dload " ^ Int.toString (Env.get(rho, x)) 
             ]

             
        | (Type.Int n, _) => ["ldc " ^ Int.toString n]
        | (Type.Real x, _) => ["ldc2_w " ^ Real.toString x]
        | (Type.Bool true, _) => ["iconst_1"]
        | (Type.Bool false, _) => ["iconst_0"]
        | (Type.Char c,_) => ["ldc" ^ str(c)]
        | (Type.Str s, _) => ["ldc2_w" ^ s]

        (* Arithmetics *)

        | (Type.Plus((e0, Type.IntTy), (e1, Type.IntTy)),Type.IntTy) =>
             compileExp'' rho (e0, Type.IntTy) @ (* S -> S.n0 *)
             compileExp'' rho (e1, Type.IntTy) @ (* S.n0 -> S.n0.n1 *)
             ["iadd"] (* S.n0.n1 -> S.n0+n1 *)

        | (Type.Plus((e0, Type.RealTy), (e1, Type.RealTy)),Type.RealTy) =>
             compileExp'' rho (e0, Type.RealTy) @ (* S -> S.x0 *)
             compileExp'' rho (e1, Type.RealTy) @ (* S -> S.x0 *)
             ["dadd"] (* S.x0.x1 -> S.x0+x1 *)

        | (Type.Minus((e0, Type.IntTy), (e1, Type.IntTy)),Type.IntTy) =>
             compileExp'' rho (e0, Type.IntTy) @
             compileExp'' rho (e1, Type.IntTy) @ 
             ["isub"] (* S.0.n1 -> S.n0-n1 *)

        | (Type.Minus((e0, Type.RealTy), (e1, Type.RealTy)),Type.RealTy) =>
             compileExp'' rho (e0, Type.RealTy) @
             compileExp'' rho (e1, Type.RealTy) @
             ["dsub"] (* S.x0.x1 -> S.x0-x1 *)

        (* Intergers multiplcation *)
        | (Type.Times((e0, Type.IntTy), (e1, Type.IntTy)),Type.IntTy) =>
             compileExp'' rho (e0, Type.IntTy) @
             compileExp'' rho (e1, Type.IntTy) @
             ["imul"] (* S.n0.n1 -> S.n0*n1 *)

        | (Type.Times((e0, Type.RealTy), (e1, Type.RealTy)),Type.RealTy) =>
             compileExp'' rho (e0, Type.RealTy) @
             compileExp'' rho (e1, Type.RealTy) @
             ["dmul"] (* S.x0.x1 -> S.x0*x1 *)

        | (Type.Div((e0, Type.IntTy), (e1, Type.IntTy)),Type.IntTy) =>
             compileExp'' rho (e0, Type.IntTy) @
             compileExp'' rho (e1, Type.IntTy) @
             ["idiv"] (* S.n0.n1 -> S.n0 div n1 *)

        | (Type.Div((e0, Type.RealTy), (e1, Type.RealTy)),Type.RealTy) =>
             compileExp'' rho (e0, Type.RealTy) @
             compileExp'' rho (e1, Type.RealTy) @
             ["ddiv"] (* S.x0.x1 -> S.x0 div x1 *)

        | (Type.Mod((e0, Type.IntTy), (e1, Type.IntTy)),Type.IntTy) =>
             compileExp'' rho (e0, Type.IntTy) @
             compileExp'' rho (e1, Type.IntTy) @
             ["iMod"] (* S.n0.n1 -> S.n0 div n1 *)

        (* Number comparisons *)

        | (Type.Lt((e0,Type.IntTy), (e1, Type.IntTy)), Type.IntTy) =>
             compileExp'' rho (e0, Type.IntTy) @
             compileExp'' rho (e1, Type.IntTy) @
             ["if_icmpglt TRUE", "iconst_0"] @ 
             ["goto DONE", "TRUE:", "iconst_1", "DONE:", "nop"] (* S.n0.n1 -> S.n0 < n1 *)

        | (Type.Lt((e0,Type.RealTy), (e1, Type.RealTy)),RealTy) =>
             ["iconst_1"] @
             compileExp'' rho (e0, Type.RealTy) @
             compileExp'' rho (e1, Type.RealTy) @
             ["dcmpg", "iflt DONE", "pop", "iconst_0", "DONE:", "nop"] (* S.x0.x1 -> S.x0 < x1 *)

        | (Type.Gt((e0,Type.IntTy), (e1, Type.IntTy)),IntTy) =>
             compileExp'' rho (e0, Type.IntTy) @
             compileExp'' rho (e1, Type.IntTy) @
             ["if_icmpgt TRUE", "iconst_0", "goto DONE"] @ 
             ["TRUE:", "ldc 1", "DONE:", "nop"] (* S.n0.n1 -> S.n0 > n1 *)

        | (Type.Gt((e0,Type.RealTy), (e1, Type.RealTy)),RealTy) =>
             ["iconst_1"] @
             compileExp'' rho (e0, Type.RealTy) @
             compileExp'' rho (e1, Type.RealTy) @
             ["dcmpg", "ifgt DONE", "pop", "iconst_0", "DONE:", "nop"] (* S.x0.x1 -> S.x0 > x1 *)

        | (Type.Le((e0,Type.IntTy), (e1, Type.IntTy)),IntTy) =>
             compileExp'' rho (e0, Type.IntTy) @
             compileExp'' rho (e1, Type.IntTy) @
             ["if_icmple TRUE", "iconst_0", "goto DONE"] @ 
             ["TRUE:", "ldc 1", "DONE:", "nop"] (* S.n0.n1 -> S.n0 <= n1 *)

        | (Type.Le((e0,Type.RealTy), (e1, Type.RealTy)),RealTy) =>
             ["iconst_0"] @
             compileExp'' rho (e0, Type.RealTy) @
             compileExp'' rho (e1, Type.RealTy) @
             ["dcmpg", "ifgt DONE", "pop", "iconst_1", "DONE:", "nop"] (* S.x0.x1 -> S.x0 <= x1 *)

        | (Type.Ge((e0,Type.IntTy), (e1, Type.IntTy)),IntTy) =>
             compileExp'' rho (e0, Type.IntTy) @
             compileExp'' rho (e1, Type.IntTy) @
             ["if_icmpge TRUE", "iconst_0", "goto DONE"] @ 
             ["TRUE:", "ldc 1", "DONE:", "nop"] (* S.n0.n1 -> S.n0 >= n1 *)

        | (Type.Ge((e0,Type.RealTy), (e1, Type.RealTy)),RealTy) =>
             ["iconst_0"] @
             compileExp'' rho (e0, Type.RealTy) @
             compileExp'' rho (e1, Type.RealTy) @
             ["dcmpg", "iflt DONE", "pop", "iconst_1", "DONE:", "nop"] (* S.x0.x1 -> S.x0 >= x1 *)

        | (Type.Eq((e0,Type.IntTy), (e1, Type.IntTy)),IntTy) =>
             compileExp'' rho (e0, Type.IntTy) @
             compileExp'' rho (e1, Type.IntTy) @
             ["if_icmpeq TRUE", "iconst_0", "goto DONE"] @  
             ["TRUE:", "ldc 1", "DONE:", "nop"] (* S.n0.n1 -> S.n0 = n1 *)


        | (Type.Eq((e0,Type.RealTy), (e1, Type.RealTy)),RealTy) =>
             ["iconst_1"] @
             compileExp'' rho (e0, Type.RealTy) @
             compileExp'' rho (e1, Type.RealTy) @
             ["dcmpg", "ifeq DONE", "pop", "iconst_0", "DONE:", "nop"] (* S.x0.x1 -> S.x0 = x1 *)

        | (Type.Ne((e0,Type.IntTy), (e1, Type.IntTy)),IntTy) =>
             compileExp'' rho (e0, Type.IntTy) @
             compileExp'' rho (e1, Type.IntTy) @
             ["if_icmpne TRUE", "iconst_0", "goto DONE"] @  
             ["TRUE:", "ldc 1", "DONE:", "nop"] (* S.n0.n1 -> S.n0 >= n1 *)


        | (Type.Ne((e0,Type.RealTy), (e1, Type.RealTy)),RealTy) =>
             ["iconst_0"] @
             compileExp'' rho (e0, Type.RealTy) @
             compileExp'' rho (e1, Type.RealTy) @
             ["dcmpg", "ifeq DONE", "pop", "iconst_1", "DONE:", "nop"] (* S.x0.x1 -> S.x0 >= x1 *)

        (* orelse & andalso *)

        | (Type.Orelse(e0, e1), _) =>
             compileExp'' rho e0 @
             compileExp'' rho e1 @
             ["ior"]

        | (Type.Andalso(e0, e1), _) =>
             compileExp'' rho e0 @
             compileExp'' rho e1 @
             ["iand"]


 
    in
    (
      emitHeader() ;
      emitMain (compileExp'' Env.empty e)
    )
    end


  fun compileExp (outs : TIO.outstream) (e : Type.ann_exp) : unit =
  let
    val emit = emit outs
    val emitNoNL = emitNoNL outs
    val emitlines : string list -> unit = List.app emit
  in
    compileExp' outs e
  end



  fun compilePgm (outs : TIO.outstream) (Type.Program ds : Type.pgm) : unit =
  let
    val emit = emit outs
    val emitNoNL = emitNoNL outs
    val emitlines : string list -> unit = List.app emit
  in
    raise Fail "compilePgm"
  end

end
