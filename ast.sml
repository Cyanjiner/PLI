(* COMP 323:  Abstract syntax for ML-.
*
* N. Danner
*
*)
structure Ast =
struct

  type ident = string

  structure IdentKey : ORD_KEY =
  struct
    type ord_key = ident
    val compare = String.compare
  end

  datatype exp = Ident of ident | Int of int | Real of real
               | Char of char | Str of string | Bool of bool 
               | Triv
               | Plus of exp*exp | Minus of exp*exp | Times of exp*exp 
               | Div of exp*exp | Slash of exp*exp | Mod of exp*exp 
               | Lt of exp*exp | Le of exp*exp 
               | Gt of exp*exp | Ge of exp*exp 
               | Eq of exp*exp | Ne of exp*exp 
               | Orelse of exp*exp | Andalso of exp*exp 
               | Cat of exp*exp | Cond of exp*exp*exp 
               | Sel of int | Tuple of exp list 
               | Nil | Cons of exp*exp | Append of exp*exp 
               | App of exp*exp | Lambda of ident*exp | Let of (dec list)*exp
               | Assign of exp*exp | Seq of exp list | While of exp*exp
               | Null

  (*  The type of program declarations.
  *)
  and dec = ValDec of ident*exp 
               | DoDec of exp
               | FunDec of ident*(ident list)*exp

  (*  The type of program statements.
  *)
  datatype stm = Dec of dec
               | ExprStm of exp

  (*  The type of programs.
  *)
  datatype pgm = Program of (stm list)

    
  (* expToString : t -> string
  *  expToString e is the string representation of ASTs. 
  *)
  local
    fun wrap s = concat ["(", s, ")"]
  in
    fun binop s e1 e2 = concat [expToString e1, s, expToString e2]
    and expToString(Ident(x)) = x
      | expToString(Int n) = Int.toString n
      | expToString(Real n) = Real.toString n
      | expToString(Char c) = Char.toString c
      | expToString(Str s) = concat ["\"", s, "\""]
      | expToString(Bool b) = Bool.toString b
      | expToString(Triv) = "(_)"
      | expToString(Plus(e1, e2)) =
          concat ["(", expToString e1, " + ", expToString e2, ")"]
      | expToString(Minus(e1, e2)) =
          concat ["(", expToString e1, " - ", expToString e2, ")"]
      | expToString(Times(e1, e2)) =
          concat ["(", expToString e1, "*", expToString e2, ")"]
      | expToString(Div(e1, e2)) =
          concat ["(", expToString e1, " div ", expToString e2, ")"]
      | expToString(Slash(e1, e2)) =
          concat ["(", expToString e1, "/", expToString e2, ")"]
      | expToString(Mod(e1, e2)) =
          concat ["(", expToString e1, " mod ", expToString e2, ")"]
      | expToString(Eq(e1, e2)) = wrap (binop "=" e1 e2)
      | expToString(Ne(e1, e2)) = wrap (binop "<>" e1 e2)
      | expToString(Lt(e1, e2)) = wrap (binop "<" e1 e2)
      | expToString(Le(e1, e2)) = wrap (binop "<=" e1 e2)
      | expToString(Gt(e1, e2)) = wrap (binop ">" e1 e2)
      | expToString(Ge(e1, e2)) = wrap (binop ">=" e1 e2)
      | expToString(Orelse(e1, e2)) =
          concat ["(", expToString e1, " orelse ", expToString e2, ")"]
      | expToString(Andalso(e1, e2)) =
          concat ["(", expToString e1, " andalso ", expToString e2, ")"]
      | expToString(Cat(e1, e2)) =
          concat ["(", expToString e1, "^", expToString e2, ")"]
      | expToString(Cond(e1, e2, e3)) =
          String.concatWith " " 
          ["if", expToString e1, "then", expToString e2, 
                                 "else", expToString e3, "fi"]
      | expToString(Sel(n)) = 
          concat ["#", Int.toString n]
      | expToString(Tuple es) = 
          ListFormat.fmt {init="(", final=")", sep=", ", fmt=expToString} es
      | expToString(Nil) = "nil"
      | expToString(Cons(e1, e2)) = wrap (binop "::" e1 e2)
      | expToString(Append(e1, e2)) = wrap (binop "@" e1 e2)
      | expToString(App(rator, rand)) =
          concat ["(", expToString rator, "@@", expToString rand, ")"]
      | expToString(Lambda(x, e)) =
          concat ["( fn ", x, " => ", expToString e, ")"]
      | expToString(Let(decs, e2)) =
          concat ["( let ", ListFormat.listToString declToString decs, 
                  " in ", expToString e2, 
                  " end)"]
      | expToString(Assign(e', e)) =
          concat ["(", expToString e', " := ", expToString e, ")"]
      | expToString(Seq es) =
          ListFormat.fmt {init="(", final=")", sep="; ", fmt=expToString} es
      | expToString(While(e', e)) =
          concat ["while ", expToString e', " do ", expToString e, " end"]
      | expToString(Null) = "NULL"

    (*  declToString d = s, where s is a string representation of the
    *   declaration d.
    *)
    and declToString (ValDec(x, e)) =
          String.concatWith " " ["val", x, "=", expToString e]
      | declToString (DoDec e) =
          String.concatWith " " ["val _ =", expToString e]
      | declToString (FunDec(f, ps, e)) =
          String.concatWith " " ["fun", f, String.concatWith " " ps, "=", 
                                 expToString e]
  end

  (*  stmToString stm = s, where s is a string representation of stm.
  *)
  fun stmToString (stm : stm) : string =
    case stm of
         Dec d => (declToString d) ^ " ;"
       | ExprStm e => (expToString e) ^ " ;"


  (*  toString pgm = s, where s is a string representation of the program pgm.
  *)
  fun pgmToString (Program(stms)) : string =
    String.concatWith "\n" (map stmToString stms)

  (* ****************************************
  *  EQUALITY TESTING
  *
  *  We need our own equality tests because of Real of real.
  *  ****************************************
  *)

  fun expEq(e, e') =
    case (e, e') of
         (Ident x, Ident x') => x = x'
       | (Int n, Int n') => n = n'
       | (Real x, Real x') => Real.==(x, x')
       | (Char c, Char c') => c = c'
       | (Str s, Str s') => s = s'
       | (Bool b, Bool b') => b = b'
       | (Triv, Triv) => true
       | ((Plus(e0, e1), Plus(e0', e1'))
         |(Minus(e0, e1), Minus(e0', e1'))
         |(Times(e0, e1), Times(e0', e1'))
         |(Div(e0, e1), Div(e0', e1'))
         |(Slash(e0, e1), Slash(e0', e1'))
         |(Mod(e0, e1), Mod(e0', e1'))
         |(Lt(e0, e1), Lt(e0', e1'))
         |(Le(e0, e1), Le(e0', e1'))
         |(Gt(e0, e1), Gt(e0', e1'))
         |(Ge(e0, e1), Ge(e0', e1'))
         |(Eq(e0, e1), Eq(e0', e1'))
         |(Ne(e0, e1), Ne(e0', e1'))
         |(Orelse(e0, e1), Orelse(e0', e1'))
         |(Andalso(e0, e1), Andalso(e0', e1'))
         |(Cat(e0, e1), Cat(e0', e1'))
         |(Cons(e0, e1), Cons(e0', e1'))
         |(Append(e0, e1), Append(e0', e1'))
         |(App(e0, e1), App(e0', e1'))
         |(Assign(e0, e1), Assign(e0', e1'))
         |(While(e0, e1), While(e0', e1'))) =>
             expEq(e0, e0') andalso expEq(e1, e1')
       | (Cond(e, e0, e1), Cond(e', e0', e1')) =>
           expEq(e, e') andalso expEq(e0, e0') andalso expEq(e1, e1')
       | (Sel(n), Sel(n')) => n = n'
       | (Tuple es, Tuple es') => ListPair.all expEq (es, es')
       | (Nil, Nil) => true
       | (Lambda(x, e), Lambda(x', e')) => x = x' andalso expEq(e, e')
       | (Let(ds, e), Let(ds', e')) => 
           ListPair.all decEq (ds, ds') andalso expEq(e, e')
       | (Seq es, Seq es') => ListPair.all expEq (es, es')
       | _ => false

  and decEq(d, d') =
    case (d, d') of
         (ValDec(x, e), ValDec(x', e')) => x = x' andalso expEq(e, e')
       | (DoDec(e), DoDec(e')) => expEq(e, e')
       | (FunDec(x, ps, e), FunDec(x', ps', e')) =>
           x = x' andalso ps = ps' andalso expEq(e, e')

  fun stmEq(s, s') =
    case (s, s') of
         (Dec d, Dec d') => decEq(d, d')
       | (ExprStm e, ExprStm e') => expEq(e, e')
       | _ => false

  fun pgmEq(Program ss, Program ss') =
    ListPair.all stmEq (ss, ss')

end
