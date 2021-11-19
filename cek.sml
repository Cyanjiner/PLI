(*  COMP 323 Project 4:  CEK machine interpreter for ML-.
*
*  N. Danner
*)

structure CEKInterp : INTERP =
struct

  val enableGC : bool ref = ref true

  (* ********************
  *  Debugging.
  *  ********************
  *)
  val debug = false ;

  fun dbg_print (s : unit -> string) : unit =
    if debug then print (s()) else ()

  fun dbg_printnl (s : unit -> string) : unit =
    dbg_print (fn () => s() ^ "\n")

  (* ********************
  *  Environments.  We'll use ORD_MAPs.
  *  ********************
  *)

  structure Env = SplayMapFn(
    struct 
      type ord_key = Ast.ident 
      val compare = String.compare 
    end)

  type 'a env = 'a Env. map

  exception NotFound of string

  fun get (rho : 'a env) (x : Ast.ident) : 'a =
    valOf(Env.find(rho, x))
    handle Option => raise NotFound x

  fun update (rho : 'a env) (x : Ast.ident) (y : 'a) : 'a env =
    Env.insert(rho, x, y)

  fun updateMany (rho : 'a env) (kvs : (Ast.ident*'a) list) : 'a env =
    foldl Env.insert' rho kvs

  (* ********************
  *  Values.  Most are self-explanatory.
  *
  *  RecClosure(f, [x_k,...,x_{n-1}], e, rho, [x_0,...,x_{k-1}])
  *  represents the (possibly) recursive function f x_0 ... x_{n-1} that has
  *  been partially applied to arguments for x_0,...,x_{k-1}.
  *
  *  Builtin id represents the built-in function id.  Each built-in function
  *  is associated to a function that maps values to values, specified by the
  *  baseEnv environment.
  *  ********************
  *)
  datatype value = Int of int | Real of real | Char of char | Str of string
                 | Bool of bool | Triv
                 | Tuple of value list | List of value list
                 | Closure of Ast.ident*Ast.exp*value env
                 | RecClosure of Ast.ident*(Ast.ident list)*Ast.exp*value env*
                                  (Ast.ident list)
                 | Sel of int
                 | Builtin of Ast.ident
                 | Location of int

  (* ********************
  *  The store.
  *  ********************
  *
  *  The store depends on the type of values, so must be defined after that
  *  type.
  *
  *  We implement the store as a fixed size array with an int free list to
  *  record the available locations.
  *
  *  Note that Store.store is effectively a global variable for the entire
  *  interpreter, but the interpreter should not use it directly.  Instead, the
  *  interpreter should only call functions implemented in this structure, which
  *  in turn access/modify/use the store.
  *)
  structure Store =
  struct

    (*  Raised when there is no available location.
    *)
    exception OutOfMemory

    (*  The size of the default store.
    *)
    val DEFAULT_STORE_SIZE : int = 1000

    (*  The store is a fixed-size array initialized to all 0s.
    *)
    val store : value Array.array ref = 
      ref(Array.array(DEFAULT_STORE_SIZE, Int 0))

    (*  Free list:  available store locations.
    *)
    val freelist : int list ref = 
      ref(List.tabulate(DEFAULT_STORE_SIZE, fn i => i))

    (*  makeStore n = ()
    *
    *  Side-effect:  a store is created of size n, with all locations free.
    *)
    fun makeStore(size : int) : unit =
    (
      store := Array.array(size, Int 0) ;
      freelist := List.tabulate(size, fn i => i)
    )

    (*  size() = the size of the store.
    *)
    fun size() : int =
      Array.length(!store)

    (*  nextLoc() = a free location in the store.
    *
    *  Side-effect:  nextLoc() is no longer free.
    *)
    fun nextLoc() : int =
    let
      val () = 
        dbg_printnl(fn () => "Store.nextLoc(): freelist = " ^
                             ListFormat.listToString Int.toString (!freelist))
    in
      case !freelist of
           [] => raise OutOfMemory
         | l :: ls => 
             l before freelist := ls
    end

    (*  alloc v = loc, where loc is the next available location in the store.
    *
    *  Side-effect:  store[loc] = v.
    *)
    fun alloc(v : value) : int =
    let
      val l = nextLoc()
      val () = 
        dbg_printnl(fn () => "Store.alloc: allocating " ^ Int.toString l)
      val () = Array.update(!store, l, v)
    in
      l
    end

    (*  update(loc, v) = ()
    *
    *  Side-effect:  store[loc] = v
    *)
    fun update(loc : int, v : value) : unit =
      Array.update(!store, loc, v)

    (*  get(loc) = v, where v is the value at location loc.
    *)
    fun get(loc : int) : value =
      Array.sub(!store, loc)

    (*  free loc = ().
    *
    *  Side-effect:  loc is free.
    *)
    fun free(loc : int) : unit =
      freelist := loc :: !freelist

  end

  (*  valueToString v = a string representation of v.
  *)
  fun valueToString (v : value) : string =
    case v of
         Int n => Int.toString n
       | Real x => Real.toString x
       | Char c => "#\"" ^ Char.toString c ^ "\""
       | Str s => "\"" ^ String.toString s ^ "\""
       | Bool b => Bool.toString b
       | Triv => "()"
       | Tuple vs => 
           ListFormat.fmt {init="(", final=")", sep=",", fmt=valueToString} vs
       | List vs =>
           ListFormat.listToString valueToString vs
       | Closure(x, _, _) => 
           String.concat [
             "(fn ",
             x,
             " => ...){...}"
           ]
       | RecClosure(f, xs, _, _, _) =>
           String.concat [
             "(recfn ",
             ListFormat.fmt 
               {init="", final="", sep=" ", fmt=String.toString}
               xs,
             " => ...)"
           ]
       | Sel n => "#" ^ (Int.toString n)
       | Builtin id => id
       | Location ~1 => "NULL"
       | Location l => "ref " 
                       ^ "[" ^ Int.toString l ^ "]"
                       ^ valueToString (Store.get l)

  (* ********************
  *  Equality testing.
  *  ********************
  *)

  (*  Exception raised when testing equality of two values that are not of
  *  equality type.  Really, when the two values are not
  *  "equality-testable," which means that they are both Int, Char, Str,
  *  Bool, Loc, or they are Tuple of List values of equality-testable
  *  values.
  *)
  exception NotEquality of value*value

  (*  equal(v0, v1) = true,  if v0 and v1 represent the same value,
  *                 = false, otherwise.
  *   Raises NotEquality if v0 and v1 are not equality-testable.
  *)
  fun equal (v0 : value, v1 : value) : bool =
  let 
    val () = dbg_printnl(fn () => valueToString v0 ^ " = " ^ valueToString v1)
  in
    case (v0, v1) of
         (Int n0, Int n1) => n0 = n1
       | (Char c0, Char c1) => c0 = c1
       | (Str s0, Str s1) => s0 = s1
       | (Bool b0, Bool b1) => b0 = b1
       | (Tuple vs0, Tuple vs1) => ListPair.allEq equal (vs0, vs1)
       | (List vs0, List vs1) => ListPair.allEq equal (vs0, vs1)
       | (Location l0, Location l1) => l0 = l1
       | _ => raise (NotEquality(v0, v1))
  end

  (* ********************
  *  Control strings, continuations, and state.
  * ********************
  *)

  type exp = Ast.exp

  (*  A closure is an expression e along with an environment that binds the
  *  free variables of e.
  *)
  type closure = exp*value env

  (*  A control string for the CEK machine is either a closure or a value.
  *)
  datatype ctrl = C of closure | V of value

  (*  Arithmetic operations for the KArithOp continuations.
  *)
  datatype arith_op = AOPlus
                    | AOMinus
                    | AOTimes
                    | AODiv
                    | AOMod

  (*  Relational operations for the KRel continuations.
  *)
  datatype rel_op = ROLt
                  | ROLe
                  | ROGt
                  | ROGe

  (*  Continuations.
  *)
  datatype cont = KArithOp1 of closure*arith_op
                | KArithOp2 of value*arith_op
                | KRel1 of closure*rel_op
                | KRel2 of value*rel_op
                | KEq1 of closure | KEq2 of value
                | KNeq1 of closure | KNeq2 of value
                | KCons1 of closure | KCons2 of value
                | KAppend1 of closure | KAppend2 of value
                | KCat1 of closure | KCat2 of value
                | KOr of closure | KAnd of closure 
                | KCond of exp*exp*value env
                | KApp1 of closure | KApp2 of value
                | KTuple of (value list)*(exp list)*(value env)
                | KList of (value list)*(exp list)*(value env)
                | KLet of Ast.ident*(Ast.dec list)*exp*value env
                | KLetVal of Ast.ident option*(Ast.dec list)*exp*value env
                | KAssign1 of closure | KAssign2 of value
                | KSeq of exp list*value env
                | KWhile1 of exp*exp*value env | KWhile2 of exp*exp*value env

  (*  The state of the CEK machine is a control string and a continuation
  *  stack.
  *)
  type state = ctrl*(cont list)

  (*  stateToString s = a string representation of s.
  *)
  fun stateToString (s : state) : string =
    case s of
         (C(e, _), _) => (Ast.expToString e) ^ "{...}\n"
       | (V v, _) => "--> " ^ (valueToString v) ^ "\n"

  (* ******************** 
  *  Garbage collection functions.
  *  ********************
  *)

  (*  Structure for sets of locations, used by the garbage collector.
  *)
  structure LocationSet = SplaySetFn(
    struct type ord_key = int val compare = Int.compare end
  )

  (*  valueToLocs v = the locations directly referenced by v.
  *)
  fun valueToLocs (v : value) : int list =
  let
    val () =
      dbg_printnl(fn () => "valueToLocs " ^ valueToString v)
  in
    case v of
         Tuple vs => List.concat (map valueToLocs vs)
       | List vs => List.concat (map valueToLocs vs)
       | Closure(_, _, rho) => envToLocs rho
       | RecClosure(_, _, _, rho, _) => envToLocs rho
       | Location loc => if loc = ~1 then [] else [loc]
       | _ => []
  end

  and envToLocs (rho : value env) : int list =
    List.concat (map valueToLocs (Env.listItems rho))

  (*  contsToLocs ks = locations directly referenced by values in ranges of
  *  environments in ks.
  *)
  fun contsToLocs (ks : cont list) : int list =
    case ks of
         [] => []
       | ( KArithOp1((_, rho), _) |
           KRel1((_, rho), _) |
           KEq1((_, rho)) |
           KNeq1((_, rho)) |
           KCons1((_, rho)) |
           KAppend1((_, rho)) |
           KCat1((_, rho)) |
           KOr((_, rho)) |
           KAnd((_, rho)) |
           KCond(_, _, rho) |
           KApp1((_, rho)) |
           KAssign1((_, rho)) |
           KLet(_, _, _, rho) |
           KLetVal(_, _, _, rho) |
           KSeq(_, rho) |
           KWhile1(_, _, rho) | 
           KWhile2(_, _, rho) ) :: ks => 
             List.concat (map valueToLocs (Env.listItems rho)) @ contsToLocs ks
       | ( KArithOp2(v, _) |
           KRel2(v, _) |
           KEq2 v |
           KNeq2 v |
           KCons2 v |
           KAppend2 v |
           KCat2 v |
           KApp2 v |
           KAssign2 v) :: ks => valueToLocs v @ contsToLocs ks
       | ( KTuple(vs, _, rho) |
           KList(vs, _, rho)) :: ks =>
             List.concat (map valueToLocs vs) @ envToLocs rho @ contsToLocs ks

  (*  mark q s = the set of locations not in s that are reachable from the
  *  locations in q.
  *)
  fun mark 
      (q : int Fifo.fifo, s : LocationSet.set) : LocationSet.set =
    if Fifo.isEmpty q then s
    else
    let
      val (q', l) = Fifo.dequeue q
      val () = dbg_printnl (fn () => "GC:  marked location " ^ Int.toString l)
      val s' = LocationSet.add(s, l)
      val ls = 
        List.filter 
          (fn l => not (LocationSet.member(s, l)))
          (valueToLocs (Store.get l))
      val q'' = foldr (fn (l, q) => Fifo.enqueue(q, l)) q' ls
    in
      mark (q'', s')
    end

  (*  sweep marked = ()
  *
  *  Side-effect:  if 0 <= i < STORE_SIZE and i is not in marked, then i is
  *  added to the free list.
  *)
  fun sweep(marked : LocationSet.set) : unit =
  let
    val i = ref 0
  in
    while !i < Store.size() do 
      if not (LocationSet.member(marked, !i)) then
        (Store.free (!i) ; i := !i + 1)
      else
        i := !i + 1
  end

  fun gc(locs : int list) : unit =
    if !enableGC then
      let
        val () = 
          dbg_printnl(fn () => 
            "*** gc " ^ ListFormat.listToString Int.toString locs
          )
        val initQ = 
          foldl (fn (l, q) => Fifo.enqueue(q, l)) (Fifo.empty) locs
      in
        sweep(mark(initQ, LocationSet.empty))
      end
    else
      ()

  (*  allocateRef v = l, where l is a fresh location.
  *
  *  Try to allocate with Store.alloc, run the garbage collector if it raises
  *  OutOfMemory.
  *)
  fun allocateRef (v : value, ks : cont list) : int =
    Store.alloc v
    handle Store.OutOfMemory => 
             (gc(valueToLocs v @ contsToLocs ks) ; Store.alloc v)

  (*  The base environment of built-in functions.  The parser considers these
  *  ordinary identifiers, but we know better...
  *)
  val baseEnv : (value * cont list -> value) env = updateMany Env.empty [
    ("printInt", fn (Int n, _) => 
      ( 
        print ((String.translate 
                (fn #"~" => "-" | c => Char.toString c)
                (Int.toString n)) ^ "\n") ; 
        Triv 
      )
    ) ,
    ("printReal", fn (Real x, _) => 
      ( 
        print ((String.translate 
                (fn #"~" => "-" | c => Char.toString c)
                (Real.toString x)) ^ "\n") ; 
        Triv 
      )
    ) ,
    ("printBool", fn (Bool b, _) => ( print (Bool.toString b ^ "\n") ; Triv )) ,
    ("hd", fn (List (x :: xs), _) => x),
    ("tl", fn (List (x :: xs), _) => List xs),
    ("null", fn (List xs, _) => Bool(null xs)),
    ("not", fn (Bool b, _) => Bool(not b)),
    ("real", fn (Int n, _) => Real(real n)),
    ("length", fn (List xs, _) => Int(length xs)),
    ("implode", fn (List cs, _) => Str(implode (map (fn (Char c) => c) cs))),
    ("explode", fn (Str s, _) => List(map Char (explode s))),
    ("ref", fn (v, ks) => Location(allocateRef (v, ks))),
    ("!", fn (Location l, _) => Store.get l),
    ("free", fn (Location l, _) => Triv before Store.free l)
  ]

  (* trans1 s = s', where s' is a one-step transition from s.
  *)
  fun trans1 (s : state) : state =
  let
    val () = dbg_printnl (fn () => stateToString s)
  in
    case s of

       (*  **********
       *   Arithmetic operators.
       *   **********
       *)

       (*  Initial closures.
       *)
         (C(Ast.Plus(e0, e1), rho), ks) =>
           (C(e0, rho), KArithOp1((e1, rho), AOPlus) :: ks)

       | (C(Ast.Minus(e0, e1), rho), ks) =>
           (C(e0, rho), KArithOp1((e1, rho), AOMinus) :: ks)

       | (C(Ast.Times(e0, e1), rho), ks) =>
           (C(e0, rho), KArithOp1((e1, rho), AOTimes) :: ks)

       | (C(Ast.Div(e0, e1), rho), ks) =>
           (C(e0, rho), KArithOp1((e1, rho), AODiv) :: ks)

       | (C(Ast.Slash(e0, e1), rho), ks) =>
           (C(e0, rho), KArithOp1((e1, rho), AODiv) :: ks)

       | (C(Ast.Mod(e0, e1), rho), ks) =>
           (C(e0, rho), KArithOp1((e1, rho), AOMod) :: ks)

       (*  Left operand computed.
       *)
       | (V v, KArithOp1((e, rho), rator) :: ks) =>
           (C(e, rho), KArithOp2(v, rator) :: ks)

       (*  Right operand computed.
       *)
       | (V(Int n), KArithOp2(Int m, AOPlus) :: ks) =>
           (V(Int(m + n)), ks)
       | (V(Real n), KArithOp2(Real m, AOPlus) :: ks) =>
           (V(Real(m + n)), ks)

       | (V(Int n), KArithOp2(Int m, AOMinus) :: ks) =>
           (V(Int(m - n)), ks)
       | (V(Real n), KArithOp2(Real m, AOMinus) :: ks) =>
           (V(Real(m - n)), ks)

       | (V(Int n), KArithOp2(Int m, AOTimes) :: ks) =>
           (V(Int(m * n)), ks)
       | (V(Real n), KArithOp2(Real m, AOTimes) :: ks) =>
           (V(Real(m * n)), ks)

       | (V(Int n), KArithOp2(Int m, AODiv) :: ks) =>
           (V(Int(m div n)), ks)
       | (V(Real n), KArithOp2(Real m, AODiv) :: ks) =>
           (V(Real(m / n)), ks)

       | (V(Int n), KArithOp2(Int m, AOMod) :: ks) =>
           (V(Int(m mod n)), ks)

       (*  **********
       *   Relational operations.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Lt(e0, e1), rho), ks) =>
           (C(e0, rho), KRel1((e1, rho), ROLt) :: ks)
       | (C(Ast.Le(e0, e1), rho), ks) =>
           (C(e0, rho), KRel1((e1, rho), ROLe) :: ks)
       | (C(Ast.Gt(e0, e1), rho), ks) =>
           (C(e0, rho), KRel1((e1, rho), ROGt) :: ks)
       | (C(Ast.Ge(e0, e1), rho), ks) =>
           (C(e0, rho), KRel1((e1, rho), ROGe) :: ks)

       (*  Left operand computed.
       *)
       | (V v, KRel1(cl, rator) :: ks) =>
           (C cl, KRel2(v, rator) :: ks)

       (*  Right operand computed.
       *)
       | (V(Int n), KRel2(Int m, ROLt) :: ks) =>
           (V(Bool(m < n)), ks)
       | (V(Real n), KRel2(Real m, ROLt) :: ks) =>
           (V(Bool(m < n)), ks)
       | (V(Char n), KRel2(Char m, ROLt) :: ks) =>
           (V(Bool(m < n)), ks)
       | (V(Str n), KRel2(Str m, ROLt) :: ks) =>
           (V(Bool(m < n)), ks)

       | (V(Int n), KRel2(Int m, ROLe) :: ks) =>
           (V(Bool(m <= n)), ks)
       | (V(Real n), KRel2(Real m, ROLe) :: ks) =>
           (V(Bool(m <= n)), ks)
       | (V(Char n), KRel2(Char m, ROLe) :: ks) =>
           (V(Bool(m <= n)), ks)
       | (V(Str n), KRel2(Str m, ROLe) :: ks) =>
           (V(Bool(m <= n)), ks)

       | (V(Int n), KRel2(Int m, ROGt) :: ks) =>
           (V(Bool(m > n)), ks)
       | (V(Real n), KRel2(Real m, ROGt) :: ks) =>
           (V(Bool(m > n)), ks)
       | (V(Char n), KRel2(Char m, ROGt) :: ks) =>
           (V(Bool(m > n)), ks)
       | (V(Str n), KRel2(Str m, ROGt) :: ks) =>
           (V(Bool(m > n)), ks)

       | (V(Int n), KRel2(Int m, ROGe) :: ks) =>
           (V(Bool(m >= n)), ks)
       | (V(Real n), KRel2(Real m, ROGe) :: ks) =>
           (V(Bool(m >= n)), ks)
       | (V(Char n), KRel2(Char m, ROGe) :: ks) =>
           (V(Bool(m >= n)), ks)
       | (V(Str n), KRel2(Str m, ROGe) :: ks) =>
           (V(Bool(m >= n)), ks)

       (*  **********
       *   Equality tests.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Eq(e0, e1), rho), ks) =>
           (C(e0, rho), KEq1 (e1, rho) :: ks)

       (*  Left operand computed.
       *)
       | (V v, KEq1((e, rho)) :: ks) =>
           (C(e, rho), KEq2 v :: ks)

       (*  Right operand computed.
       *)
       | (V v1, KEq2 v0 :: ks) =>
           (V(Bool(equal(v0, v1))), ks)

       (*  **********
       *   Inequality tests.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Ne(e0, e1), rho), ks) =>
           (C(e0, rho), KNeq1(e1, rho) :: ks)

       (*  Left operand computed.
       *)
       | (V v, KNeq1 cl :: ks) =>
           (C cl, KNeq2 v :: ks)

       (*  Right operand computed.
       *)
       | (V v1, KNeq2 v0 :: ks) =>
           (V(Bool(not (equal(v0, v1)))), ks)

       (*  **********
       *   Cons.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Cons(e0, e1), rho), ks) =>
           (C(e0, rho), KCons1(e1, rho) :: ks)

       (*  Left operand computed.
       *)
       | (V v, KCons1 cl :: ks) =>
           (C cl, KCons2 v :: ks)

       (*  Right operand computed.
       *)
       | (V (List vs), KCons2 v :: ks) =>
           (V(List(v :: vs)), ks)

       (*  **********
       *   Append.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Append(e0, e1), rho), ks) =>
           (C(e0, rho), KAppend1(e1, rho) :: ks)

       (*  Left operand computed.
       *)
       | (V v, KAppend1 cl :: ks) =>
           (C cl, KAppend2 v :: ks)

       (*  Right operand computed.
       *)
       | (V (List vs), KAppend2 (List vs') :: ks) =>
           (V(List(vs' @ vs)), ks)

       (*  **********
       *   String concatenation.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Cat(e0, e1), rho), ks) =>
           (C(e0, rho), KCat1(e1, rho) :: ks)

       (*  Left operand computed.
       *)
       | (V v, KCat1 cl :: ks) =>
           (C cl, KCat2 v :: ks)

       (*  Right operand computed.
       *)
       | (V (Str s), KCat2 (Str s') :: ks) =>
           (V(Str(s' ^ s)), ks)

       (*  **********
       *   Orelse.  Ensure early termination if LHS is true.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Orelse(e0, e1), rho), ks) =>
           (C(e0, rho), KOr(e1, rho) :: ks)

       (*  Left operand true.
       *)
       | (v as V (Bool true), KOr cl :: ks) =>
           (v, ks)

       (*  Left operand false.  The value of the orelse expression is the value
       *  of the RHS.
       *)
       | (v as V (Bool false), KOr cl :: ks) =>
           (C cl, ks)

       (*  **********
       *   Andalso.  Ensure early termination if LHS is false.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Andalso(e0, e1), rho), ks) =>
           (C(e0, rho), KAnd(e1, rho) :: ks)

       (*  Left operand false.
       *)
       | (v as V (Bool false), KAnd cl :: ks) =>
           (v, ks)

       (*  Left operand true.  The value of the andalso expression is the value
       *  of the RHS.
       *)
       | (v as V (Bool true), KAnd cl :: ks) =>
           (C cl, ks)

       (*  **********
       *   Conditional.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Cond(e, e0, e1), rho), ks) =>
           (C(e, rho), KCond(e0, e1, rho) :: ks)

       (*  Test true.
       *)
       | (V (Bool true), KCond(e0, _, rho) :: ks) =>
           (C (e0, rho), ks)

       (*  Test false.
       *)
       | (V (Bool false), KCond(_, e1, rho) :: ks) =>
           (C (e1, rho), ks)

       (*  **********
       *   Application.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.App(e0, e1), rho), ks) =>
           (C (e0, rho), KApp1 (e1, rho) :: ks)

       (*  Operator evaluated.
       *)
       | (V v, KApp1 cl :: ks) =>
           (C cl, KApp2 v :: ks)

       (*  Operand evaluated and operator is projection.
       *)
       | (V (Tuple vs), KApp2 (Sel n) :: ks) =>
           (V (List.nth(vs, n-1)), ks)

       (*  Operand evaluated and operator is a built-in.
       *)
       | (V v, KApp2 (Builtin id) :: ks) =>
           (V(get baseEnv id (v, ks)), ks)

       (*  Operand evaluated and operator is a non-recursive closure.
       *)
       | (V v1, KApp2 (Closure (x, e0', rho0')) :: ks) =>
           (C (e0', update rho0' x v1), ks)

       (*  Operand evaluated and operator is a (potentially) recursive closure
       *  with one parameter.  Evaluate the body with environment updated for
       *  the parameter and the recursive function identifier.
       *)
       | (V v1, KApp2 (RecClosure(f, [x], e0, rho0, ys)) :: ks) =>
           (C (e0, update 
                     (update rho0 x v1) 
                     f 
                     (RecClosure(f, rev (x :: ys), e0, rho0, []))), ks)

       (*  Operand evaluated and operator is a (potentially) recursive closure
       *  with more than one parameter.  Add the binding for the first
       *  parameter and keep going.  The result is a value because it is still
       *  a (potentially recursive) function.
       *)
       | (V v1, KApp2 (RecClosure(f, x :: xs, e0, rho0, ys)) :: ks) =>
           (V (RecClosure(f, xs, e0, update rho0 x v1, x :: ys)), ks)

       (*  **********
       *   Tuples.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Tuple (e :: es), rho), ks) =>
           (C (e, rho), KTuple([], es, rho) :: ks)

       (*  Evaluated a component, have more to go.
       *)
       | (V v, KTuple (vs, e :: es, rho) :: ks) =>
           (C (e, rho), KTuple (v :: vs, es, rho) :: ks)

       (*  Evaluated last component.
       *)
       | (V v, KTuple (vs, [], _) :: ks) =>
           (V (Tuple (rev (v :: vs))), ks)

       (*  **********
       *   Let expressions.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Let([], e), rho), ks) =>
           (C (e, rho), ks)

       | (C(Ast.Let(Ast.ValDec(x, e') :: ds, e), rho), ks) =>
           (C (e', rho), KLetVal(SOME x, ds, e, rho) :: ks)

       | (C(Ast.Let(Ast.DoDec(e') :: ds, e), rho), ks) =>
           (C(e', rho), KLetVal(NONE, ds, e, rho) :: ks)

       | (C(Ast.Let(Ast.FunDec(f, xs, e') :: ds, e), rho), ks) =>
           (C (Ast.Let(ds, e), 
               update rho f (RecClosure(f, xs, e', rho, []))), ks)

       | (V v, KLetVal(SOME x, ds, e, rho) :: ks) =>
           (C (Ast.Let(ds, e), update rho x v), ks)

       | (V v, KLetVal(NONE, ds, e, rho) :: ks) =>
           (C (Ast.Let(ds, e), rho), ks)

       (*  Assignment.
       *)

       | (C(Ast.Assign(e', e), rho), ks) =>
           (C(e', rho), KAssign1(e, rho) :: ks)

       | (V v, KAssign1(e, rho) :: ks) =>
           (C(e, rho), KAssign2 v :: ks)

       | (V v, KAssign2(Location l) :: ks) =>
           (Store.update(l, v) ; (V Triv, ks))

       (*  **********
       *   Sequencing.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.Seq (e :: es), rho), ks) =>
           (C (e, rho), KSeq(es, rho) :: ks)

       (*  Evaluated a component, have more to go.
       *)
       | (V v, KSeq (e :: es, rho) :: ks) =>
           (C (e, rho), KSeq (es, rho) :: ks)

       (*  Evaluated last component.
       *)
       | (V v, KSeq ([], _) :: ks) =>
           (V v, ks)

       (*  **********
       *   While loops.
       *   **********
       *)

       (*  Initial closure.
       *)
       | (C(Ast.While(e', e), rho), ks) =>
           (C(e', rho), KWhile1(e', e, rho) :: ks)

       (*  Test true; evaluate body.
       *)
       | (V(Bool true), KWhile1(e', e, rho) :: ks) =>
           (C(e, rho), KWhile2(e', e, rho) :: ks)

       (*  Test false; evaluate to (), continue computation.
       *)
       | (V(Bool false), KWhile1(e', e, rho) :: ks) =>
           (V Triv, ks)

       (*  Evaluated body; repeat (just inlining C(While(e', e), rho)).
       *)
       | (V _, KWhile2(e', e, rho) :: ks) =>
           (C(e', rho), KWhile1(e', e, rho) :: ks)

       (*  Closures that are values.
       *)
       | (C(Ast.Int n, rho), ks) => (V(Int n), ks)

       | (C(Ast.Real n, rho), ks) => (V(Real n), ks)

       | (C(Ast.Char c, rho), ks) => (V(Char c), ks)

       | (C(Ast.Str s, rho), ks) => (V(Str s), ks)

       | (C(Ast.Bool v, rho), ks) => (V(Bool v), ks)

       | (C(Ast.Triv, rho), ks) => (V Triv, ks)

       | (C(Ast.Lambda(x, e), rho), ks) => (V(Closure(x, e, rho)), ks)

       | (C(Ast.Ident x, rho), ks) =>
           (
           (V (get rho x), ks)
           handle NotFound _ => (V (Builtin x), ks)
           )

       | (C(Ast.Sel n, rho), ks) =>
           (V (Sel n), ks)

       | (C(Ast.Nil, rho), ks) => (V (List []), ks)
       
       | (C(Ast.Null, rho), ks) => (V(Location ~1), ks)

       | _ => raise LibBase.Impossible "trans1"

  end

  (*  iterate s = v, where s = s_0 -> s_1 -> ... -> s_k = (V v, []).
  *)
  fun iterate (s : state) : value =
    case trans1 s of
         (V v, []) => v
       | s' => iterate s'

  (*  evalExp e = iterate (C(e, Env.empty), []).
  *)
  fun evalExp (e : Ast.exp) : value =
    iterate (C(e, Env.empty), [])

  (*  execPgm p = ().
  *
  *  Effect:  the program p is executed under the empty environment.  Each
  *  statement in p is executed in order.  A value declaration is executed by
  *  evaluating its RHS and then adding the binding to the current
  *  environment.  A function declaration is executed by adding the function
  *  binding to the current environment as an unapplied RecClosure.  An
  *  expression statement is executed by evaluating the expression to a value
  *  v, then printing a string representation of v to the terminal using
  *  valueToString.
  *)
  fun execPgm (Ast.Program ss : Ast.pgm) : unit =
  let
    fun execDec (rho : value env) (d : Ast.dec) : value env =
      case d of
           Ast.ValDec(x, e) =>
           let
             val v = iterate (C(e, rho), [])
           in
             update rho x v
           end
         | Ast.DoDec(e) =>
             let
               val _ = iterate (C(e, rho), [])
             in
               rho
             end
         | Ast.FunDec(f, xs, e) =>
             update rho f (RecClosure(f, xs, e, rho, []))

    fun execStms (rho : value env) (ss : Ast.stm list) : unit =
      case ss of
           [] => ()
         | Ast.Dec d :: ss =>
           let
             val rho' = execDec rho d
           in
             execStms rho' ss
           end
         | Ast.ExprStm e :: ss =>
             let
               val v = iterate (C(e, rho), [])
               val () = print (valueToString v ^ "\n")
             in
               execStms rho ss
             end
  in
    execStms Env.empty ss
  end


end
