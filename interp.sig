(*  COMP 323 Project 4:  Interpretation.
*
*  N. Danner
*)

signature INTERP =
sig


  (*  The structure that implements the store.  The only thing the interpreter
  *  client (e.g., driver) needs to know is how to initialize a new store.
  *)
  structure Store : sig 
                      (*  makeStore n = ()
                      *
                      *  Side-effect:  a new store of size n is created with
                      *  all locations free.
                      *)
                      val makeStore : int -> unit 
                    end

  (*  Whether or not to enable garbage collection.
  *)
  val enableGC : bool ref

  (*  The type of a value.
  *)
  type value

  (*  valueToString v = a string representation of v.
  *)
  val valueToString : value -> string

  (*  evalExp e = v, where _ |- e => v.
  *)
  val evalExp : Ast.exp -> value

  (*  execPgm p = ().
  *
  *  Side-effect:  the program p is executed.  In particular, for each
  *  expression statement of the form "e ;" in p, the value of e is printed
  *  to the terminal.
  *
  *  Pre-condition:  for each expression statement of the form "e ;" in p, e is
  *  a ground-type expression.
  *)
  val execPgm : Ast.pgm -> unit

end
