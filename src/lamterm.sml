
(*********************************************************************)
(*                                                                   *)
(*         LAMTERM.SML - TOOLS FOR DEALING WITH LAMBDA TERMS         *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from ARITHME.SML:                                              *)
(*       succ     = fn: int -> int                                   *)
(*    from LISTING.SML:                                              *)
(*       out      = fn: string -> unit                               *)
(*    from TYLAM.SML:                                                *)
(*       datatype term and constr and tycon                          *)
(* Exports:                                                          *)
(*       nest     = fn: int -> term -> term                          *)
(*       occvar   = fn: term -> bool                                 *)
(*       freevar  = fn: term -> bool                                 *)
(*       printerm = fn: int -> term -> unit                          *)
(*       z        = ? : int                                          *)
(*                                                                   *)
(*********************************************************************)

fun nest n = 
   let
      fun f l (Parameter k) = Parameter (if k >= l then k+n else k)
        | f l (Lambda t) = Lambda ( f (succ l) t )
        | f l (Application (t1,t2)) = Application (f l t1 , f l t2)
        | f l (Conditional (t1,t2,t3)) =
             Conditional (f l t1 , f l t2 , f l t3)
        | f l (Equality (t1,t2)) = Equality (f l t1 , f l t2)
        | f l (Pair (t1,t2)) = Pair (f l t1 , f l t2)
        | f _ t = t;
   in
      f 0
   end;

local
   fun f p l (Parameter n) = p (n,l)
     | f p l (Lambda t) = f p (succ l) t
     | f p l (Application (t1,t2)) = f p l t1 orelse f p l t2
     | f p l (Conditional (t1,t2,t3)) = f p l t1 orelse f p l t2 orelse
                                        f p l t3 
     | f p l (Equality (t1,t2)) = f p l t1 orelse f p l t2
     | f p l (Pair (t1,t2)) = f p l t1 orelse f p l t2
     | f _ _ _ = false;
in
   val occvar  = f op  = 0;
   val freevar = f op >= 0;
end;

val z = ord "z";

fun printerm level (Parameter n) = out ( chr (z-level+n+1) )
  | printerm   _   (Constructor (Constr (ref {name=id,...}))) = out id
  | printerm   _   (Iterator (ref (Type {name=id,coty=ct,...}))) =
       out ("_" ^ id ^ (if ct then "ci" else "it"))
  | printerm   _   (Recursor (ref (Type {name=id,coty=ct,...}))) =
       out ("_" ^ id ^ (if ct then "cr" else "rec"))
  | printerm level (trm as Lambda _) =
       ( out "fn";
         let 
            fun param (l , Lambda t) = 
                   ( out ( " " ^ chr (z-l) ) ; param (succ l , t) )
              | param arg = arg;                                 
            val (l , t) = param (level , trm);
         in
            out " => " ; printerm l t
         end
       )
  | printerm level (Application (rator,rand)) =
       ( case rator of
            Lambda      _ => (out"(" ; printerm level rator ; out")") |
            Conditional _ => (out"(" ; printerm level rator ; out")") |
                        _ => printerm level rator;
         out " ";
         case rand of
            Lambda      _ => (out"(" ; printerm level rand ; out")") |
            Application _ => (out"(" ; printerm level rand ; out")") |
            Conditional _ => (out"(" ; printerm level rand ; out")") |
            Equality    _ => (out"(" ; printerm level rand ; out")") |
            Pair        _ => (out"(" ; printerm level rand ; out")") |
                        _ => printerm level rand 
       )                      
  | printerm   _   True  = out "True"
  | printerm   _   False = out "False"
  | printerm   _   Inl   = out "Inl"
  | printerm   _   Inr   = out "Inr"
  | printerm   _   When  = out "when"
  | printerm   _   Case0 = out "case0"
  | printerm   _   Case1 = out "case1"
  | printerm   _   Fst   = out "fst"
  | printerm   _   Snd   = out "snd"
  | printerm   _   Unit  = out "()"
  | printerm level (Conditional (t1,t2,t3)) =
       ( out "if ";
         printerm level t1;
         out " then ";
         printerm level t2;
         out " else ";
         printerm level t3
       )
  | printerm level (Equality (t1,t2)) =
       ( printerm level t1;
         out " = ";
         printerm level t2
       )
  | printerm level (Pair (t1,t2)) =
       ( case t1 of
            Lambda      _ => (out "(" ; printerm level t1 ; out ")" ) |
            Conditional _ => (out "(" ; printerm level t1 ; out ")" ) |
            Equality    _ => (out "(" ; printerm level t1 ; out ")" ) |
                        _ => printerm level t1;
         out " , ";
         case t2 of
            Lambda      _ => (out "(" ; printerm level t2 ; out ")" ) |
            Conditional _ => (out "(" ; printerm level t2 ; out ")" ) |
            Equality    _ => (out "(" ; printerm level t2 ; out ")" ) |
            Pair        _ => (out "(" ; printerm level t2 ; out ")" ) |
                        _ => printerm level t2
       );

(* end of LAMTERM.SML ************************************************)

