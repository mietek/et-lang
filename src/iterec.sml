                                                                      
(*********************************************************************)
(*								     *)
(*  ITEREC.SML  - curry/uncurry converters; iterators and recursors  *)
(*                     for cardinals and lists.                      *)
(*								     *)
(*       Programmed in Standard ML by Tomasz Wierzbicki, 1992.       *)
(*                                                                   *)
(*                                                                   *)
(* Imports: none                                                     *)
(* Exports:                                                          *)
(*       curry     = fn: ('a * 'b -> 'c) -> 'a -> 'b -> 'c           *)
(*       uncurry   = fn: ('a -> 'b -> 'c) -> 'a * 'b -> 'c           *)
(*       con Iter  = - : exn                                         *)
(*       iter      = fn: ('st -> 'st) -> 'st -> int -> 'st           *)
(*       con Recur = - : exn                                         *)
(*       recur     = fn: (int -> 'st -> 'st) -> 'st -> int -> 'st    *)
(*       listiter  = fn: 'res -> ('elem -> 'res -> 'res) ->          *)
(*                       'elem list -> 'res                          *)
(*       listrecur = fn: 'res ->                                     *)
(*                       ('elem -> 'elem list -> 'res -> 'res) ->    *)
(*                       'elem list -> 'res                          *)
(*								     *)
(*********************************************************************)


(******************************* CURRY *******************************)

fun curry f x y = f (x,y);
fun uncurry f (x,y) = f x y;

(***************************** CARDINALS *****************************)

(*
Idea :
fun iter next state 0 = state
  | iter next state n = next ( iter next state (n-1) );
*)
exception Iter;
fun iter next state n =
   let
      fun f state 0 = state
	| f state n = f (next state) (n-1);
   in
      if n<0
         then raise Iter
	 else f state n
   end;    

(*
Idea :
fun recur h g 0 = g
  | recur h g n = h n ( recur h g (n-1) );
*)
exception Recur;
fun recur h g n =                               
   let 
      fun f x y = if x = n then y else f (x+1) (h x y);
   in 
      if n<0
         then raise Recur
	 else f 0 g      
   end;

(******************************* LISTS *******************************)
                                                                  
(* 
Idea :
fun listiter g h   nil   = g
  | listiter g h (x::xs) = h x (listiter g h xs);
*)
fun listiter g h l = 
   let
      fun f (x::xs) acc = f xs (h x acc)
        | f   nil   acc = acc;
   in 
      f (rev l) g
   end;

(* 
Idea :
fun listrecur g h nil = g
  | listrecur g h (x::xs) = h x xs (listiter g h xs);
*)
fun listrecur g h l = 
   let
      fun f (x::xs) acc = f xs (h x xs acc)
        | f   nil   acc = acc;
   in 
      f (rev l) g
   end;

(* end of ITEREC.SML *************************************************)

