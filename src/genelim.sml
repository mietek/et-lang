
(*********************************************************************)
(*                                                                   *)
(*      GENELIM.SML  - THE GENERATOR OF THE TYPE OF ELIMINATORS      *)
(*                                                                   *)
(*       Programmed in Standard ML by Tomasz Wierzbicki, 1992.       *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from TYLAM.SML:                                                *)
(*       datatype typex and tyvar                                    *)
(* Exports:                                                          *)
(*       splitconty = fn: typex -> typex list                        *)
(*       substy     = fn: typex -> (typex -> bool) -> typex -> typex *)
(*       genelim    = fn: typex -> typex list -> bool -> typex ->    *)
(*                        typex                                      *)
(*                                                                   *)
(*********************************************************************)

val splitconty =
  let
    fun f acc ( Tyfun (t1 , t2) ) = f (acc @ [t1]) t2
      | f acc _ = acc;              
  in  
    f nil
  end;

fun substy isoldty newty t =
   if isoldty t
      then newty
      else case t of
         Tyvar (ref None) => t |
         Tyvar (ref (Some ty)) => substy isoldty newty ty |
         Tycon (t , para) =>
            Tycon (t , map (substy isoldty newty) para) |
         Tyfun (t1 , t2) =>
            Tyfun (substy isoldty newty t1 , substy isoldty newty t2) |
         Typair (t1 , t2) =>
            Typair (substy isoldty newty t1 , substy isoldty newty t2)|
         Tyun (t1 , t2) =>
            Tyun (substy isoldty newty t1 , substy isoldty newty t2) |
         t => t;

fun genelim newt contys elim result =
   let               
      val V = if elim then Typair (newt , result) else result;

      fun f (t::ts) = Tyfun (substy (fn t => t = newt) V t , f ts)
        | f nil = result;
   in
      Tyfun (newt , fold (fn (t,ts) => Tyfun (f (splitconty t) , ts))
             contys result)
   end;

(* end of GENELIM.SML ************************************************)

