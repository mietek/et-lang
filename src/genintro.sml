
(*********************************************************************)
(*                                                                   *)
(*     GENINTRO.SML  - THE GENERATOR OF THE TYPE OF INTRODUCTORS     *)
(*                                                                   *)
(*       Programmed in Standard ML by Tomasz Wierzbicki, 1993.       *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from TYLAM.SML:                                                *)
(*       datatype typex and tyvar                                    *)
(*    from GENELIM.SML:                                              *)
(*       substy     = fn: typex -> (typex -> bool) -> typex -> typex *)
(* Exports:                                                          *)
(*       genintro   = fn: typex -> typex list -> bool -> typex ->    *)
(*                        typex                                      *)
(*                                                                   *)
(*********************************************************************)

fun genintro newt contys elim result =
   let               
      val V = if elim then Tyun (newt , result) else result;
   in
     fold (fn (t,ts) =>
             Tyfun ((Tyfun (result,substy (fn t => t = newt) V t)),ts))
          contys (Tyfun (result , newt))
   end;

(* end of GENINTRO.SML ***********************************************)

