
(*********************************************************************)
(*                                                                   *)
(*  GENTRADES.SML - THE GENERATOR OF THE TRANSLATION OF DESTRUCTORS  *)
(*                                                                   *)
(*       Programmed in Standard ML by Tomasz Wierzbicki, 1993.       *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from ARITHME.SML:                                              *)
(*       pred       = fn: int -> int                                 *)
(*    from EVAL.SML:                                                 *)
(*       eval       = fn: term -> term                               *)
(*    from ITEREC.SML:                                               *)
(*       iter       = fn: ('st -> 'st) -> 'st -> int -> 'st          *)
(*    from MONAMON.SML:                                              *)
(*       mon        = fn: bool -> tyvar ref -> typex -> bool -> term *)
(*    from TYLAM.SML:                                                *)
(*       datatype term and typex and tyvar and tycon                 *)
(* Exports:                                                          *)
(*       gentrades  = fn: tyvar ref -> tycon ref -> int -> int ->    *)
(*                        typex -> bool -> term                      *)
(*                                                                   *)
(*********************************************************************)

fun gentrades newtref newtycon pos conum conty elim = eval
  (iter
     (fn trm => Lambda trm)
     (Application
        (Application
           (mon true newtref conty elim,
            (fn x =>
              if elim
                 then (Lambda
                   (Application
                      (Application
                         (Application (When , Parameter 0),
                          (Lambda (Parameter 0))
                         ),
                       nest 1 x
                      )
                   ))
                 else x
            )
            (#2 (iter (fn (k , trm) => (pred k,
                                   Application (trm , Parameter k)))
                      (conum,
                       (if elim then Recursor else Iterator) newtycon
                      )
                      conum
               )
            )
           ),
           Application (Parameter (pos + 1), Parameter 0)
        )
     )
     (conum + 1)
  );

(* end of GENTRADES.SML **********************************************)

