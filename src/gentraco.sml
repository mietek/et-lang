
(*********************************************************************)
(*                                                                   *)
(* GENTRACON.SML  - THE GENERATOR OF THE TRANSLATION OF CONSTRUCTORS *)
(*                                                                   *)
(*       Programmed in Standard ML by Tomasz Wierzbicki, 1992.       *)
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
(*       splitconty = fn: typex -> typex list                        *)
(*    from TYLAM.SML:                                                *)
(*       datatype term and typex and tyvar and tycon                 *)
(* Exports:                                                          *)
(*       gentracon  = fn: tyvar ref -> tycon ref -> int -> int ->    *)
(*                        typex -> bool -> term                      *)
(*                                                                   *)
(*********************************************************************)

fun gentracon newtref newtycon pos conum conty elim =
  let
    val conpara = splitconty conty;
    val paranum = length conpara;
  in
    eval
    ( iter (fn trm => Lambda trm)
        (#2 (revfold
              (fn (p , (j,trm)) =>
                (pred j,
                 Application
                   (trm,
                    Application
                      (Application
                         (mon true newtref p elim,
                          Lambda
                            ((fn x => if elim
                                then Pair (Parameter 0 , x)
                                else x
                             )(#2
                                (iter (fn (k , trm) =>
                                         (pred k,
                                          Application
                                            (trm , Parameter k)
                                         )
                                      )
                                      (conum,
                                         Application
                                           ((if elim
                                               then Recursor
                                               else Iterator) newtycon,
                                            Parameter 0
                                           )
                                      )
                                      conum
                                )
                              )
                            )
                         ),
                         Parameter j
                      )
                   )
                )
              )
              conpara ( conum + paranum - 1 , Parameter pos )
            )
        ) (conum + paranum)
    )
  end;

(* end of GENTRACON.SML **********************************************)

