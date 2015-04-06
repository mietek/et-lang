
(*********************************************************************)
(*                                                                   *)
(*       TYPARAM.SML  - TOOLS FOR DEALING WITH TYPE PARAMETERS       *)
(*                                                                   *)
(*       Programmed in Standard ML by Tomasz Wierzbicki, 1992.       *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from LEXICAL.SML:                                              *)
(*       datatype symbol                                             *)
(*       getsym        = fn: unit -> symbol                          *)
(*       nextsym       = fn: unit -> unit                            *)
(*    from TYLAM.SML:                                                *)
(*       datatype tyvar                                              *)
(* Exports:                                                          *)
(*       con Unknown_type_param   = - : exn                          *)
(*       con Bad_typaram          = - : exn                          *)
(*       con Typaram_expected     = - : exn                          *)
(*       con Unused_typaram       = - : exn                          *)
(*       abstype typaram with                                        *)
(*          gettypar   = fn: unit -> typaram                         *)
(*          findtypar  = fn: string -> tyvar ref                     *)
(*          checktypar = fn: typaram -> unit                         *)
(*          mktyvars   = fn: typaram -> tyvar ref list               *)
(*          usedtypar  = fn: typaram -> unit                         *)
(*                                                                   *)
(*********************************************************************)

exception Unknown_type_param
      and Bad_typaram
      and Typaram_expected
      and Unused_typaram;

abstype
   typaram = TP of (string * tyvar ref * bool ref) list
with
   fun gettypar () =
      let
         fun f param =
            case getsym() of
               Ident' str =>
                  ( nextsym();
                    f ( param @ [ (str , ref None , ref false) ] )
                  ) |
               _ => param;
      in
         nextsym() ; TP (f nil)
      end;

   fun findtypar str (TP ((id , tr , u) :: param)) =
          if id = str
             then (u := true ; tr)
             else findtypar str (TP param)
     | findtypar _ (TP nil) = raise Unknown_type_param;

   fun checktypar (TP param) =
      let
         fun f ((id,_,_) :: param) =
                ( case getsym() of
                     Ident' str => if id = str
                                      then ( nextsym() ; f param )
                                      else raise Bad_typaram |
                              _ => raise Typaram_expected
                )
           | f nil = ();
      in
         f param
      end;

   fun mktyvars (TP param) = map (#2) param;

   fun usedtypar (TP param) =
      app (fn (_,_,ref true ) => () |
              (_,_,ref false) => raise Unused_typaram) param;
end; (* typaram *)

(* end of TYPARAM.SML ************************************************)

