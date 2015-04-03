
(*********************************************************************)
(*                                                                   *)
(*             UNIFY.SML - THE TYPE UNIFICATION ALGORITHM            *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from TYLAM.SML:                                                *)
(*       datatype typex and tyvar                                    *)
(*    from TYPEX.SML:                                                *)
(*       derefer           = fn: typex -> typex                      *)
(* Exports:                                                          *)
(*       occurs            = fn: tyvar ref -> typex -> unit          *)
(*       infix unify       = fn: typex * typex -> unit               *)
(*       con Infinite_type = - : exn                                 *)
(*       con Type_mismatch = - : exn                                 *)
(*                                                                   *)
(*********************************************************************)

exception Infinite_type and Type_mismatch;

fun occurs tr ( Tyvar (tr' as ref None) ) = if tr = tr'
                                               then raise Infinite_type
                                               else ()
  | occurs tr ( Tyvar ( ref (Some ty) ) ) = occurs tr ty
  | occurs tr ( Tycon (_,para) ) = app (occurs tr) para
  | occurs tr ( Tyfun (t1,t2) ) = ( occurs tr t1 ; occurs tr t2 )
  | occurs tr ( Typair (t1,t2) ) = ( occurs tr t1 ; occurs tr t2 )
  | occurs tr ( Tyun (t1,t2) ) = ( occurs tr t1 ; occurs tr t2 )
  | occurs _ _ = ();

infix unify;
fun ( Tyvar (tr as ref None) ) unify t =
      let
         val t' = derefer t;
      in
         case t' of
            Tyvar tr' => if tr = tr'
                            then ()
                            else tr := Some t' |
            _ => ( occurs tr t' ; tr := Some t' )
      end
  | ( Tyvar ( tr as ref (Some ty) ) ) unify t = ty unify t
  | t unify ( t' as Tyvar _ ) = t' unify t
  | ( Tycon (t , para) ) unify ( Tycon (t' , para') ) =
       if t <> t'
          then raise Type_mismatch
          else let
                  fun f (t::ts) (t'::ts') = ( t unify t' ; f ts ts' )
                    | f   nil      nil    = ();
               in
                  f para para'
               end
  | ( Tyfun (t1,t2) ) unify ( Tyfun (t1',t2') ) =
       ( t1 unify t1' ; t2 unify t2' )
  | Tybool unify Tybool = ()
  | Tyunit unify Tyunit = ()
  | Absurd unify Absurd = ()
  | ( Typair (t1,t2) ) unify ( Typair (t1',t2') ) =
       ( t1 unify t1' ; t2 unify t2' )
  | ( Tyun (t1,t2) ) unify ( Tyun (t1',t2') ) =
       ( t1 unify t1' ; t2 unify t2' )
  | _ unify _ = raise Type_mismatch;

(* end of UNIFY.SML **************************************************)

