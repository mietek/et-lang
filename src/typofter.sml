
(*********************************************************************)
(*                                                                   *)
(*       TYPOFTERM.SML - THE ANALYSER OF TYPES OF LAMBDA TERMS       *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from TYLAM.SML:                                                *)
(*       datatype term and typex and tyvar and constr and tycon      *)
(*    from TYPEX.SML:                                                *)
(*       derefer           = fn: typex -> typex                      *)
(*       tycopy            = fn: typex -> typex                      *)
(*    from UNIFY.SML:                                                *)
(*       occurs            = fn: tyvar ref -> typex -> unit          *)
(*       infix unify       = fn: typex * typex -> unit               *)
(*       con Type_mismatch = - : exn                                 *)
(* Exports:                                                          *)
(*       typofterm         = fn: term -> typex                       *)
(*                                                                   *)
(*********************************************************************)

val typofterm =
   let
      fun f var ( Parameter n ) = nth ( var , n )
        | f  _  ( Constructor ( Constr (ref {ty=t,...}) ) ) = tycopy t
        | f  _  ( Iterator ( ref (Type {typiter=t,...}) ) ) = tycopy t
        | f  _  ( Recursor ( ref (Type {typrec =t,...}) ) ) = tycopy t
        | f var ( Lambda trm ) = 
             let
                val argty = Tyvar (ref None);
             in
                Tyfun ( argty , f ( argty :: var ) trm )
             end
        | f var ( Application (rator,rand) ) =
             let
                val tyran = derefer (f var rand);
             in 
                case derefer (f var rator) of
                   Tyfun (t1,t2) => ( t1 unify tyran ; t2 ) |
                   Tyvar tr =>
                      let
                         val tyres = Tyvar (ref None);
                      in
                         occurs tr tyran;
                         tr := Some ( Tyfun (tyran , tyres) );
                         tyres
                      end |
                   _ => raise Type_mismatch
             end
        | f _ True   = Tybool
        | f _ False  = Tybool
        | f _ Unit   = Tyunit
        | f _ Case0  = Tyfun (Absurd , Tyvar (ref None))
        | f _ Case1  =
            let
              val tv = Tyvar (ref None);
            in
              Tyfun (Tyunit , Tyfun (tv , tv))
            end
        | f _ When  =
            let
              val lefty   = Tyvar (ref None);
              val righty  = Tyvar (ref None);
              val resulty = Tyvar (ref None);
            in
              Tyfun (Tyun (lefty , righty),
                     Tyfun (Tyfun (lefty , resulty), 
                            Tyfun (Tyfun (righty , resulty),
                                   resulty
                                  )
                           )
                    )
            end
        | f var Inl = 
            let 
              val lefty = Tyvar (ref None)
            in
              Tyfun (lefty , Tyun (lefty , Tyvar (ref None)))
            end
        | f var Inr = 
            let 
              val righty = Tyvar (ref None)
            in
              Tyfun (righty , Tyun (Tyvar (ref None) , righty))
            end
        | f var ( Conditional (t1,t2,t3) ) =
             ( f var t1 unify Tybool;
               let
                  val result = f var t2;
               in
                  result unify f var t3;
                  result
               end
             )
        | f var ( Equality (t1,t2) ) = 
             ( f var t1 unify f var t2 ; Tybool )
        | f var ( Pair (t1,t2) ) = Typair ( f var t1 , f var t2 )
        | f var Fst = let
                         val tv = Tyvar (ref None);
                      in
                         Tyfun ( Typair (tv , Tyvar (ref None)) , tv )
                      end
        | f var Snd = let
                         val tv = Tyvar (ref None);
                      in
                         Tyfun ( Typair (Tyvar (ref None) , tv) , tv )
                      end;
   in
      f nil
   end;

(* end of TYPOFTERM.SML **********************************************)

