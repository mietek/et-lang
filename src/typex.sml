
(*********************************************************************)
(*                                                                   *)
(*        TYPEX.SML - TOOLS FOR DEALING WITH TYPE EXPRESSIONS        *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from ARITHME.SML:                                              *)
(*      succ     = fn: int -> int                                    *)
(*    from ITEREC.SML:                                               *)
(*      uncurry  = fn: ('a -> 'b -> 'c) -> 'a * 'b -> 'c             *)
(*    from LISTING.SML:                                              *)
(*      out      = fn: string -> unit                                *)
(*    from TYLAM.SML:                                                *)
(*      datatype typex and tyvar and tycon                           *)
(* Exports:                                                          *)
(*      derefer  = fn: typex -> typex                                *)
(*      eratyvar = fn: typex -> unit                                 *)
(*      tycopy   = fn: typex -> typex                                *)
(*      numtyvar = fn: typex -> int -> unit                          *)
(*      a        = ? : int                                           *)
(*      printy   = fn: typex -> unit                                 *)
(*      printype = fn: typex -> unit                                 *)
(*                                                                   *)
(*********************************************************************)
                                   
fun derefer ( Tyvar ( ref (Some ty) ) ) = derefer ty
  | derefer t = t;

fun eratyvar ( Tyvar ( tr as ref (Label _) ) ) = tr := None
  | eratyvar ( Tyvar ( ref (Some ty) ) ) = eratyvar ty
  | eratyvar ( Tycon (_ , ts) ) = app eratyvar ts
  | eratyvar ( Tyfun (t1 , t2) ) = (eratyvar t1 ; eratyvar t2)
  | eratyvar ( Typair (t1 , t2) ) = (eratyvar t1 ; eratyvar t2)
  | eratyvar ( Tyun (t1 , t2) ) = (eratyvar t1 ; eratyvar t2)
  | eratyvar _ = ();

fun tycopy t =
   let
      fun copy n ntrs ( Tyvar ( tr as (ref None) ) ) =
             let
                val ntr = ref None;
             in
                tr := Label n;
                ( succ n , ntrs @ [ntr] , Tyvar ntr )
             end
        | copy n ntrs ( Tyvar ( ref (Label k) ) ) =
             ( n , ntrs , Tyvar ( nth (ntrs , k) ) )
        | copy n ntrs ( Tyvar ( ref (Some ty) ) ) =
             copy n ntrs ty
        | copy n ntrs ( Tycon (t , para) ) =
             let
                val (n' , ntrs' , para') = fold
                       ( fn ( t , (n,ntrs,ps) ) =>
                            let
                               val (n',ntrs',p) = copy n ntrs t;
                            in
                               (n',ntrs',p::ps)
                            end
                       ) para (n , ntrs , nil);
             in                      
                ( n' , ntrs' , Tycon (t , para') )
             end 
        | copy n ntrs ( Tyfun (t1 , t2) ) =
             let
                val (n'  , ntrs'  , t1') = copy n  ntrs  t1;
                val (n'' , ntrs'' , t2') = copy n' ntrs' t2;
             in
                ( n'' , ntrs'' , Tyfun (t1',t2') )
             end                       
        | copy n ntrs Tybool = (n , ntrs , Tybool)
        | copy n ntrs Tyunit = (n , ntrs , Tyunit)
        | copy n ntrs Absurd = (n , ntrs , Absurd)
        | copy n ntrs ( Typair (t1 , t2) ) =
             let
                val (n'  , ntrs'  , t1') = copy n  ntrs  t1;
                val (n'' , ntrs'' , t2') = copy n' ntrs' t2;
             in
                ( n'' , ntrs'' , Typair (t1',t2') )
             end
        | copy n ntrs ( Tyun (t1 , t2) ) =
             let
                val (n'  , ntrs'  , t1') = copy n  ntrs  t1;
                val (n'' , ntrs'' , t2') = copy n' ntrs' t2;
             in
                ( n'' , ntrs'' , Tyun (t1',t2') )
             end;

      val ( _ , _ , t' ) = copy 0 nil t;
   in
      eratyvar t ; t'
   end; (* tycopy *)

fun numtyvar ( Tyvar ( tr as (ref None) ) ) n =
       ( tr := Label n ; succ n )           
  | numtyvar ( Tyvar ( ref (Some ty) ) ) n = numtyvar ty n
  | numtyvar ( Tycon (_ , ts) ) n = revfold (uncurry numtyvar) ts n
  | numtyvar ( Tyfun (t1 , t2) ) n = numtyvar t2 (numtyvar t1 n)
  | numtyvar ( Typair (t1 , t2) ) n = numtyvar t2 (numtyvar t1 n)
  | numtyvar ( Tyun (t1 , t2) ) n = numtyvar t2 (numtyvar t1 n)
  | numtyvar _ n = n;
                                        
val a = ord "a";

fun printy ( Tyvar ( ref (Label n) ) ) =
       out ( "'" ^ chr (a + n) )
  | printy ( Tyvar ( ref (Some ty) ) ) = printy ty
  | printy ( Tycon (ref (Type {name=id,...}) , params) ) =
       ( out id; 
         app ( fn t => ( out " ";
                         case derefer t of
                            Tyvar       _ => printy t |
                            Tycon (_,nil) => printy t |
                            Tybool        => printy t |
                            _ => ( out "(" ; printy t ; out ")" )
                       )
             ) params
       )
  | printy ( Tyfun (t1 , t2) ) =
       ( case derefer t1 of
            Tyvar         _ => printy t1 |
            Tycon (_ , nil) => printy t1 |
            Tybool          => printy t1 |
            Tyunit          => printy t1 |
            Absurd          => printy t1 |
            Typair        _ => printy t1 |
            Tyun          _ => printy t1 |
                          _ => ( out "(" ; printy t1 ; out ")" );
         out " -> ";
         printy t2
       )
  | printy Tybool = out "BOOL"
  | printy Tyunit = out "UNIT"
  | printy Absurd = out "{}"
  | printy ( Typair (t1 , t2) ) =
       ( case derefer t1 of
            Tyvar         _ => printy t1 |
            Tycon (_ , nil) => printy t1 |
            Tybool          => printy t1 |
            Tyunit          => printy t1 |
            Absurd          => printy t1 |
            Typair        _ => printy t1 |
                          _ => ( out "(" ; printy t1 ; out ")" );
         out " * ";
         case derefer t2 of
            Tyvar         _ => printy t2 |
            Tycon (_ , nil) => printy t2 |        
            Tybool          => printy t2 |
            Tyunit          => printy t2 |
            Absurd          => printy t2 |
                          _ => ( out "(" ; printy t2 ; out ")" )
         
       )
  | printy ( Tyun (t1 , t2) ) =
       ( case derefer t1 of
            Tyvar         _ => printy t1 |
            Tycon (_ , nil) => printy t1 |
            Tybool          => printy t1 |
            Tyunit          => printy t1 |
            Absurd          => printy t1 |
            Tyun          _ => printy t1 |
            Typair        _ => printy t1 |
                          _ => ( out "(" ; printy t1 ; out ")" );
         out " + ";
         case derefer t2 of
            Tyvar         _ => printy t2 |
            Tycon (_ , nil) => printy t2 |        
            Tybool          => printy t2 |
            Tyunit          => printy t2 |
            Absurd          => printy t2 |
            Typair        _ => printy t2 |
                          _ => ( out "(" ; printy t2 ; out ")" )
         
       );

fun printype t = ( numtyvar t 0 ; printy t ; eratyvar t );
        
(* end of TYPEX.SML **************************************************)

