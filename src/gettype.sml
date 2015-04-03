
(*********************************************************************)
(*                                                                   *)
(*           GETTYPE.SML  - THE PARSER OF TYPE EXPRESSIONS           *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from LEXICAL.SML:                                              *)
(*       datatype symbol                                             *)
(*       getsym        = fn: unit -> symbol                          *)
(*       nextsym       = fn: unit -> unit                            *)
(*    from TYLAM.SML:                                                *)
(*       datatype typex and tyvar and tycon                          *)
(*    from TYPARAM.SML:                                              *)
(*       abstype typaram with                                        *)
(*          findtypar  = fn: string -> typaram -> tyvar ref          *)
(*          checktypar = fn: typaram -> unit                         *)
(*    from ENVIRON.SML:                                              *)
(*       abstype environment with                                    *)
(*          find_ty    = fn: string -> environment -> tycon ref      *)
(* Exports:                                                          *)
(*       gettype       = fn: typaram -> environment -> typex ->      *)
(*                       string -> typex                             *)
(*       con Type_expected = - : exn                                 *)
(*                                                                   *)
(*********************************************************************)

exception Type_expected;

fun gettype param env newt newtid =
  let
    fun gettycon str =
      if str = newtid
        then ( nextsym() ; checktypar param ; newt )
        else let
               val t as ref (Type {varlist=vl,...}) = find_ty str env;
             in
               nextsym();
               Tycon (t , iter (fn para => para @
                 [gettype param env newt newtid]) nil (length vl))
             end;

    fun atomic () =
      case getsym() of
        Ident' str     => ( nextsym() ; Tyvar (findtypar str param) ) |
        Identupper str => gettycon str |
        Identlower str => gettycon str |
        Boolsym        => ( nextsym() ; Tybool ) |
        Tyunitsym      => ( nextsym() ; Tyunit ) |
        Absym          => ( nextsym() ; Absurd ) |
        Left_brace     => ( nextsym();
                            let
                              val t = gettype param env newt newtid;
                            in
                              if getsym() = Right_brace
                                then ( nextsym() ; t )
                                else raise Right_brace_expected
                            end
                          ) |
                     _ => raise Type_expected;

    fun typair () =
      let
        fun f t = if getsym() = Star
                    then ( nextsym() ; f (Typair (t , atomic())) )
                    else t
      in
        f ( atomic() )
      end;

    val ty =
      let
        fun f t = if getsym() = Plus
                    then ( nextsym() ; f (Tyun (t , typair())) )
                    else t
      in
        f ( typair() )
      end;
  in
    if getsym() = Thinarrow
      then ( nextsym() ; Tyfun (ty , gettype param env newt newtid) )
      else ty
  end; (* gettype *)

(* end of GETTYPE.SML ************************************************)

