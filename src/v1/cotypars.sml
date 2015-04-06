
(*********************************************************************)
(*                                                                   *)
(*            COTYPARS.SML - THE COTYPE DEFINITION PARSER            *)
(*                                                                   *)
(*       Programmed in Standard ML by Tomasz Wierzbicki, 1993.       *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from ARITHME.SML:                                              *)
(*       succ         = fn: int -> int                               *)
(*    from ENVIRON.SML:                                              *)
(*       abstype environment with                                    *)
(*          repl_ty   = fn: tycon ref -> environment -> environment  *)
(*    from GENINTRO.SML:                                             *)
(*       genintro     = fn: typex -> typex list -> bool -> typex ->  *)
(*                          typex                                    *)
(*       splitconty   = fn: typex -> typex list                      *)
(*    from GENTRADES.SML:                                            *)
(*       gentrades    = fn: tyvar ref -> tycon ref -> int -> int ->  *)
(*                          typex -> bool -> term                    *)
(*    from GETTYPE.SML:                                              *)
(*       con Type_expected          = - : exn                        *)
(*       gettype      = fn: typaram -> environment -> typex ->       *)
(*                          string -> typex                          *)
(*    from LAMPARS.SML:                                              *)
(*       con Equal_expected         = - : exn                        *)
(*       con Semicolon_expected     = - : exn                        *)
(*    from LEXICAL.SML:                                              *)
(*       datatype symbol                                             *)
(*       getsym       = fn: unit -> symbol                           *)
(*       nextsym      = fn: unit -> unit                             *)
(*    from TYLAM.SML:                                                *)
(*       datatype term and typex and tyvar and constr and tycon      *)
(*    from TYPARAM.SML:                                              *)
(*       abstype typaram with                                        *)
(*          gettypar  = fn: unit -> typaram                          *)
(*          mktyvars  = fn: typaram -> tyvar ref list                *)
(*          usedtypar = fn: typaram -> unit                          *)
(*    from TYPARS.SML:                                               *)
(*       con Tycon_expected         = - : exn                        *)
(*    from UNIFY.SML:                                                *)
(*       occurs       = fn: tyvar ref -> typex -> unit               *)
(*       con Infinite_type          = - : exn                        *)
(* Exports:                                                          *)
(*       con Destructor_expected   = - : exn                         *)
(*       con Duplicated_destructor = - : exn                         *)
(*       cotypars     = fn: environment -> environment               *)
(*                                                                   *)
(*********************************************************************)

exception Tycon_expected
      and Destructor_expected
      and Duplicated_destructor;

fun cotypars env =
  let
    val newt as Tyvar newtref = Tyvar (ref None);
    val newtycon = ref Marker;
    val result = Tyvar (ref None);

    fun tydef newtid =
      let
        val param = gettypar();
      in
        if getsym() = Equal
          then
          ( nextsym();
            let
              fun getcon conslist =
                case getsym() of
                  Identupper str =>
                  ( nextsym();
                    app ( fn (id , _) => if id = str
                            then raise Duplicated_destructor
                            else () ) conslist;
                    let
                      val contype =
                        let
                          fun f ts =
                            let
                              fun g () = f (Tyun (ts,
                                     (gettype param env newt newtid)));
                            in
                              case getsym() of
                                Identupper _ => g() |
                                Identlower _ => g() |
                                Ident'     _ => g() |
                                Left_brace   => g() |
                                Absym        => g() |
                                Tyunitsym    => g() |
                                Boolsym      => g() |
                                           _ => ts
                            end
                        in
                          if getsym() = Tosym
                            then (nextsym();
                                  f (gettype param env newt newtid))
                            else Absurd
                        end;

                      val conslist' = conslist @ [(str, contype)];
                    in
                      if getsym() = Amper
                        then ( nextsym() ; getcon conslist' )
                        else conslist'
                    end
                  ) |
                  _ => raise Destructor_expected;

              val consts = if getsym() = Semicolon
                              then nil
                              else getcon nil;
              val conum = length consts;
            in
              if getsym() = Semicolon
                then
                  let
                    fun isinduc nil = ()
                      | isinduc ((_,ct)::cs) = (occurs newtref ct;
                        isinduc cs);
                    val isind = (isinduc consts ; false)
                                   handle Infinite_type => true;
                    val tpi = genintro newt (map (#2) consts)
                                   false result;
                  in
                    usedtypar param;
                    newtycon := Type
                      { name    = newtid,
                        induc   = isind,
                        coty    = true,
                        varlist = mktyvars param,
                        typiter = tpi,
                        typrec  = if isind then genintro newt
                                    (map (#2) consts) true result
                                    else tpi,
                        conlist = #1 ( fold
                          (fn ((str,conty) , (cl,pos)) =>
                             let
                               val trai' = gentrades newtref newtycon
                                               pos conum conty false;
                             in
                               (Constr ( ref
                                  { name = str,
                                    coty = true,
                                    ty   = Tyfun (newt , conty),
                                    trai = trai',
                                    trar = if isind
                                        then gentrades newtref newtycon
                                                   pos conum conty true
                                        else trai'
                                  } ) :: cl,
                                succ pos
                               )
                            end
                          ) consts (nil,0) )
                      };
                    newtref := Some (Tycon (newtycon,
                               map Tyvar (mktyvars param) ));
                    show_env (repl_ty newtycon env) newtid
                  end
                else raise Semicolon_expected
            end
          )
          else raise Equal_expected
      end;
  in
    nextsym();
    case getsym() of
       Identupper str => tydef str |
       Identlower str => tydef str |
                    _ => raise Tycon_expected
  end;

(* end of COTYPARS.SML ***********************************************)

