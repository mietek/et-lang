
(*********************************************************************)
(*                                                                   *)
(*              TYPARS.SML - THE TYPE DEFINITION PARSER              *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from ARITHME.SML:                                              *)
(*       succ         = fn: int -> int                               *)
(*    from ENVIRON.SML:                                              *)
(*       abstype environment with                                    *)
(*          repl_ty   = fn: tycon ref -> environment -> environment  *)
(*    from GENELIM.SML:                                              *)
(*       genelim      = fn: typex -> typex list -> bool -> typex ->  *)
(*                          typex                                    *)
(*       splitconty   = fn: typex -> typex list                      *)
(*    from GENTRACON.SML:                                            *)
(*       gentracon    = fn: tyvar ref -> tycon ref -> int -> int ->  *)
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
(*    from UNIFY.SML:                                                *)
(*       occurs       = fn: tyvar ref -> typex -> unit               *)
(*       con Infinite_type          = - : exn                        *)
(* Exports:                                                          *)
(*       con Tycon_expected         = - : exn                        *)
(*       con Constructor_expected   = - : exn                        *)
(*       con Duplicated_constructor = - : exn                        *)
(*       typars       = fn: environment -> environment               *)
(*                                                                   *)
(*********************************************************************)
                                
exception Tycon_expected
      and Constructor_expected 
      and Duplicated_constructor;

fun typars env =
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
                            then raise Duplicated_constructor
                            else () ) conslist;
                    let                   
                      val contype = 
                        let
                          fun f ts =
                            let
                              val ts' = 
                                gettype param env newt newtid::ts
                            in
                              case getsym() of
                                Identupper _ => f ts' |
                                Identlower _ => f ts' |
                                Ident'     _ => f ts' |
                                Left_brace   => f ts' |
                                Absym        => f ts' |
                                Tyunitsym    => f ts' |
                                Boolsym      => f ts' |
                                           _ => ts'
                            end
                        in
                          if getsym() = Fromsym
                            then (nextsym() ; f nil)
                            else nil
                        end;

                      val conslist' = conslist @
                             [(str,revfold Tyfun contype newt)];
                    in                   
                      if getsym() = Bar
                        then ( nextsym() ; getcon conslist' )
                        else conslist'
                    end   
                  ) |
                  _ => raise Constructor_expected;

              val consts = if getsym() = Semicolon
                              then nil
                              else getcon nil;
              val conum = length consts;
            in       
              if getsym() = Semicolon
                then
                  let
                    fun isinduc nil = ()
                      | isinduc ((_,ct)::cs) =
                       (app (fn t => occurs newtref t) (splitconty ct);
                        isinduc cs)
                    val isind = (isinduc consts ; false)
                                   handle Infinite_type => true;
                    val tpi = genelim newt (map (#2) consts)
                                   false result;
                  in
                    usedtypar param;
                    newtycon := Type
                      { name    = newtid,
                        induc   = isind,
                        coty    = false,
                        varlist = mktyvars param,
                        typiter = tpi,
                        typrec  = if isind then genelim newt
                                    (map (#2) consts) true result
                                    else tpi,
                        conlist = #1 ( fold 
                          (fn ((str,conty) , (cl,pos)) =>
                             let
                               val trai' = gentracon newtref newtycon
                                               pos conum conty false;
                             in
                               (Constr ( ref
                                  { name = str,
                                    coty = false,
                                    ty   = conty,
                                    trai = trai',
                                    trar = if isind
                                        then gentracon newtref newtycon
                                                   pos conum conty true
                                        else trai'
                                  } ) :: cl,
                                succ pos
                               )
                             end
                          )
                          consts (nil,0) )      
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

(* end of TYPARS.SML *************************************************)

