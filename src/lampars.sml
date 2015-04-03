
(*********************************************************************)
(*                                                                   *)
(*             LAMPARS.SML - THE PARSER OF LAMBDA TERMS              *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from ARITHME.SML:                                              *)
(*       succ           = fn: int -> int                             *)
(*    from ENVIRON.SML:                                              *)
(*       con Undef_type = - : exn                                    *)
(*       abstype environment with                                    *)
(*          find_param  = fn: string -> environment -> term          *)
(*          find_con    = fn: string -> environment -> constr        *)
(*          find_ty     = fn: string -> environment -> tycon         *)
(*          ins_param   = fn: string -> environment -> environment   *)
(*    from ITEREC.SML:                                               *)
(*       iter           = fn: ('st -> 'st) -> 'st -> int -> 'st      *)
(*    from LEXICAL.SML:                                              *)
(*       datatype symbol                                             *)
(*       getsym         = fn: unit -> symbol                         *)
(*       nextsym        = fn: unit -> unit                           *)
(*    from TYLAM.SML:                                                *)
(*       datatype term and constr and tycon                          *)
(* Exports:                                                          *)
(*       lambdaterm     = fn: environment -> term                    *)
(*       and exceptions listed below                                 *)
(*                                                                   *)
(*********************************************************************)

exception Right_brace_expected
      and Parameter_expected
      and Arrow_expected
      and Undef_elim
      and Unknown_elim_kind
      and In_expected
      and End_expected
      and Term_expected
      and Semicolon_expected
      and Equal_expected
      and Identifier_expected
      and Then_expected
      and Else_expected
      and Intro_not_exist
      and Elim_not_exist;

fun lambdaterm env =
  let
    fun atomic () =
      ( case getsym() of
          Identlower str =>
            let
              val trm = find_param str env;
            in
              nextsym() ; trm
            end |
          Identupper str =>
            let
              val trm = Constructor ( find_con str env )
            in
              nextsym() ; trm
            end |
          Ident_ str =>
            let
              val len = size str;
              val trm =
                (if len > 2 andalso
                     substring (str , len-2 , 2) = "cr"
                   then
                     let
                       val tyre as ref (Type {coty = ct , ...}) =
                         find_ty (substring (str , 0 , len-2)) env;
                     in
                       if ct
                         then Recursor tyre
                         else raise Intro_not_exist
                     end
                 else if len > 2 andalso
                     substring (str , len-2 , 2) = "ci"
                   then
                     let
                       val tyre as ref (Type {coty = ct , ...}) =
                         find_ty (substring (str , 0 , len-2)) env;
                     in
                       if ct
                         then Iterator tyre
                         else raise Intro_not_exist
                     end
                 else if len > 3 andalso
                     substring (str , len-3 , 3) = "rec"
                   then
                     let
                       val tyre as ref (Type {coty = ct , ...}) =
                         find_ty (substring (str , 0 , len-3)) env;
                     in
                       if ct
                         then raise Elim_not_exist
                         else Recursor tyre
                     end
                 else if len > 2 andalso
                     substring (str , len-2 , 2) = "it"
                   then
                     let
                       val tyre as ref (Type {coty = ct , ...}) =
                         find_ty (substring (str , 0 , len-2)) env;
                     in
                       if ct
                         then raise Elim_not_exist
                         else Iterator tyre
                     end
                 else raise Unknown_elim_kind
                ) handle Undef_type => raise Undef_elim;
            in
              nextsym() ; trm
            end |
          Truesym  => ( nextsym() ; True  ) |
          Falsesym => ( nextsym() ; False ) |
          Fstsym   => ( nextsym() ; Fst   ) |
          Sndsym   => ( nextsym() ; Snd   ) |
          Inlsym   => ( nextsym() ; Inl   ) |
          Inrsym   => ( nextsym() ; Inr   ) |
          Whensym  => ( nextsym() ; When  ) |
          Case0sym => ( nextsym() ; Case0 ) |
          Case1sym => ( nextsym() ; Case1 ) |
          Circle   => ( nextsym() ; Unit  ) |
          Left_brace =>
            ( nextsym();
              let
                val trm = lambdaterm env;
              in
                if getsym() = Right_brace
                  then ( nextsym() ; trm )
                  else raise Right_brace_expected
              end
            ) |
          Funsym =>
            ( nextsym();
              let
                fun getparam lev env =
                  case getsym() of
                    Identlower str =>
                      ( nextsym();
                        getparam (succ lev) (ins_param str env)
                      ) |
                    _ => (lev , env);

                val (lev , env') = getparam 0 env;
              in
                if lev = 0
                  then raise Parameter_expected
                  else
                    if getsym() <> Arrow
                      then raise Arrow_expected
                      else ( nextsym();
                             iter (fn t => Lambda t)
                                  (lambdaterm env') lev
                           )
              end
            ) |
          Letsym =>
            ( nextsym();
              let
                fun locdec env =
                  let
                    val env' =
                      ( nextsym();
                        case getsym() of
                          Identlower str =>
                            ( nextsym();
                              if getsym() = Equal
                                then
                                ( nextsym();
                                  let
                                    val trm = lambdaterm env;
                                  in
                                    if getsym() = Semicolon
                                      then repl_val str trm env
                                      else raise Semicolon_expected
                                  end
                                )
                                else raise Equal_expected
                            ) |
                          _ => raise Identifier_expected
                      );
                  in
                    nextsym();
                    case getsym() of
                      Valsym => locdec env' |
                      Insym  => ( nextsym() ; env' ) |
                           _ => raise In_expected
                  end;

                val trm = lambdaterm (locdec env);
              in
                if getsym() = Endsym
                  then ( nextsym() ; trm )
                  else raise End_expected
              end
            ) |
          Ifsym =>
            ( nextsym();
              let
                val t1 = lambdaterm env;
              in
                if getsym() = Thensym
                  then
                  ( nextsym();
                    let
                      val t2 = lambdaterm env;
                    in
                      if getsym() = Elsesym
                        then
                        ( nextsym();
                          Conditional (t1 , t2 , lambdaterm env)
                        )
                        else raise Else_expected
                    end
                  )
                  else raise Then_expected
              end
            ) |
          _ => raise Term_expected
      ); (* atomic *)

    fun appl () =
      let
        fun f trm =
          case getsym() of
            Identlower _ => f ( Application (trm , atomic()) ) |
            Identupper _ => f ( Application (trm , atomic()) ) |
            Ident_     _ => f ( Application (trm , atomic()) ) |
            Left_brace   => f ( Application (trm , atomic()) ) |
            Funsym       => f ( Application (trm , atomic()) ) |
            Letsym       => f ( Application (trm , atomic()) ) |
            Truesym      => f ( Application (trm , atomic()) ) |
            Falsesym     => f ( Application (trm , atomic()) ) |
            Fstsym       => f ( Application (trm , atomic()) ) |
            Sndsym       => f ( Application (trm , atomic()) ) |
            Circle       => f ( Application (trm , atomic()) ) |
            Case0sym     => f ( Application (trm , atomic()) ) |
            Case1sym     => f ( Application (trm , atomic()) ) |
            Inlsym       => f ( Application (trm , atomic()) ) |
            Inrsym       => f ( Application (trm , atomic()) ) |
            Whensym      => f ( Application (trm , atomic()) ) |
                       _ => trm;
      in
        f ( atomic() )
      end;

    fun pairexp () =
      let
        fun f trm =
          if getsym() = Colon
            then ( nextsym() ; f (Pair (trm , appl())) )
            else trm;
      in
        f ( appl() )
      end;

    fun eqexp () =
      let
        fun f trm =
          if getsym() = Equal
            then ( nextsym() ; f (Equality (trm , pairexp())) )
            else trm;
      in
        f ( pairexp() )
      end;
  in
    eqexp()
  end; (* lambdaterm *)

(* end of LAMPARS.SML ************************************************)

