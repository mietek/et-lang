
(*********************************************************************)
(*                                                                   *)
(*                    PARSER.SML - THE IPLL PARSER                   *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports (no exceptions listed here):                              *)
(*    from ENVIRON.SML:                                              *)
(*       abstype environment with                                    *)
(*          show_env = fn: environment -> string -> environment      *)
(*          repl_val = fn: string -> term -> environment ->          *)
(*                         environment                               *)
(*          del_val  = fn: string -> environment -> environment      *)
(*    from LAMPARS.SML:                                              *)
(*       lambdaterm  = fn: environment -> term                       *)
(*    from LAMTERM.SML:                                              *)
(*       printerm    = fn: int -> term -> unit                       *)
(*    from LEXICAL.SML:                                              *)
(*       datatype symbol                                             *)
(*       start_text  = fn: string -> unit                            *)
(*       stop_text   = fn: unit -> unit                              *)
(*       getsym      = fn: unit -> symbol                            *)
(*       nextsym     = fn: unit -> unit                              *)
(*    from LISTING.SML                                               *)
(*       out         = fn: string -> unit                            *)
(*    from SOURCE.SML:                                               *)
(*       sweep       = fn: unit -> unit                              *)
(*    from TYLAM.SML:                                                *)
(*       datatype term and typex                                     *)
(*    from TYPARS.SML:                                               *)
(*       typars = fn: environment -> environment                     *)
(*    from TYPEX.SML:                                                *)
(*       printype    = fn: typex -> unit                             *)
(*    from TYPOFTERM.SML:                                            *)
(*       typofterm   = fn: term -> typex                             *)
(* Exports:                                                          *)
(*       parse       = fn: string -> environment -> environment      *)
(*       con Empty_filename  = - : exn                               *)
(*       con String_expected = - : exn                               *)
(*       con Use_error       = - : exn                               *)
(*                                                                   *)
(*********************************************************************)

exception Empty_filename and String_expected and Use_error;

fun parse filename environ =
  let
    fun program env =
      let
        fun ermes str =
          ( sweep();
            out ("Error: " ^ str ^ "\n" );
            if filename = ""
              then (true , env)
              else raise Use_error
          );

        val (cont , env') =
          ( case getsym() of
              Semicolon => ( out "" ; (true , env) ) |
              End_of_text => (false , env) |
              Exitsym =>
                ( nextsym();
                  if getsym() = Semicolon
                    then (false , env)
                    else raise Semicolon_expected
                ) |
              Delsym =>
              let
                fun f ss =
                  case getsym() of
                    Identlower str => ( nextsym() ; f (str::ss) ) |
                    _ => ss;
              in
                nextsym();
                case getsym() of
                  Identlower _ =>
                    let
                      val ss = f nil;
                    in
                      if getsym() = Semicolon
                        then ( true,
                               fold ( fn (str,env) =>
                                      ( out ("deleting " ^ str ^ "\n");
                                        del_val str env
                                      )
                                    ) ss env
                             )
                        else raise Semicolon_expected
                    end |
                  _ => raise Identifier_expected
              end |
              Usesym =>
                ( nextsym();
                  case getsym() of
                    Strval str =>
                      if str = ""
                        then raise Empty_filename
                        else
                          ( nextsym();
                            if getsym() = Semicolon
                              then (true , parse str env)
                              else raise Semicolon_expected
                          ) |
                    _ => raise String_expected
                ) |
              Showsym =>
                ( nextsym();
                  case getsym() of
                     Identlower str =>
                        ( nextsym();
                          if getsym() = Semicolon
                             then (true , show_env env str)
                             else raise Semicolon_expected
                        ) |
                     Identupper str =>
                        ( nextsym();
                          if getsym() = Semicolon
                             then (true , show_env env str)
                             else raise Semicolon_expected
                        ) |
                     Semicolon => (true , show_env env "") |
                     _ => raise Semicolon_expected
                ) |
              Typesym => (true , typars env) |
              Cotysym => (true , cotypars env) |
              Valsym =>
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
                                then
                                   let
                                     val ty = typofterm trm;
                                     val env' = repl_val str trm env;
                                   in
                                     out ( "val " ^ str ^ " : " );
                                     printype ty;
                                     out "\n";
                                     (true , env')
                                   end
                                else raise Semicolon_expected
                            end
                          )
                          else raise Equal_expected
                      ) |
                    _ => raise Identifier_expected
                ) |
              _ => (* expression *)
                let
                  val trm = lambdaterm env;
                in
                  if getsym() = Semicolon
                    then
                      let
                        val ty = typofterm trm;
                        val env' = repl_val "it" trm env;
                      in
                        printerm 0 (eval trm);
                        out " : ";
                        printype ty;
                        out "\n";
                        (true , env')
                      end
                    else raise Semicolon_expected
                end
          ) handle
              EOT_in_comment    => ermes "end of text inside comment" |
              EOT_in_string      => ermes "end of text inside string" |
              Unbound_value       => ermes "unbound value identifier" |
              Right_brace_expected              => ermes ") expected" |
              Parameter_expected        => ermes "parameter expected" |
              Arrow_expected                   => ermes "=> expected" |
              In_expected                    => ermes "'in' expected" |
              End_expected                  => ermes "'end' expected" |
              Term_expected                  => ermes "term expected" |
              Semicolon_expected                => ermes "; expected" |
              Equal_expected                    => ermes "= expected" |
              Identifier_expected      => ermes "identifier expected" |
              Then_expected                => ermes "'then' expected" |
              Else_expected                => ermes "'else' expected" |
              Infinite_type                  => ermes "infinite type" |
              Type_mismatch                  => ermes "type mismatch" |
              Undef_constr           => ermes "undefined constructor" |
              Undef_type        => ermes "undefined type constructor" |
              Undef_elim        => ermes "eliminator of unknown type" |
              Intro_not_exist => ermes "datatype has no introductors" |
              Elim_not_exist => ermes "codatatype has no eliminators" |
              Unknown_elim_kind => ermes "unknown kind of eliminator" |
              Empty_filename                => ermes "empty filename" |
              String_expected                  => ermes "\" expected" |
              Unknown_type_param    => ermes "unknown type parameter" |
              Bad_typaram             => ermes "wrong type parameter" |
              Typaram_expected     => ermes "type parameter expected" |
              Unused_typaram         => ermes "unused type parameter" |
              Type_expected                  => ermes "type expected" |
              Tycon_expected     => ermes "type constructor expected" |
              Constructor_expected    => ermes "constructor expected" |
              Duplicated_constructor =>ermes "duplicated constructor" |
              Destructor_expected      => ermes "destructor expected" |
              Duplicated_destructor  => ermes "duplicated destructor" |
              Bad_occurrence      => ermes "negative type occurrence" |
              Use_error                      => if filename = ""
                                                  then (true , env)
                                                  else raise Use_error;
      in
        if cont
          then ( nextsym() ; program env' )
          else env'
      end; (* program *)

    val environ' =
      ( start_text filename;
        program environ
      ) handle SOpen     => ( out ( "Failure during " ^
                                    "opening source file\n"
                                  );
                              raise Use_error
                            ) |
               Use_error => ( stop_text() ; raise Use_error ) |
               Io _      => ( out "File operation failure\n" ;
                              stop_text() ; raise Use_error
                            ) |
               ?         => ( out ("IPLL system failure - contact " ^
                                   "with the programmer\n");
                              stop_text() ; raise Use_error
                            );
  in
    stop_text();
    environ'
  end; (* parse *)

(* end of PARSER.SML *************************************************)

