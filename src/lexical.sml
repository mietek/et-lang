
(*********************************************************************)
(*                                                                   *)
(*                LEXICAL.SML  - THE LEXICAL ANALYSIS                *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from LISTING.SML:                                              *)
(*       type character                                              *)
(*    from SCANNER.SML:                                              *)
(*       skip       = fn: unit -> unit                               *)
(*       comment    = fn: unit -> unit                               *)
(*       lowercase  = fn: character -> bool                          *)
(*       uppercase  = fn: character -> bool                          *)
(*       getalnum   = fn: unit -> string                             *)
(*       getstring  = fn: unit -> string                             *)
(*    from SOURCE.SML:                                               *)
(*       open_text  = fn: string -> unit                             *)
(*       close_text = fn: unit -> unit                               *)
(*       eot        = fn: unit -> bool                               *)
(*       getchar    = fn: unit -> character                          *)
(*       nextchar   = fn: unit -> unit                               *)
(* Exports:                                                          *)
(*       datatype symbol                                             *)
(*       start_text = fn: string -> unit                             *)
(*       stop_text  = fn: unit -> unit                               *)
(*       getsym     = fn: unit -> symbol                             *)
(*       nextsym    = fn: unit -> unit                               *)
(*                                                                   *)
(*********************************************************************)

datatype symbol = Amper | Bar | Colon | Equal | Plus | Semicolon |
                  Star | Left_brace | Right_brace | Arrow | Thinarrow |
                  Circle | Absym | Boolsym | Case0sym | Case1sym |
                  Cotysym | Delsym | Elsesym | Endsym | Exitsym |
                  Falsesym | Fromsym | Fstsym | Funsym | Ifsym |
                  Inlsym | Inrsym | Insym | Letsym | Showsym | Sndsym |
                  Thensym | Tosym | Truesym | Typesym | Tyunitsym |
                  Usesym | Valsym | Whensym | Strval of string |
                  Identupper of string | Identlower of string |
                  Ident' of string | Ident_ of string | Unknown |
                  End_of_text;

local
   val cursym = ref Unknown;
in  
   fun nextsym () =
      ( skip();
        if eot() 
           then cursym := End_of_text 
           else
              case getchar() of
                 "&" => ( nextchar() ; cursym := Amper       ) |
                 "|" => ( nextchar() ; cursym := Bar         ) |
                 "," => ( nextchar() ; cursym := Colon       ) |
                 ";" => ( nextchar() ; cursym := Semicolon   ) |
                 "+" => ( nextchar() ; cursym := Plus        ) |
                 "*" => ( nextchar() ; cursym := Star        ) |
                 ")" => ( nextchar() ; cursym := Right_brace ) |
                 "(" => ( nextchar();
                          if not ( eot() )
                             then case getchar() of
                                "*" => (nextchar(); comment();
                                        nextsym()) |
                                ")" => (nextchar(); cursym := Circle) |
                                 _  => cursym := Left_brace
                             else cursym := Left_brace
                        ) |
                 "=" => ( nextchar();
                          if not ( eot() ) andalso getchar() = ">"
                             then ( nextchar() ; cursym := Arrow )
                             else cursym := Equal 
                        ) |                    
                 "-" => ( nextchar() ;
                          if not ( eot() ) andalso getchar() = ">"
                             then ( nextchar() ; cursym := Thinarrow )
                             else cursym := Unknown
                        ) |
                 "{" => ( nextchar() ;
                          if not ( eot() ) andalso getchar() = "}"
                             then ( nextchar() ; cursym := Absym )
                             else cursym := Unknown
                        ) |
                 "\""=> ( nextchar();
                          cursym := Strval ( getstring() ) 
                        ) |
                 "'" => ( nextchar();
                          cursym := Ident' ( getalnum() ) 
                        ) | 
                 "_" => ( nextchar();
                          cursym := Ident_ ( getalnum() ) 
                        ) |
                  _  => if uppercase ( getchar() )
                           then cursym :=
                              let
                                 val str = getalnum();
                              in
                                 case str of
                                    "BOOL"  => Boolsym   |
                                    "UNIT"  => Tyunitsym |
                                    "False" => Falsesym  |
                                    "True"  => Truesym   |
                                    "Inl"   => Inlsym    |
                                    "Inr"   => Inrsym    |
                                          _ => Identupper str
                              end
                           else
                              if lowercase ( getchar() )
                                 then cursym := 
                                    let
                                       val str = getalnum();
                                    in
                                       case str of
                                          "case0"      => Case0sym |
                                          "case1"      => Case1sym |
                                          "codatatype" => Cotysym  |
                                          "datatype"   => Typesym  |
                                          "del"        => Delsym   |
                                          "else"       => Elsesym  |
                                          "end"        => Endsym   |
                                          "exit"       => Exitsym  |
                                          "fn"         => Funsym   |
                                          "from"       => Fromsym  |
                                          "fst"        => Fstsym   |
                                          "if"         => Ifsym    |
                                          "in"         => Insym    |
                                          "let"        => Letsym   |
                                          "show"       => Showsym  |
                                          "snd"        => Sndsym   |
                                          "then"       => Thensym  |
                                          "to"         => Tosym    |
                                          "use"        => Usesym   |
                                          "val"        => Valsym   |
                                          "when"       => Whensym  |
                                          _ => Identlower str
                                    end
                                 else (nextchar() ; cursym := Unknown)
      ); (* nextsym *)
                                                 
   fun getsym () = ! cursym;
end;    

fun start_text name = ( open_text name ; nextsym() );
val stop_text = close_text;
                          
(* end of LEXICAL.SML ************************************************)
                                       
