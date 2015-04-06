
(*********************************************************************)
(*                                                                   *)
(* SCANNER.SML - FUNCTIONS SCANNING THE TEXT BEFORE LEXICAL ANALYSIS *)
(*                                                                   *)
(*       Programmed in Standard ML by Tomasz Wierzbicki, 1992.       *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from LISTING.SML:                                              *)
(*       type character                                              *)
(*    from SOURCE.SML:                                               *)
(*       eot                = fn: unit -> bool                       *)
(*       getchar            = fn: unit -> character                  *)
(*       nextchar           = fn: unit -> unit                       *)
(*       con EOT            = - : exn                                *)
(* Exports:                                                          *)
(*       skip               = fn: unit -> unit                       *)
(*       comment            = fn: unit -> unit                       *)
(*       uppercase          = fn: character -> bool                  *)
(*       lowercase          = fn: character -> bool                  *)
(*       digit              = fn: character -> bool                  *)
(*       getalnum           = fn: unit -> string                     *)
(*       getstring          = fn: unit -> string                     *)
(*       con EOT_in_comment = - : exn                                *)
(*       con EOT_in_string  = - : exn                                *)
(*                                                                   *)
(*********************************************************************)

exception EOT_in_comment and EOT_in_string;

fun skip () =
   let
      fun white ch = ch = " " orelse ch = "\t" orelse ch = "\n";
   in
      if not ( eot() ) andalso white ( getchar() )
         then ( nextchar() ; skip() )
         else ()
   end;

fun comment () =
   ( if getchar() = "*"
        then ( nextchar();
               if getchar() = ")"
                  then nextchar()
                  else comment()
             )
        else ( nextchar() ; comment() )
   ) handle EOT => raise EOT_in_comment;

fun uppercase (ch : character) = ch >= "A" andalso ch <= "Z";
fun lowercase (ch : character) = ch >= "a" andalso ch <= "z";
fun digit     (ch : character) = ch >= "0" andalso ch <= "9";

fun getalnum () =
   let
      fun alfanum ch = uppercase ch orelse lowercase ch orelse
                       digit ch orelse ch = "'" orelse ch = "_";
      fun f s =
         if not ( eot() ) andalso alfanum ( getchar() )
            then let
                    val ch = getchar()
                 in
                    nextchar();
                    f (s ^ ch)
                 end
            else s
   in
      f ""
   end;

fun getstring () =
   let
      fun f s =
         let
            val ch = getchar();
         in
            nextchar();
            if ch = "\""
               then s
               else f (s ^ ch)
         end
            handle EOT => raise EOT_in_string;
   in
      f ""
   end;

(* end of SCANNER.SML ************************************************)

