
(*********************************************************************)
(*                                                                   *)
(*             LISTING.SML - THE OUTPUT STREAM INTERFACE             *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from IPLL.SYS:                                                 *)
(*       ipll_ver     = ? : string                                   *)
(* Exports:                                                          *)
(*       type character                                              *)
(*       start_output = fn: string -> unit                           *)
(*       stop_output  = fn: unit -> unit                             *)
(*       copy         = fn: bool -> character -> unit                *)
(*       out          = fn: string -> unit                           *)
(*       prompt       = ? : string                                   *)
(*       contprompt   = ? : string                                   *)
(*                                                                   *)
(*********************************************************************)

type character  = string;

val prompt      = "+ ";
val contprompt  = "= ";

local
   val greeting = "\n\n   THE INFERENTIAL PROGRAMMING LANGUAGE " ^
                  "INTERPRETER  " ^ ipll_ver ^ "\n" ^
                  "               (c) Technical University of " ^
                  "Wroclaw, 1992, 1993\n\n";
   val goodbye  = "IPL exit - returning to SML\n\n";
   val stream   = ref std_out;
   val is_std   = ref true;
   val newline  = ref false;
   val copying  = ref true;
   fun write s  = output (! stream , s);
in
   fun start_output name =
      ( is_std := name = "";
        if ! is_std
           then ()
           else stream := open_out name;
        write greeting
      );

   fun stop_output () =
      ( write goodbye;
        if ! is_std
           then ()
           else ( close_out (! stream) ; stream := std_out )
      );

   fun copy console (ch : character) =
      if console
         then
            if ! copying
               then if ch = "\n"
                       then write contprompt
                       else ()
               else ( if ch = "\n"
                         then write prompt
                         else ();
                      copying := true;
                      newline := true
                    )
         else
            if ! copying
               then ( if ! newline
                         then ( newline := false ; write contprompt )
                         else ();
                      write ch;
                      if ch = "\n"
                         then newline := true
                         else ()
                    )
               else ( newline := false;
                      write prompt;
                      copying := true;
                      if ch = "\n"
                         then ()
                         else write ch
                    );

   fun out str =
      ( (* if ! copying
           then write "\n"
           else (); *)
        copying := false;
        newline := true;
        write str
      );
end;

(* end of LISTING.SML ************************************************)

