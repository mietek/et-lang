
(*********************************************************************)
(*                                                                   *)
(*              SOURCE.SML - THE SOURCE TEXT INTERFACE               *)
(*                                                                   *)
(*       Programmed in Standard ML by Tomasz Wierzbicki, 1992.       *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from LISTING.SML:                                              *)
(*       type character                                              *)    
(*       copy       = fn: bool -> character -> unit                  *)
(*       prompt     = ? : string                                     *)
(* Exports:                                                          *)
(*       open_text  = fn: string -> unit                             *)
(*       close_text = fn: unit -> unit                               *)
(*       eot        = fn: unit -> bool                               *)
(*       getchar    = fn: unit -> character                          *)
(*       nextchar   = fn: unit -> unit                               *)
(*       sweep      = fn: unit -> unit                               *)
(*       con EOT    = - : exn                                        *)
(*       con Source = - : exn                                        *)
(*       con SOpen  = - : exn                                        *)
(*    and standard exception Io may be raised while running theese   *)
(*    functions                                                      *)
(*                                                                   *)
(*********************************************************************)

exception EOT and Source and SOpen;

local
   val streams     = ref nil;
   val snames      = ref nil;        
   val interactive = ref true;
in
   fun open_text name = 
      ( if name = ""
           then ( streams := std_in :: (! streams);       
                  out ( "Opening interactive session\n" ^ prompt )
                )
           else ( streams := open_in name :: (! streams);
                  out ( "Opening " ^ name ^ "\n" )
                ) handle Io _ => raise SOpen;
        snames      := name :: (! snames);
        interactive := name = ""
      );  

   fun close_text () = 
      if ! snames = nil
         then raise Source
         else       
            ( if ! interactive
                 then out "Closing interactive session\n"     
                 else ( out ( "Closing " ^ hd (! snames) ^ "\n" );
                        close_in ( hd (! streams) )
                      ) handle Io _ => ();
              snames  := tl (! snames);     
              streams := tl (! streams);
              interactive := ( (! snames) = nil orelse 
                               hd (! snames) = ""
                             )
            );

   fun eot () = end_of_stream ( hd (! streams) )
                   handle Hd => raise Source;

   fun getchar () : character =
      if eot ()
         then raise EOT
         else lookahead ( hd (! streams) );

   fun nextchar () = 
      if eot ()
         then raise EOT
         else copy (! interactive) (input (hd (! streams) , 1));

   fun sweep () =
      if ! interactive
         then let 
                 fun f () = if getchar() = "\n"
                               then ()
                               else ( nextchar() ; f() );
              in                                              
                 f()
              end
         else ();
end;

(* end of SOURCE.SML *************************************************)

