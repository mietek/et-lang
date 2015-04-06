
(*********************************************************************)
(*                                                                   *)
(* IPLL.SML  - THE INFERENTIAL PROGRAMMING LANGUAGE AND LOGIC SYSTEM *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from ENVIRON.SML:                                              *)
(*       abstype environment with                                    *)
(*          emptyenv   = - : environment                             *)
(*    from LISTING.SML:                                              *)
(*       start_output  = fn: string -> unit                          *)
(*       stop_output   = fn: unit -> unit                            *)
(*    from PARSER.SML:                                               *)
(*       parse         = fn: string -> environment -> unit           *)
(*       con Use_error = - : exn                                     *)
(* Exports:                                                          *)
(*       ipl          = fn: unit -> unit                             *)
(*       ipl_clear    = fn: unit -> unit                             *)
(*       ipl_env      = - : environment ref                          *)
(*       ipl_run      = fn: string -> string -> environment -> unit  *)
(*                                                                   *)
(*********************************************************************)

val ipl_env = ref emptyenv;

fun ipl_clear () = ipl_env := emptyenv;

fun ipl_run infile outfile env =
   ( start_output outfile;
     ( ipl_env := parse infile env handle Use_error => () );
     stop_output()
   );

fun ipl () = ipl_run "" "" (! ipl_env);

(* end of IPLL.SML ***************************************************)

