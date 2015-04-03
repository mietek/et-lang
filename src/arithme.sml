
(*********************************************************************)
(*                                                                   *)
(*        ARITHME.SML - some additional arithmetic functions.        *)
(*                                                                   *)
(*       Programmed in Standard ML by Tomasz Wierzbicki, 1992.       *)
(*                                                                   *)
(*                                                                   *)
(* Imports: none                                                     *)
(* Exports:                                                          *)
(*       isqr        = fn: int -> int                                *)
(*       odd         = fn: int -> bool                               *)
(*       even        = fn: int -> bool                               *)
(*       halve       = fn: int -> int                                *)
(*       succ        = fn: int -> int                                *)
(*       pred        = fn: int -> int                                *)
(*       iszero      = fn: int -> bool                               *)
(*       infix 2 eqv = fn: bool * bool -> bool                       *)
(*                                                                   *)
(*********************************************************************)

fun isqr n : int = n * n;

fun odd  n = n mod 2 = 1;
fun even n = n mod 2 = 0;

fun halve n = n div 2;

fun succ n = n + 1;
fun pred n = n - 1;

fun iszero n = n = 0;

infix 2 eqv;
fun a eqv b = (not a orelse b) andalso (not b orelse a);

(* end of ARITHME.SML ************************************************)

