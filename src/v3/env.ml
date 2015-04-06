(*
 * Copyright (c) 2002, 2003 The University of Wroclaw.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgement:
 *      This product includes software developed by the University of
 *      Wroclaw and its contributors.
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE UNIVERSITY AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *)
open Ast
open Util

type env = 
  {e_tycons : tycon Stringmap.t;
   e_values : value Stringmap.t}

let add_tycon e t =
  let () = 
    if Stringmap.mem t.tc_name e.e_tycons then
      (Stringmap.find t.tc_name e.e_tycons).tc_outdated <- true
  in {e with e_tycons = Stringmap.add t.tc_name t e.e_tycons}

let add_value e t =
  {e with e_values = Stringmap.add t.val_name t e.e_values}

let get_tycon e n =
  try 
    Stringmap.find n e.e_tycons
  with Not_found -> 
    raise (Unlocated_error ("unbound type constructor `" ^ n ^ "'"))

let get_value e n =
  try 
    Stringmap.find n e.e_values
  with Not_found -> 
    raise (Unlocated_error ("unbound value `" ^ n ^ "'"))

let null_env =
  {e_tycons = Stringmap.empty; 
   e_values = Stringmap.empty}

let dummy_value = {val_name = "???"; val_ty = Tyvar "'?"; val_semantics = Dummy}

let value_names env = Stringmap.fold (fun n _ l -> n :: l) env.e_values []
let tycon_names env = Stringmap.fold (fun n _ l -> n :: l) env.e_tycons []

let empty_env = 
  List.fold_left add_tycon null_env 
    [{tc_name = "->"; 
      tc_is_cotype = false;
      tc_args = [Negative; Positive]; 
      tc_cons = []; 
      tc_tyvars = ["'a"; "'b"];
      tc_it = {dummy_value with val_name = "_FUNit"};
      tc_rec = {dummy_value with val_name = "_FUNrec"};
      tc_rules = [];
      tc_outdated = false}]

