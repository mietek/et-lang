(*
 * Copyright (c) 2003 The University of Wroclaw.
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
open Tyutil
open Lambda

let pf = Printf.printf

(* Compile pterm [t], that is already typed. *)
let compile genv t =
  let rec f env t =
    match t.v with
    | T_app (t1, t2) -> 
      App (f env t1, f env t2)
    | T_abs (v, t) ->
      let k = gen_var () in
      let env = Stringmap.add v (rf k) env in
      lambda [k] (f env t)
    | T_ref s when Stringmap.mem s env -> Stringmap.find s env
    | T_ref s -> 
      begin
        match Env.get_value genv s with
        | {val_semantics = Shorthand t}
        | {val_semantics = Alias t} -> t
        | x -> Value x
      end
    | T_let (bindings, t) ->
      let add e (n, v) = Stringmap.add n (f env v) e in
      f (List.fold_left add env bindings) t
  in f Stringmap.empty t

let show env name =
  let show_tycon n = 
    if n <> "->" then Tysem.print_type (Env.get_tycon env n) 
  in
  let show_value n = 
    let v = Env.get_value env n in
    match v.val_semantics with
    | Alias t ->
      if name <> "" then begin
        pf "alias %s = %s;\n" v.val_name (Pp.string_of_term t);
        print_val "val" v;
        pf "\n"
      end
    | Shorthand t ->
      pf "val %s = %s;\n" v.val_name (Pp.string_of_term t);
      print_val "val" v;
      pf "\n"
    | Constructor _ -> if name <> "" then print_val "con" v
    | Eliminator _ -> if name <> "" then print_val "des" v
    | Dummy -> assert false
    in
  match name with
  | "" ->
    List.iter show_tycon (Env.tycon_names env);
    List.iter show_value (Env.value_names env)
  | _ ->
    (try show_tycon name with Unlocated_error _ -> ());
    (try show_value name with Unlocated_error _ -> ())
  
let eval_decl env d =
  match d.v with
  | Value_binding (n, m) ->
    let ty = Typing.type_pterm env m in
    let vv = {val_name = n; 
              val_ty = ty; 
              val_semantics = Shorthand (compile env m)} in
    let () = print_val "val" vv in
    Env.add_value env vv
  | Term m ->
    let ty = Typing.type_pterm env m in
    let norm = nf (compile env m) in
    let () = pf "%s : %s\n" (Pp.string_of_term norm) (Pp.string_of_ty ty) in
    env
  | Type (n, tv, tors) -> Tysem.add_type env n tv tors
  | Cotype (n, tv, tors) ->  Tysem.add_cotype env n tv tors
  | Eq_test (t1, t2) ->
    let ty1 = Typing.type_pterm env t1 in
    let ty2 = Typing.type_pterm env t2 in
    let n1 = nf (compile env t1) in
    let n2 = nf (compile env t2) in
    let r = 
      if eq n1 n2 then "True"
      else "False"
    in
    if !debug then
      pf "%s : %s =? %s : %s  = %s\n" 
         (Pp.string_of_term n1) (Pp.string_of_ty ty1)
         (Pp.string_of_term n2) (Pp.string_of_ty ty2)
         r;
    pf "%s : BOOL\n" r;
    env
    
  | Exit_cmd -> exit 0
  | Show_cmd n -> show env n; env
  | Use_cmd _ -> env
  | Set_cmd "debug" ->
    debug := true; env
  | Set_cmd "nodebug" ->
    debug := false; env
  | Set_cmd "quiet" ->
    quiet := true; env
  | Set_cmd "noquiet" ->
    quiet := false; env
  | Set_cmd x ->
    pf "unknown set: %s\n" x; env

