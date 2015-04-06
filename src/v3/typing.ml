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

let xf = Printf.sprintf
let pf = Printf.printf

type ty_ctx = 
  {c_env : Env.env;
   c_lev : int;
   c_varcnt : int;
   c_locals : ty Stringmap.t}

let gen_tyvar ctx =
  let n = ctx.c_varcnt in
  ({ctx with c_varcnt = n + 1}, tyvar_no n)

let rec ctx_map f ctx = function
  | x :: xs ->
    let (ctx, x') = f ctx x in
    let (ctx, xs') = ctx_map f ctx xs in
    (ctx, x' :: xs')
  | [] -> (ctx, [])

let rec unbox ctx =
  function
    | Tycon (n, a) -> 
      let (ctx, a') = ctx_map unbox ctx a in
      (ctx, Tycon (n, a'))
    | Tybox {box_value = Some (Tyvar _ as t)} -> (ctx, t)
    | Tybox {box_value = Some x} -> unbox ctx x
    | Tybox b as a ->
      let lev = b.box_set in
      (*let () = assert (lev <= ctx.c_lev) in*)
      if ctx.c_lev <= lev then
        let (ctx, tv) = gen_tyvar ctx in
        let t = Tyvar tv in
        let () = b.box_value <- Some t in
        (ctx, t)
      else
        (ctx, a)
    | Tyvar _ -> assert false

let rec norm = function
  | Tybox {box_value = Some x} -> norm x
  | t -> t

let sorry m = raise (Unlocated_error m)

let empty_box =
  let cnt = ref 0 in
  fun ctx ->
    let () = incr cnt in
    Tybox {box_set = ctx.c_lev; 
           box_value = None; 
           box_id = !cnt}

let freshen ctx t =
  let rec f m = function
    | Tycon (n, a) ->
      let (m, a') = ctx_map f m a in
      (m, Tycon (n, a'))
    | Tyvar v ->
      if Stringmap.mem v m then
        (m, Stringmap.find v m)
      else
        let b = empty_box ctx in
        let m = Stringmap.add v b m in
        (m, b)
    | Tybox {box_value = Some x} -> 
      f m x
    | Tybox _ as t -> (m, t)
  in
  let (_, t) = f Stringmap.empty t in
  t

let subst b t =
  (* Used to remember nodes we already visited, to speed things up.  This cuts
     down exponential complexity to linear in some cases.  *)
  let h = Hashtbl.create 16 in
  let rec f = function
    | Tycon (_, a) -> List.iter f a
    | Tyvar _ -> ()
    | Tybox bb -> 
      if Hashtbl.mem h bb.box_id then ()
      else
        let () = Hashtbl.add h bb.box_id () in
        if b == bb then
          sorry ("cyclic type in " ^ Pp.string_of_ty t ^ 
                 " (cycle to " ^ Pp.string_of_ty (Tybox b) ^ ")")
        else
          match bb.box_value with
          | Some x -> f x
          | None -> ()
  in
  let () = f t in
  b.box_value <- Some t

let rec lift_level f =
  function
    | Tycon (_, a) ->
      List.iter (lift_level f) a
    | Tyvar _ -> ()
    | Tybox ({box_value = Some x} as t) ->
      f t;
      lift_level f x
    | Tybox x -> f x
    
let rec unify t1 t2 =
  (* let () = pf "unify: %s =?= %s\n" (Pp.string_of_ty t1) (Pp.string_of_ty t2) in  *)
  match t1, t2 with
  | Tycon ({n_binding = Some c1}, a1), 
    Tycon ({n_binding = Some c2}, a2) when (c1 == c2) ->
    let () = assert (List.length a1 == List.length a2) in
    List.iter2 unify a1 a2
  | Tyvar a1, Tyvar a2 when (a1 = a2) -> ()
  | Tybox _, _ | _, Tybox _ ->
    (match norm t1, norm t2 with
     | Tybox b1, Tybox b2 ->
       if b1 == b2 then ()
       else
         let lev = min b1.box_set b2.box_set in
         let () = b1.box_set <- lev in
         let () = b2.box_set <- lev in
         subst b1 (Tybox b2)
     | Tybox b, t | t, Tybox b ->
       lift_level (fun b' -> b'.box_set <- min b'.box_set b.box_set) t;
       subst b t
     | t1, t2 -> unify t1 t2)
  | Tycon ({n_binding = None}, _), _ 
  | _, Tycon ({n_binding = None}, _) -> assert false
  | _ -> sorry ("type clash of " ^ (Pp.string_of_ty t1) ^ " with " ^
                (Pp.string_of_ty t2))

let app_ty ctx t1 t2 =
  let t = Tycon ({n_name = "->"; n_binding = None}, [t1; t2]) in
  let () = bind_ty ctx.c_env t in
  t

let rec type_term ctx m =
  match m.v with
  | T_app (m1, m2) ->
    let t1 = type_term ctx m1 in
    let t2 = type_term ctx m2 in
    let b = empty_box ctx in
    let () = unify (app_ty ctx t2 b) t1 in
    b
    
  | T_abs (v, m) ->
    let b = empty_box ctx in
    let ctx' = {ctx with c_locals = Stringmap.add v b ctx.c_locals} in
    let t = type_term ctx' m in
    app_ty ctx b t
    
  | T_ref v ->
    if Stringmap.mem v ctx.c_locals then
      Stringmap.find v ctx.c_locals
    else
      let vl = Env.get_value ctx.c_env v in
      freshen ctx vl.val_ty
    
  | T_let (bindings, m) ->
    let gctx = {ctx with c_lev = ctx.c_lev + 1} in
    let add ctx (v, m) =
      let ty = type_term_ub gctx m in
      let vv = {val_name = v; val_ty = ty; val_semantics = Dummy} in
      let () = print_val "   val" vv in
      {ctx with c_env = Env.add_value ctx.c_env vv}
    in
    let ctx' = List.fold_left add gctx bindings in
    type_term {ctx' with c_lev = ctx.c_lev} m

and type_term_ub ctx m =
  let ty = type_term ctx m in
  let (_, ty) = unbox ctx ty in
  ty

let type_pterm env t =
  let ctx = {c_env = env; 
             c_locals = Stringmap.empty; 
             c_lev = 0;
             c_varcnt = 0} in
  type_term_ub ctx t
