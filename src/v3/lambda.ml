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

let xf = Printf.sprintf
let pf = Printf.printf

type var = int

let gen_var =
  let cnt = ref 1 in
  fun () -> 
    assert (!cnt < 1000000000); incr cnt; !cnt

let rf x = Var x

let rec lambda x y =
  match x with
  | [] -> y
  | x :: xs -> Abs (x, lambda xs y)

let rec app = function
  | [] -> assert false
  | [x] -> x
  | x1 :: x2 :: xs -> app (App (x1, x2) :: xs)
  
let var_vect lst = List.map (fun x -> gen_var (), x) lst

let freshen t =
  let rec f map = function
  | App (t1, t2) -> 
    App (f map t1, f map t2)
  | Abs (k, t) -> 
    let k' = gen_var () in 
    Abs (k', f (Intmap.add k k' map) t)
  | Var n when Intmap.mem n map -> Var (Intmap.find n map)
  | t -> t
  in f Intmap.empty t

let complete_development t =
  let rec f sub = function
    | App (Abs (k, t1), t2) ->
      let (_, t2') = f sub t2 in
      (true, snd (f (Intmap.add k t2' sub) (freshen t1)))

    | App (Value ({val_semantics = Eliminator tc} as ev), t) ->
      let (did, t) = f sub t in
      let rec find_ctor acc = function 
        | App (t, t') -> find_ctor (t' :: acc) t
        | Value ({val_semantics = Constructor tc'} as cv) when tc == tc' ->
          let our_rule r = r.r_elim == ev && r.r_ctor == cv in
          Some (List.find our_rule tc.tc_rules, acc)
        | _ -> None
      in
      begin
        match find_ctor [] t with
        | Some (r, args) when List.length args == List.length r.r_vars ->
          let rec add_subst sub = function
            | (v :: vs, a :: args) -> add_subst (Intmap.add v a sub) (vs, args)
            | ([], []) -> sub
            | _ -> assert false
          in
          let sub = add_subst Intmap.empty (r.r_vars, args) in
          (true, snd (f sub (freshen r.r_value)))
        | _ -> (did, App (Value ev, t))
      end
          
    | App (t1, t2) ->
      let (did1, t1') = f sub t1 in
      let (did2, t2') = f sub t2 in
      (did1 || did2, App (t1', t2'))
      
    | Var k when Intmap.mem k sub -> (false, Intmap.find k sub)
    
    | Abs (k, t) ->
      let rec is_fv = function
        | App (t1, t2) -> is_fv t1 || is_fv t2
        | Abs (n, t) -> n != k && is_fv t
        | Var n -> n == k
        | Value _ -> false
      in
      let (did, t') = f sub t in
      begin
        match t' with
        | App (t, Var k') when k == k' && not (is_fv t) -> (true, t)
        | _ -> (did, Abs (k, t'))
      end
      
    | (Var _ as t) | (Value _ as t) -> (false, t)
  in f Intmap.empty t 

let nf t =
  let rec f t =
(*    let () = pf "bn: %s -> " (Pp.string_of_lambda t) in*)
    let (didsth, t') = complete_development t in
(*    let () = pf "%s\n" (Pp.string_of_lambda t') in *)
    if didsth then f t' else t'
  in f t

exception Different

let eq t1 t2 =
  let rec f m = function
    | App (t1, t2), App (t1', t2') ->
      f (f m (t1, t1')) (t2, t2')
    | Abs (k, t), Abs (k', t') ->
      f (Intmap.add k' k m) (t, t')
    | Var k, Var k' when k == Intmap.find k' m -> m
    | Value v, Value v' when v == v' -> m
    | _ -> raise Different
  in
  try
    let _ = f Intmap.empty (t1, t2) in
    true
  with Different -> false
  
let make_rule elim con vars t =
  {r_vars = vars; 
   r_elim = elim; 
   r_ctor = con; 
   r_value = nf t}
