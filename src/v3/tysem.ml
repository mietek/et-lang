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

let xf = Printf.sprintf
let pf = Printf.printf

let tycon n a = Tycon ({n_name = n; n_binding = None}, a)

let rec is_present v = function
  | Tycon (_, a) -> List.exists (is_present v) a
  | Tyvar x -> x = v
  | Tybox {box_value = Some x} -> is_present v x
  | Tybox {box_value = None} -> assert false

and is_positive v = function
  | Tycon ({n_binding = Some {tc_args = s}}, a) ->
    let rec f = function
      | Positive :: ss, a :: aa -> is_positive v a && f (ss, aa)
      | Negative :: ss, a :: aa -> is_negative v a && f (ss, aa)
      | Signless :: ss, a :: aa -> not (is_present v a) && f (ss, aa)
      | Bisigned :: ss, a :: aa -> f (ss, aa)
      | [], [] -> true
      | _ -> assert false
    in f (s, a)
  | Tyvar _ -> true
  | Tybox {box_value = Some x} -> is_positive v x
  | Tycon ({n_binding = None}, _) -> assert false
  | Tybox {box_value = None} -> assert false

and is_negative v = function
  | Tycon ({n_binding = Some {tc_args = s}}, a) ->
    let rec f = function
      | Positive :: ss, a :: aa -> is_negative v a && f (ss, aa)
      | Negative :: ss, a :: aa -> is_positive v a && f (ss, aa)
      | Signless :: ss, a :: aa -> not (is_present v a) && f (ss, aa)
      | Bisigned :: ss, a :: aa -> f (ss, aa)
      | [], [] -> true
      | _ -> assert false
    in f (s, a)
  | Tyvar x -> x <> v
  | Tybox {box_value = Some x} -> is_negative v x
  | Tycon ({n_binding = None}, _) -> assert false
  | Tybox {box_value = None} -> assert false

let tyvars_of t =
  let rec f m = function
    | Tycon (_, a) ->
      List.fold_left f m a
    | Tyvar x -> Stringset.add x m
    | Tybox {box_value = Some x} -> f m x
    | Tybox {box_value = None} -> assert false
  in Stringset.fold (fun x xs -> x :: xs) (f Stringset.empty t) []

let check_cdtors tvs cds =
  let test_ty m t =
    let test_tv m tv =
      if tv = "'@" then m 
      else
        try
          match Stringmap.find tv m with
          | Signless -> m
          | Positive ->
            if is_positive tv t then m
            else Stringmap.add tv Signless m
          | Negative ->
            if is_negative tv t then m
            else Stringmap.add tv Signless m
          | Bisigned ->
            match is_negative tv t, is_positive tv t with
            | true, true -> m
            | true, false -> Stringmap.add tv Negative m
            | false, true -> Stringmap.add tv Positive m
            | false, false -> Stringmap.add tv Signless m
        with Not_found -> 
          sorry (xf "unbound type variable %s" tv)
    in 
    List.fold_left test_tv m (tyvars_of t) 
  in 
  let add_bisigned m tv = Stringmap.add tv Bisigned m in
  let initial_map = List.fold_left add_bisigned Stringmap.empty tvs in
  let map = 
    List.fold_left (List.fold_left test_ty) initial_map cds in
  List.map (fun tv -> Stringmap.find tv map) tvs

(* return t[s := u], where s need not be type variable. *)
let big_subst t s u =
  let rec f = function
    | x when x = s -> u
    | Tycon (n, a) -> Tycon (n, List.map f a)
    | Tyvar _ as t -> t
    | Tybox {box_value = Some x} -> f x
    | Tybox {box_value = None} -> assert false
  in f t

let small_subst t v s = big_subst t (Tyvar v) s

let rec make_multi_arg_type ret = function
  | [] -> ret
  | x :: xs -> tycon "->" [x; make_multi_arg_type ret xs]

let pair env x y =
  let t = tycon "PAIR" [x; y] in
  let () = bind_ty env t in
  t

let rec plus = function
  | [] -> tycon "BOTTOM" []
  | [x] -> x
  | x1 :: x2 :: xs -> plus (tycon "UNION" [x1; x2] :: xs)

let rec count_args = function
  | Tycon ({n_name = "->"}, [t1; t2]) -> 1 + count_args t2
  | _ -> 0

(* (t1 -> t2) -> t[v := t1] -> t[v := t2] *)
let t2s = Pp.string_of_ty

(* suba x t = t['@/x] *)
let suba x t = small_subst t "'@" x

(* suba x t = t['#/x] *)
let subh x t = small_subst t "'#" x

type mon_env = {
  me_env  : Env.env;
  me_tcf  : mon_env -> ty -> tycon -> ty list -> var -> var -> term;
  me_atcf : mon_env -> ty -> tycon -> ty list -> var -> var -> term;
  me_t1   : ty;
  me_t2   : ty;
}

let rec tc_apply e = function
  | (tv :: tvs, arg :: args) -> tc_apply (small_subst e tv arg) (tvs, args)
  | ([], []) -> e
  | _ -> assert false

let get_value me name =
  match Env.get_value me.me_env name with
  | {val_semantics = Shorthand t} -> t
  | {val_semantics = Alias t} -> t
  | x -> Value x
 
let bound env t =
  let () = bind_ty env t in t

let rec tcf_it env t x a z y =
  let n (name, args) =  
    let cons (vr, e) =
      let e_inst = (tc_apply e (x.tc_tyvars, a)) in
      let e' = suba (subh env.me_t2 t) e_inst in
      app [mon env e'; rf z; rf vr]
    in
    let vars = var_vect args in
    lambda (List.map fst vars) (app (Value name :: (List.map cons vars)))
  in
  app (Value x.tc_it :: rf y :: (List.map n x.tc_cons))

and atcf_it env t x a z y = 
  let n (name, args) =  
    let cons (vr, e) =
      let e = suba (subh env.me_t1 t) (tc_apply e (x.tc_tyvars, a)) in
      app [amon env e; rf z; rf vr]
    in
    let vars = var_vect args in
    lambda (List.map fst vars) (app (Value name :: (List.map cons vars)))
  in
  app (Value x.tc_it :: rf y :: (List.map n x.tc_cons))

and tcf_rec env t x a z y =
  let n (name, args) =  
    let cons (vr, e) =
      let tt1 = subh env.me_t1 t in
      let tt2 = subh env.me_t2 t in
      let e' = suba tt2 (tc_apply e (x.tc_tyvars, a)) in
      let e'' = suba (Tyvar "'#") (tc_apply e (x.tc_tyvars, List.map (subh env.me_t1) a)) in
      app [mon env e'; rf z; app [mon {env with me_t1 = (pair env.me_env tt1 tt2); 
                                                me_t2 = tt2} e'';
                                  get_value env "snd"; 
                                  rf vr]]
    in
    let vars = var_vect args in
    lambda (List.map fst vars) (app (Value name :: (List.map cons vars)))
  in
  app (Value x.tc_rec :: rf y :: (List.map n x.tc_cons))

and atcf_rec env t x a z y =
  let n (name, args) =  
    let cons (vr, e) =
      let tt1 = subh env.me_t1 t in
      let tt2 = subh env.me_t2 t in
      let e' = suba tt1 (tc_apply e (x.tc_tyvars, a)) in
      let e'' = suba (Tyvar "'#") (tc_apply e (x.tc_tyvars, List.map (subh env.me_t2) a)) in
      app [amon env e'; rf z; app [mon {env with me_t1 = pair env.me_env tt2 tt1;
                                                 me_t2 = tt1} e'';
                                   get_value env "snd"; 
                                   rf vr]]
    in
    let vars = var_vect args in
    lambda (List.map fst vars) (app (Value name :: (List.map cons vars)))
  in
  app (Value x.tc_it :: rf y :: (List.map n x.tc_cons))

and tcf_coit env t c a z y =
  let n (name, args) = 
    let x = gen_var () in
    let sub e = suba (subh env.me_t1 t) (tc_apply e (c.tc_tyvars, a)) in
    let t' = bound env.me_env (plus (List.map sub args)) in
    lambda [x] (app [mon env t'; rf z; app [Value name; rf x]])
  in
  app ((Value c.tc_it :: (List.map n c.tc_cons)) @ [rf y])

and atcf_coit env t c a z y = 
  let n (name, args) = 
    let x = gen_var () in
    let sub e = suba (subh env.me_t1 t) (tc_apply e (c.tc_tyvars, a)) in
    let t' = bound env.me_env (plus (List.map sub args)) in
    lambda [x] (app [amon env t'; rf z; app [Value name; rf x]])
  in
  app ((Value c.tc_it :: (List.map n c.tc_cons)) @ [rf y])

and tcf_corec env t c a z y =
  let n (name, args) = 
    let x = gen_var () in
    let sub e = suba (subh env.me_t1 t) (tc_apply e (c.tc_tyvars, a)) in
    let sub' e = suba (Tyvar "'#") (tc_apply e (c.tc_tyvars, List.map (subh env.me_t2) a)) in
    let tt1 = subh env.me_t1 t in
    let tt2 = subh env.me_t2 t in
    let env' = {env with me_t1 = tt1; 
                         me_t2 = bound env.me_env (tycon "UNION" [tt1; tt2])} in
    let p' = bound env.me_env (plus (List.map sub' args)) in
    let t' = bound env.me_env (plus (List.map sub args)) in
    lambda [x] (app [mon env' p'; 
                     get_value env "Inr"; 
                     (app [mon env t'; rf z; app [Value name; rf x]])])
  in
  app ((Value c.tc_rec :: (List.map n c.tc_cons)) @ [rf y])

and atcf_corec env t c a z y =
  let n (name, args) = 
    let x = gen_var () in
    let sub e = suba (subh env.me_t1 t) (tc_apply e (c.tc_tyvars, a)) in
    let sub' e = suba (Tyvar "'#") (tc_apply e (c.tc_tyvars, List.map (subh env.me_t1) a)) in
    let tt1 = subh env.me_t1 t in
    let tt2 = subh env.me_t2 t in
    let env' = {env with me_t1 = tt2; 
                         me_t2 = bound env.me_env (tycon "UNION" [tt2; tt1])} in
    let p' = bound env.me_env (plus (List.map sub' args)) in
    let t' = bound env.me_env (plus (List.map sub args)) in
    lambda [x] (app [mon env' p'; 
                     get_value env "Inr"; 
                     (app [amon env t'; rf z; app [Value name; rf x]])])
  in
  app ((Value c.tc_rec :: (List.map n c.tc_cons)) @ [rf y])


and mon env t =
  let () = 
    if !debug then 
      pf "starting mon (%s->%s, %s)\n" (t2s env.me_t1) (t2s env.me_t2) (t2s t)  
  in
  let res =
    if is_present "'#" t then
      match t with
      | Tyvar k -> 
        let () = assert (k = "'#") in 
        let z = gen_var () in
        lambda [z] (rf z)
      | Tybox {box_value = Some x} -> mon env x
      | Tybox {box_value = None} -> assert false
      | Tycon ({n_name = "->"}, [r1; r2]) ->
        let z = gen_var () in
        let y = gen_var () in
        let x = gen_var () in
        lambda [z; y; x] (app [mon env r2; rf z;
                               app [rf y; app [amon env r1; rf z; rf x]]])
      | Tycon ({n_binding = Some x}, a) -> 
        let z = gen_var () in
        let y = gen_var () in
        lambda [z; y] (env.me_tcf env t x a z y)
      | Tycon ({n_binding = None}, _) -> assert false
    else
      let z = gen_var () in
      let y = gen_var () in
      lambda [z; y] (rf y)
  in 
  let () = 
    if !debug then
      pf "mon (%s->%s, %s) = %s\n" (t2s env.me_t1) (t2s env.me_t2) (t2s t) 
                                   (Pp.string_of_term res) 
  in res

and amon env t =
  let () = 
    if !debug then 
      pf "starting amon (%s->%s, %s)\n" (t2s env.me_t1) (t2s env.me_t2) (t2s t)  
  in
  let res =
    if is_present "'#" t then
      match t with
      | Tyvar k -> assert false
      | Tybox {box_value = Some x} -> amon env x
      | Tybox {box_value = None} -> assert false
      | Tycon ({n_name = "->"}, [r1; r2]) ->
        let z = gen_var () in
        let y = gen_var () in
        let x = gen_var () in
        lambda [z; y; x] (app [amon env r2; rf z; 
                                     app [rf y; 
                                          app [mon env r1; rf z; rf x]]])
      | Tycon ({n_binding = Some x}, a) -> 
        let z = gen_var () in
        let y = gen_var () in
        lambda [z; y] (env.me_atcf env t x a z y)
      | Tycon ({n_binding = None}, _) -> assert false
    else
      let z = gen_var () in
      let y = gen_var () in
      lambda [z; y] (rf y)
  in
  let () = 
    if !debug then
      pf "amon (%s->%s, %s) = %s\n" (t2s env.me_t1) (t2s env.me_t2) (t2s t) 
                                    (Pp.string_of_term res) 
  in res


let print_type tc =
  if tc.tc_is_cotype then (
    pf "codatatype %s\n" tc.tc_name;
    List.iter (fun (v, _) -> print_val "des   " v) tc.tc_cons;
    print_val "coiter" tc.tc_it;
    (match tc.tc_rec.val_semantics with
     | Alias (Value v) -> pf "corec  %s = %s\n" tc.tc_rec.val_name v.val_name
     | _ -> print_val "corec " tc.tc_rec);
    List.iter (fun r -> pf "comp   %s\n" (Pp.string_of_rule r)) tc.tc_rules
  ) else (
    pf "datatype %s\n" tc.tc_name;
    List.iter (fun (v, _) -> print_val "con " v) tc.tc_cons;
    print_val "iter" tc.tc_it;
    (match tc.tc_rec.val_semantics with
     | Alias (Value v) -> pf "rec  %s = %s\n" tc.tc_rec.val_name v.val_name
     | _ -> print_val "rec " tc.tc_rec);
    List.iter (fun r -> pf "comp %s\n" (Pp.string_of_rule r)) tc.tc_rules
  );
  pf "\n"

let add_type env n tv ctors =
  let self = tycon n (List.map (fun tv -> Tyvar tv) tv) in
  let is_inductive = ref false in
  let subst_self t =
    let t' = big_subst t self (Tyvar "'@") in
    let () = bind_ty env t' in
    let () = if is_present "'@" t' then is_inductive := true in
    let () = if is_positive "'@" t' then () 
             else sorry "inductive datatype must not be negative" in
    t'
  in
  let ess = List.map (fun c -> List.map subst_self c.cd_args) ctors in
  let tc = {tc_name = n; 
            tc_is_cotype = false;
            tc_args = check_cdtors tv ess;
            tc_cons = [];
            tc_it = Env.dummy_value;
            tc_rec = Env.dummy_value;
            tc_tyvars = tv;
            tc_rules = [];
            tc_outdated = false} in
  let make_conval {cd_name = n; cd_args = a} = 
    let t = make_multi_arg_type self a in
    let con = {val_name = n; val_ty = t; val_semantics = Constructor tc} in
    con
  in
  let convals = List.map make_conval ctors in
  let env = Env.add_tycon env tc in
  let env = List.fold_left Env.add_value env convals in
  let () = List.iter (fun v -> bind_ty env v.val_ty) convals in
  let () = tc.tc_cons <- List.map2 (fun v e -> (v, e)) convals ess in

  (* Iterator. *)
  let rec find_fresh_tv n =
    if List.mem (tyvar_no n) tv then find_fresh_tv (n + 1)
    else tyvar_no n
  in
  let fresh_tv_name = find_fresh_tv 0 in
  let fresh_tv = Tyvar fresh_tv_name in
  
  let elim_type (_, a) = 
    make_multi_arg_type fresh_tv (List.map (fun t -> small_subst t "'@" fresh_tv) a) 
  in
  let it_type = make_multi_arg_type fresh_tv (self :: List.map elim_type tc.tc_cons) in
  let () = bind_ty env it_type in
  let it = {val_name = "_" ^ n ^ "it"; 
            val_ty = it_type; 
            val_semantics = Eliminator tc} in
  let () = tc.tc_it <- it in
  let env = Env.add_value env it in
  
  (* Computational rules. *)
  let vs = var_vect tc.tc_cons in
  let comp_rule (v, (name, es)) =
    let uij (u, e) =
      let z = gen_var () in
      let e = suba (Tyvar "'#") e in
      let me = 
        {me_env = env; 
         me_tcf = tcf_it;
         me_atcf = atcf_it;
         me_t1 = self; 
         me_t2 = fresh_tv}
      in
      app [mon me e;
           lambda [z] (app (Value it :: rf z :: 
                                      (List.map (fun (v, _) -> rf v) vs)));
           rf u]
    in
    let us = var_vect es in
    let t = lambda (List.map fst vs) (app (rf v :: List.map uij us)) in
    make_rule it name (List.map (fun (v, _) -> v) us) t
  in
  let () = tc.tc_rules <- List.map comp_rule vs in

  (* Recursor. *)
  let rec_ =
    if !is_inductive then
      let rec_in_ty = tycon "PAIR" [self; fresh_tv] in
      let elim_type (_, a) = 
        make_multi_arg_type fresh_tv (List.map (fun t -> small_subst t "'@" rec_in_ty) a) 
      in
      let rec_type = make_multi_arg_type fresh_tv (self :: List.map elim_type tc.tc_cons) in
      let () = bind_ty env rec_type in
      let rec_ = {val_name = "_" ^ n ^ "rec"; 
                  val_ty = rec_type; 
                  val_semantics = Eliminator tc} in
      let () = tc.tc_rec <- rec_ in
      let env = Env.add_value env rec_ in

      (* Comp/rec. *)
      let pair = Env.get_value env "Pair" in
      let vs = var_vect tc.tc_cons in
      let comp_rule (v, (name, es)) =
        let uij (u, e) =
          let z = gen_var () in
          let e = suba (Tyvar "'#") e in
          let me = 
             {me_env = env; 
              me_tcf = tcf_rec;
              me_atcf = atcf_rec;
              me_t1 = self; 
              me_t2 = rec_in_ty}
          in
          app [mon me e;
               lambda [z] (app [Value pair; 
                                rf z; 
                                (app (Value rec_ :: rf z :: (List.map (fun (v, _) -> rf v) vs)))]);
               rf u]
        in
        let us = var_vect es in
        let t = lambda (List.map fst vs) (app (rf v :: List.map uij us)) in
        make_rule rec_ name (List.map (fun (v, _) -> v) us) t
      in
      let () = tc.tc_rules <- tc.tc_rules @ List.map comp_rule vs in
      rec_
    else
      {val_name = "_" ^ n ^ "rec"; val_ty = it.val_ty; val_semantics = Alias (Value it)}
  in

  let () = tc.tc_rec <- rec_ in
  let env = Env.add_value env rec_ in
  
  let () = if not !quiet then print_type tc in
  env

(* Transform:
     Foo to t1 t2 t3
   into:
     Foo to (t1 -> 'a) -> ((t2 -> 'a) -> ((t3 -> 'a) -> 'a))
 *)
let fix_dtors tvs dtors =
  let has_multi =
    List.exists (fun d -> List.length d.cd_args > 1) dtors
  in
  if has_multi then
    let aint_present tv =
      not (List.exists (fun d -> List.exists (is_present tv) d.cd_args) dtors)
    in
    let free_tv =
      try List.find aint_present tvs
      with Not_found ->
        sorry "cannot find free type variable, but several arguments used"
    in
    List.map (fun d ->
      {d with cd_args =
        if List.length d.cd_args > 1 then
          [List.fold_right
            (fun t acc -> tycon "->" [tycon "->" [t; Tyvar free_tv]; acc])
            d.cd_args (Tyvar free_tv)]
        else d.cd_args})
      dtors
  else dtors
    


let add_cotype env n tv dtors =
  let dtors = fix_dtors tv dtors in
  let self = tycon n (List.map (fun tv -> Tyvar tv) tv) in
  let is_inductive = ref false in
  let subst_self t =
    let t' = big_subst t self (Tyvar "'@") in
    let () = bind_ty env t' in
    let () = if is_present "'@" t' then is_inductive := true in
    let () = if is_positive "'@" t' then () 
             else sorry "inductive codatatype must not be negative" in
    t'
  in
  let ess = List.map (fun c -> List.map subst_self c.cd_args) dtors in
  let tc = {tc_name = n; 
            tc_is_cotype = true;
            tc_args = check_cdtors tv ess;
            tc_cons = [];
            tc_it = Env.dummy_value;
            tc_rec = Env.dummy_value;
            tc_tyvars = tv;
            tc_rules = [];
            tc_outdated = false} in
  let make_desval {cd_name = n; cd_args = a} = 
    {val_name = n; 
     val_ty = tycon "->" [self; plus a]; 
     val_semantics = Eliminator tc}
  in
  let desvals = List.map make_desval dtors in
  let env = Env.add_tycon env tc in
  let env = List.fold_left Env.add_value env desvals in
  let () = List.iter (fun v -> bind_ty env v.val_ty) desvals in
  let () = tc.tc_cons <- List.map2 (fun v e -> (v, e)) desvals ess in

  (* Iterator. *)
  let rec find_fresh_tv n =
    if List.mem (tyvar_no n) tv then find_fresh_tv (n + 1)
    else tyvar_no n
  in
  let fresh_tv_name = find_fresh_tv 0 in
  let fresh_tv = Tyvar fresh_tv_name in
  
  let intro_type (_, a) = 
    tycon "->" [fresh_tv; plus (List.map (fun t -> small_subst t "'@" fresh_tv) a)]
  in
  let it_type = make_multi_arg_type (tycon "->" [fresh_tv; self]) 
                                    (List.map intro_type tc.tc_cons) in
  let () = bind_ty env it_type in
  let it = {val_name = "_" ^ n ^ "ci"; 
            val_ty = it_type; 
            val_semantics = Constructor tc} in
  let () = tc.tc_it <- it in
  let env = Env.add_value env it in
  
  (* Computational rules. *)
  let vs = var_vect tc.tc_cons in
  let comp_rule (v, (name, es)) =
    let u = gen_var () in
    let es = List.map (suba (Tyvar "'#")) es in
    let me = 
      {me_env = env; 
       me_tcf = tcf_coit;
       me_atcf = atcf_coit;
       me_t1 = fresh_tv; 
       me_t2 = self}
    in
    let t =
      app [mon me (plus es); 
           app (Value it :: List.map (fun (v, _) -> rf v) vs);
           app [rf v; rf u]] in
    make_rule name it ((List.map (fun (v, _) -> v) vs) @ [u]) t
  in
  let () = tc.tc_rules <- List.map comp_rule vs in

  (* Recursor. *)
  let rec_ =
    if !is_inductive then
      let rec_in_ty = tycon "UNION" [self; fresh_tv] in
      let intro_type (_, a) = 
        tycon "->" [fresh_tv; plus (List.map (fun t -> small_subst t "'@" rec_in_ty) a)]
      in
      let rec_type = make_multi_arg_type (tycon "->" [fresh_tv; self]) 
                                         (List.map intro_type tc.tc_cons) in
      let () = bind_ty env rec_type in
      let rec_ = {val_name = "_" ^ n ^ "cr"; 
                  val_ty = rec_type; 
                  val_semantics = Constructor tc} in
      let () = tc.tc_rec <- rec_ in
      let env = Env.add_value env rec_ in

      (* Comp/rec. *)
      let when_ = Env.get_value env "_UNIONit" in
      let vs = var_vect tc.tc_cons in
      let comp_rule (v, (name, es)) =
        let z = gen_var () in
        let x = gen_var () in
        let u = gen_var () in
        let es = List.map (suba (Tyvar "'#")) es in
        let me = 
           {me_env = env; 
            me_tcf = tcf_corec;
            me_atcf = atcf_corec;
            me_t1 = rec_in_ty; 
            me_t2 = self}
        in
        let t =
          app [mon me (plus es); 
               lambda [z] (app [Value when_; rf z; lambda [x] (rf x);
                                app (Value rec_ :: List.map (fun (v, _) -> rf v) vs)]);
               app [rf v; rf u]] in
        make_rule name rec_ ((List.map (fun (v, _) -> v) vs) @ [u]) t
      in
      let () = tc.tc_rules <- tc.tc_rules @ List.map comp_rule vs in
      rec_
    else
      {val_name = "_" ^ n ^ "cr"; val_ty = it.val_ty; val_semantics = Alias (Value it)}
  in

  let () = tc.tc_rec <- rec_ in
  let env = Env.add_value env rec_ in
  
  let () = if not !quiet then print_type tc in
  env

