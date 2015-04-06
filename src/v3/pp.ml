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

let pf = Printf.printf
let xf = Printf.sprintf

let string_of_ty t =
  let rec nf = function
    | Tyvar s -> s
    | Tycon ({n_name = "->"}, [t1; Tycon ({n_name = "->"}, _) as t2]) ->
      f t1 ^ " -> " ^ nf t2
    | Tycon ({n_name = "->"}, [t1; t2]) ->
      f t1 ^ " -> " ^ f t2
    | Tycon ({n_name = "UNION"}, [t1; Tycon ({n_name = "UNION"}, _) as t2]) ->
      f t1 ^ " + " ^ nf t2
    | Tycon ({n_name = "UNION"}, [t1; t2]) ->
      f t1 ^ " + " ^ f t2
    | Tycon ({n_name = "PAIR"}, [t1; Tycon ({n_name = "PAIR"}, _) as t2]) ->
      f t1 ^ " * " ^ nf t2
    | Tycon ({n_name = "PAIR"}, [t1; t2]) ->
      f t1 ^ " * " ^ f t2
    | Tycon ({n_name = "BOTTOM"}, []) ->
      "{}"
    | Tycon (n, a) ->
      let name = 
        match n.n_binding with
        | Some {tc_name = c; tc_outdated = false} -> c
        | Some {tc_name = c; tc_outdated = true} -> "?" ^ c
        | None -> "." ^ n.n_name
      in
      begin
        match a with
        | [] -> name
        | _ -> 
          let a' =  List.map f a in
          name ^ " " ^ String.concat " " a'
      end
    | Tybox {box_value = Some x} -> nf x
    | Tybox {box_value = None; box_set = s; box_id = i} -> 
      xf "[%d@%d]" i s
  and f t =
    match t with
    | Tybox {box_value = None} 
    | Tycon (_, [])
    | Tyvar _ -> nf t
    | Tybox {box_value = Some x} -> f x
    | _ -> "(" ^ nf t ^ ")"
  in nf t

let tyvar_no n =
  if n <= 25 then String.make 1 (Char.chr (Char.code 'z' - n))
  else "x" ^ string_of_int n
  
let rec print_pterm t =
  match t.v with
  | T_app (t1, t2) ->
    pf "(";
    print_pterm t1;
    pf " ";
    print_pterm t2;
    pf ")"
  | T_abs (v, t) ->
    let rec print_abs vars t =
      match t.v with
      | T_abs (v, t) ->
        print_abs (vars ^ " " ^ v) t
      | _ ->
        pf "%s. " vars;
        print_pterm t
     in
     print_abs ("\\" ^ v) t
  | T_ref s -> 
    pf "%s" s
  | T_let (bindings, t) ->
    let print_binding (n, t) =
      pf "  val %s = " n;
      print_pterm t;
      pf ";\n"
    in
    pf "let\n";
    List.iter print_binding bindings;
    pf "in\n  ";
    print_pterm t;
    pf "\nend"
  
let print_decl d = 
  let print_cd sep1 sep2 c =
    let tys = (String.concat " " (List.map string_of_ty c.cd_args)) in
    pf "  %s %s %s %s\n" sep1 c.cd_name sep2 tys
  in
  let () = 
    match d.v with
    | Value_binding (s, t) ->
      pf "val %s = " s;
      print_pterm t
    | Term t ->
      print_pterm t
    | Eq_test (t1, t2) ->
      print_pterm t1;
      pf " = ";
      print_pterm t2
    | Type (n, tv, ctors) ->
      pf "datatype %s %s =\n" n (String.concat " " tv);
      List.iter (print_cd "|" "from") ctors
    | Cotype (n, tv, dtors) ->
      pf "codatatype %s %s =\n" n (String.concat " " tv);
      List.iter (print_cd "&" "to") dtors
    | Exit_cmd -> pf "exit"
    | Set_cmd s -> pf "set \"%s\"" s
    | Show_cmd s -> pf "show %s" s
    | Use_cmd s -> pf "use \"%s\"" s
  in
  pf ";\n";
  flush stdout


(* Lambda printing *)
type ctx = 
  {
    c_env    : string Intmap.t;
    c_in_abs : bool;
    c_var_no : int;
  }

let proj_kind = function
  | Abs (k, Abs (_, Var (k'))) when k == k' -> 1
  | Abs (_, Abs (k, Var (k'))) when k == k' -> 2
  | _ -> 0

let dummy_value name =
  { val_name = name;
    val_semantics = Dummy;
    val_ty = Tyvar "dummy";
  }
    
let rec f ctx = function
  | Value {val_name = "_UNIONit"} -> "when"
  | Value {val_name = "_UNITit"} -> "case1"
  | Value {val_name = "_BOTTOMit"} -> "case0"

  | App (App (Value {val_name = "_PAIRit"}, t1), t2) when proj_kind t2 > 0 ->
    let name = if proj_kind t2 == 1 then "fst" else "snd" in
    f ctx (App (Value (dummy_value name), t1))
  
  | App (App (App (Value {val_name = "_BOOLit"}, t1), t2), t3) ->
    "(if " ^ (f ctx t1) ^ " then " ^
             (f ctx t2) ^ " else " ^
             (f ctx t3) ^ ")"

  | App (App (Value {val_name = "Pair"}, t1), t2) ->
    (f ctx t1) ^ ", " ^ (f ctx t2)

  | App (t1, t2) ->
    let s1 = f ctx t1 in
    let s2 = f ctx t2 in
    begin
      match t2 with
      | App (_, _) | Abs (_, _) -> s1 ^ " (" ^ s2 ^ ")"
      | _ -> s1 ^ " " ^ s2
    end
  | Abs (k, t) -> 
    let v = tyvar_no ctx.c_var_no in
    let sep = if ctx.c_in_abs then " " else "\\" in
    let ctx = {ctx with c_env = Intmap.add k v ctx.c_env;
                        c_var_no = ctx.c_var_no + 1} in
    begin
      match t with
      | Abs (_, _) -> sep ^ v ^ (f {ctx with c_in_abs = true} t)
      | _ -> sep ^ v ^ ". " ^ (f {ctx with c_in_abs = false} t)
    end
  | Var k when Intmap.mem k ctx.c_env -> Intmap.find k ctx.c_env
  (*| Var k when Intmap.mem k ctx.c_env -> xf "%s[%d]" (Intmap.find k ctx.c_env) k*)
  | Var k -> xf "?%d" k
  | Value v -> v.val_name

let init_ctx = {c_env = Intmap.empty; c_var_no = 0; c_in_abs = false}

let string_of_term = f init_ctx

let string_of_rule r =
  let addv ctx k =
    {ctx with c_env = Intmap.add k (tyvar_no ctx.c_var_no) ctx.c_env;
              c_var_no = ctx.c_var_no + 1}
  in
  let ctx = List.fold_left addv init_ctx r.r_vars in
  let vars = List.map (fun k -> Intmap.find k ctx.c_env) r.r_vars in
  xf "%s (%s %s) = %s" 
     r.r_elim.val_name 
     r.r_ctor.val_name 
     (String.concat " " vars)
     (f ctx r.r_value)
    
