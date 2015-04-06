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

(* Location in source file. *)
type location = {mutable loc_file: string;
                 mutable loc_char: int;
                 mutable loc_line: int}
                 
type tyvar = string

type 'a located = {v : 'a; l : location}

type raw_decl =
  | Value_binding of string * pterm
  | Term of pterm
  | Type of string * tyvar list * cdtor list
  | Cotype of string * tyvar list * cdtor list
  | Exit_cmd
  | Show_cmd of string
  | Use_cmd of string
  | Set_cmd of string
  | Eq_test of pterm * pterm
and cdtor = 
  {cd_name : string;
   cd_args : ty list}
and decl = raw_decl located

and raw_pterm =
  | T_app of pterm * pterm
  | T_abs of string * pterm
  | T_ref of string
  | T_let of (string * pterm) list * pterm

and pterm = raw_pterm located

and 'a name = {n_name : string;
               mutable n_binding : 'a option}

and ty =
  | Tyvar of string
  | Tycon of tycon name * ty list
  | Tybox of tybox

and tybox = 
  {
    mutable box_value : ty option;
    mutable box_set : int;
    box_id : int;
  }

(* For environment. *)

and signess = Positive | Negative | Signless | Bisigned
  
and tycon = 
  {
    tc_name : string;
    tc_args : signess list;
    tc_is_cotype : bool;
    mutable tc_cons : (value * ty list) list;
    mutable tc_it : value;
    mutable tc_rec : value;
    mutable tc_tyvars : string list;
    mutable tc_rules : rule list;
    mutable tc_outdated : bool;
  }

and rule = 
  {
    r_vars : int list;
    r_elim : value;
    r_ctor : value;
    r_value : term;
  }
  
and semantics =
  | Shorthand of term
  | Alias of term
  | Constructor of tycon
  | Eliminator of tycon
  | Dummy

and value =
  {
    val_name : string;
    val_ty : ty;
    val_semantics : semantics;
  }

and term =
  | App of term * term
  | Abs of int * term
  | Var of int
  | Value of value
