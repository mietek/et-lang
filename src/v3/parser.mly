%{
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

let locus () =
  let fn = Lexer.get_file_name () in
  let (l, c) = Lexer.get_line_column fn (Parsing.symbol_start()) in
        {loc_file=fn;
         loc_char=c;
         loc_line=l}

let ice () = raise Parse_error

let locate x = {l = locus (); v = x}

let name n = {n_name = n; n_binding = None}
let tc n a = Tycon (name n, a)

%}

%token <string> LOWER_ID
%token <string> UPPER_ID
%token <string> TYVAR
%token <string> STRING

%token KW_FN KW_VAL KW_LET KW_IN KW_END KW_DATATYPE KW_FROM KW_CODATATYPE
%token KW_TO KW_USE KW_EXIT KW_SHOW KW_IF KW_THEN KW_ELSE KW_SET
%token LPAREN RPAREN DARROW ARROW COMMA EQ SEMICOLON STAR PLUS LAMBDA DOT
%token BAR AND LBRACE RBRACE

%right ARROW
%left PLUS
%left STAR
%nonassoc DARROW DOT
%left COMMA
%left EQ
%left SEMICOLON
%nonassoc KW_IF KW_THEN KW_ELSE
%nonassoc APP
%nonassoc LOWER_ID UPPER_ID KW_LET KW_FN LAMBDA
%nonassoc TYVAR

%start decl

%type <Ast.decl> decl

%%

decl:
    raw_decl SEMICOLON  { locate $1 }
;

raw_decl:
    KW_VAL LOWER_ID EQ term
        { Value_binding ($2, $4) }
  | KW_LET LOWER_ID EQ term
        { Value_binding ($2, $4) }
  | KW_DATATYPE UPPER_ID tyvars EQ ctors
        { Type ($2, $3, $5) }
  | KW_CODATATYPE UPPER_ID tyvars EQ dtors
        { Cotype ($2, $3, $5) }
  | KW_EXIT
        { Exit_cmd }
  | KW_SHOW
        { Show_cmd "" }
  | KW_SHOW any_id
        { Show_cmd $2 }
  | KW_USE STRING
        { Use_cmd $2 }
  | KW_SET any_id
        { Set_cmd $2 }
  | KW_SET STRING
        { Set_cmd $2 }
  | term
        { Term $1 }
  | term EQ term
        { Eq_test ($1, $3) }
;

any_id:
    UPPER_ID            { $1 }
  | LOWER_ID            { $1 }
;

tyvars:
    /* empty */                 { [] }
  | TYVAR tyvars                { $1 :: $2 }
;

maybe_bar: /* empty */ {()} | BAR {()};
maybe_and: /* empty */ {()} | AND {()};

ctors:
    /* empty */                 { [] }
  | maybe_bar ctor ctor_list    { $2 :: $3 }
;

ctor_list:
    /* empty */                 { [] }
  | BAR ctor ctor_list          { $2 :: $3 }
;

ctor:
    UPPER_ID                    { {cd_name = $1; cd_args = []} }
  | UPPER_ID KW_FROM ty_list    { {cd_name = $1; cd_args = $3} }
;

ty_list:
    ty                  { [$1] }
  | ty ty_list          { $1 :: $2 }
;

dtors:
    /* empty */                 { [] }
  | maybe_and dtor dtor_list    { $2 :: $3 }
;

dtor_list:
    /* empty */                 { [] }
  | AND dtor dtor_list          { $2 :: $3 }
;

dtor:
    UPPER_ID                    { {cd_name = $1; cd_args = []} }
  | UPPER_ID KW_TO ty_list      { {cd_name = $1; cd_args = $3} }
;

aty:
    TYVAR                                { Tyvar $1 }
  | LPAREN ty RPAREN                     { $2 }
  | UPPER_ID                             { tc $1 [] }
;

ty_app:
    ty_app aty      { 
       match $1 with 
       | Tycon (n, a) -> Tycon (n, a @ [$2])
       | _ -> assert false
    }
  | UPPER_ID                             { tc $1 [] }
;

ty:
    ty_app                { $1 }
  | TYVAR                                { Tyvar $1 }
  | LBRACE RBRACE                        { tc "BOTTOM" [] }
  | LPAREN ty RPAREN                     { $2 }
  | ty STAR ty                           { tc "PAIR" [$1; $3] }
  | ty PLUS ty                           { tc "UNION" [$1; $3] }
  | ty ARROW ty                          { tc "->" [$1; $3] }
;

aterm:
    raw_aterm                            { locate $1 }
;

term:
    raw_term                            { locate $1 }
;

raw_aterm:
    any_id                               { T_ref $1 }
  | LPAREN raw_term RPAREN               { $2 }
  | LPAREN RPAREN                        { T_ref "Unit" }
  | KW_LET value_binding_list KW_IN term KW_END
                                         { T_let ($2, $4) }
  | KW_FN fn_vars                        { $2 }
  | LAMBDA lambda_vars                   { $2 }
  | KW_IF term KW_THEN term KW_ELSE term
        { T_app (locate (T_app (locate (T_app (locate (T_ref "_BOOLit"), $2)), $4)), $6) }
;

raw_term:
    raw_aterm                               { $1 }
  | term aterm %prec APP                    { T_app ($1, $2) }
  | term COMMA term 
        { T_app (locate (T_app (locate (T_ref "Pair"), $1)), $3) }
;

value_binding_list:
    value_binding                               { [$1] }
  | value_binding value_binding_list            { $1 :: $2 }
;

value_binding:
    KW_VAL LOWER_ID EQ term SEMICOLON             { ($2, $4) }
  | KW_LET LOWER_ID EQ term SEMICOLON             { ($2, $4) }
;

fn_vars:
    LOWER_ID DARROW term        { T_abs ($1, $3) }
  | LOWER_ID fn_vars            { T_abs ($1, locate $2) }
;

lambda_vars:
    LOWER_ID DOT term           { T_abs ($1, $3) }
  | LOWER_ID lambda_vars        { T_abs ($1, locate $2) }
;
