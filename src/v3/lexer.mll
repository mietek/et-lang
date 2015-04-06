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
(* 
 * Copyright (c) 2002, 2003 The University of Wroclaw.
 * All rights reserved. See file COPYRIGHT for details about licensing.
 *)

{

open Parser        (* The type token is defined in parser.mli *)

type lexer_location = {mutable ll_char : int;
                       mutable ll_file : string}
type global_lexer = {mutable gl_lexbuf : Lexing.lexbuf option}

let comment_depth = ref 0
let comment_start = {ll_file = ""; ll_char = 0}
let current_location = {ll_file = "stdin"; ll_char = 0}

let global_lexer = {gl_lexbuf = None} 

let line_caches : (string, int list ref) Hashtbl.t = Hashtbl.create 16

(* exported *)
exception Error of string * int * int * string
exception Eof

let get_file_name () = current_location.ll_file
let set_file_name s = current_location.ll_file <- s
let get_line_column file_name char_no =
  try
    let stack = Hashtbl.find line_caches file_name in
    let rec helper lst =
      match lst with
          x::xs ->
            if char_no >= x then
              (x, (List.length xs) + 1)
            else
              helper xs
        | [] ->
            (0, 1) in
    let (beg, line) = helper !stack in
    (line, char_no - beg + 1)
  with Not_found -> (1, char_no + 1)
  
let get_current_location () =
   let (l, c) = 
     match global_lexer with
     | {gl_lexbuf = None} -> 
       get_line_column (get_file_name ()) 1
     | {gl_lexbuf = Some lexbuf} -> 
       get_line_column (get_file_name ()) 
                       (Lexing.lexeme_end lexbuf) in
   (get_file_name (), l, c)
(* /exported *)

let next_line lexbuf =
  global_lexer.gl_lexbuf <- Some lexbuf;
  let stack = 
    try
      Hashtbl.find line_caches (get_file_name ())
    with Not_found -> 
      let lst = ref [0] in
        Hashtbl.add line_caches (get_file_name ()) lst; lst
  in
    stack := ((Lexing.lexeme_end lexbuf)) :: !stack

}

let nl = ('\r' '\n' | '\n' | '\r')

let num = ['0'-'9']

let upper = ['A' - 'Z']
let lower = ['a' - 'z']
let id_body = (upper | lower | num | "_" | "'")

rule token = parse
    [' ' '\t']          { token lexbuf }     (* skip blanks *)
  | nl                  { next_line lexbuf; token lexbuf }
  | '"' [^ '"']* '"'    
    { let s = Lexing.lexeme lexbuf in 
      STRING (String.sub s 1 (String.length s - 2)) }
  | "fn"                { KW_FN }
  | "set"               { KW_SET }
  | "val"               { KW_VAL }
  | "let"               { KW_LET }
  | "in"                { KW_IN }
  | "end"               { KW_END }
  | "datatype"          { KW_DATATYPE }
  | "from"              { KW_FROM }
  | "codatatype"        { KW_CODATATYPE }
  | "to"                { KW_TO }
  | "use"               { KW_USE }
  | "exit"              { KW_EXIT }
  | "quit"              { KW_EXIT }
  | "show"              { KW_SHOW }
  | "if"                { KW_IF }
  | "then"              { KW_THEN }
  | "else"              { KW_ELSE }
  | upper id_body *     
                        { UPPER_ID(Lexing.lexeme lexbuf) }
  | (lower | "_") id_body *
                        { LOWER_ID(Lexing.lexeme lexbuf) }
  | "'" (lower | upper) id_body* 
                        { TYVAR(Lexing.lexeme lexbuf) }
  | "(*"                { comment_depth := 1;
                          comment_start.ll_file <- get_file_name ();
                          comment_start.ll_char <- (Lexing.lexeme_start lexbuf);
                          comment lexbuf; 
                          token lexbuf }
  | "#" [^ '\n' '\r']* nl { next_line lexbuf; token lexbuf }
  | "("                 { LPAREN }
  | ")"                 { RPAREN }
  | "{"                 { LBRACE }
  | "}"                 { RBRACE }
  | "=>"                { DARROW }
  | "->"                { ARROW }
  | ","                 { COMMA }
  | "="                 { EQ }
  | ";"                 { SEMICOLON }
  | "*"                 { STAR }
  | "+"                 { PLUS }
  | "\\"                { LAMBDA }
  | "."                 { DOT }
  | "|"                 { BAR }
  | "&"                 { AND }
  | eof                 { raise Eof }
  | _                   
    { let (f, l, c) = get_current_location () in 
        raise (Error(f, l, c, "invalid character in input `" ^ 
                     (String.escaped (Lexing.lexeme lexbuf)) ^ "'")) }

and comment = parse
    "*)"                { decr comment_depth; 
                          if !comment_depth > 0 then (comment lexbuf) }
  | "(*"                { incr comment_depth; comment lexbuf }
  | nl                  { next_line lexbuf; comment lexbuf }
  | eof                 { 
      let (l, c) = get_line_column comment_start.ll_file 
                                   comment_start.ll_char in
      raise (Error (comment_start.ll_file, l, c, "EOF within comment")) }
  | _                   { comment lexbuf }

