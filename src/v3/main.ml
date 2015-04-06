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

let first_mark = ref true
let log_file = ref None

let channel_reader ch buf s n =
  if !buf <> "" then 
    let len = (min (String.length !buf) n) in
    let () = String.blit !buf 0 s 0 len in
    let () = buf := String.sub !buf len (String.length !buf - len) in
    len
  else
    let () = 
      if ch == stdin then 
        print_verbose (if !first_mark then "+ " else "= ") 
    in
    let () = flush stdout in
    let l = 
      try (input_line ch) ^ "\n" 
      with End_of_file -> raise Lexer.Eof in
    let () = 
      match !log_file with
      | None -> ()
      | Some ch -> output_string ch l
    in
    let () = 
      if ch != stdin then
        print_verbose ((if !first_mark then "+ " else "= ") ^ l)
    in
    let () = first_mark := false in
    let ll = String.length l in
    if ll <= n then
      let () = String.blit l 0 s 0 ll in
      ll
    else
      let () = String.blit l 0 s 0 n in
      let () = buf := String.sub l n (ll - n) in
      n

let parse_decl lexbuf =
   begin
     first_mark := true;
     try
       let d = Parser.decl Lexer.token lexbuf in
       d
     with 
       | Lexer.Error (fn, l, c, msg) ->
         raise (Error ({loc_file = fn; loc_line = l; loc_char = c}, msg))
       | Parsing.Parse_error ->
         let (fn, l, c) = Lexer.get_current_location () in
         raise (Error ({loc_file = fn; loc_line = l; loc_char = c}, 
                       "parse error"))
   end

let handle_file env name =
  let f = 
    try
      open_in name
    with _ -> 
      raise (Unlocated_error ("error opening input file: `" ^ name ^ "'"))
  in
  let lexbuf = Lexing.from_function (channel_reader f (ref "")) in
  let rec eval env =
    try
      let d = parse_decl lexbuf in
      let env = Eval.eval_decl env d in
      eval env
    with 
    | Error (l, m) -> 
      let () = report_error l m in
      env
    | Unlocated_error m ->
      let (fn, l, c) = Lexer.get_current_location () in
      let () = report_error {loc_file = fn; loc_line = l; loc_char = c} m in
      env
    | Lexer.Eof -> 
      let () = print_verbose "EOF.\n" in
      env
  in
  let old_name = Lexer.get_file_name () in
  let () = Lexer.set_file_name name in
  let env = eval env in
  let () = close_in f in
  let () = Lexer.set_file_name old_name in
  env

let rec read_eval =
  let lexbuf = Lexing.from_function (channel_reader stdin (ref "")) in
  fun env ->
    if false then () else (* XXX: hack. *)
    try
      let d = parse_decl lexbuf in
(*      let () = Pp.print_decl d in *)
      match d.v with
      | Use_cmd fn -> read_eval (handle_file env fn)
      | _ ->
        let env = Eval.eval_decl env d in
        read_eval env
    with 
    | Error (l, m) -> 
      let () = report_error l m in 
      read_eval env
    | Unlocated_error m ->
      let (fn, l, c) = Lexer.get_current_location () in
      let () = report_error {loc_file = fn; loc_line = l; loc_char = c} m in
      read_eval env

let interactive env =
  try
    log_file := Some (open_out "session.et");
    read_eval env
  with Lexer.Eof -> 
    let () = print_endline "\nPaka." in
    exit 0

let main () =
  let () =
    if Array.length Sys.argv > 2 then
    begin
      prerr_endline ("USAGE: " ^ Sys.argv.(0) ^ " [filename.et]");
      exit 1
    end
  in
  let () = quiet := true in
  let env = handle_file Env.empty_env "startup.et" in
  let () = quiet := false in
  if Array.length Sys.argv == 1 then interactive env
  else ignore (handle_file env Sys.argv.(1))

let _ = main ()
