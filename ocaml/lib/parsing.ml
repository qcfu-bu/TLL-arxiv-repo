open Fmt
open Sedlexing
open Parser0
open Tokenize
module I = MenhirInterpreter
module S = MenhirLib.General

exception
  ParseError of
    { start_lnum : int
    ; start_cnum : int
    ; end_lnum : int
    ; end_cnum : int
    }

let handle_error checkpoint =
  match Lazy.force (I.stack checkpoint) with
  | S.Nil -> assert false
  | S.Cons (Element (s, _, pos_start, pos_end), _) ->
    let start_lnum = pos_start.pos_lnum in
    let start_cnum = pos_start.pos_cnum in
    let end_lnum = pos_end.pos_lnum in
    let end_cnum = pos_end.pos_cnum in
    raise (ParseError { start_lnum; start_cnum; end_lnum; end_cnum })

let rec loop next_token checkpoint =
  match checkpoint with
  | I.InputNeeded env ->
    let token = next_token () in
    loop next_token (I.offer checkpoint token)
  | I.Shifting _
  | I.AboutToReduce _ ->
    loop next_token (I.resume checkpoint)
  | I.HandlingError env -> handle_error env
  | I.Accepted tm -> tm
  | I.Rejected -> assert false

let parse lexbuf =
  let lexer = with_tokenizer tokenize lexbuf in
  loop lexer (Incremental.main (fst (lexing_positions lexbuf)))
