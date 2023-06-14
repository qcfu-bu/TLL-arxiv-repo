open Fmt
open Bindlib
open TLL
open Names
open Syntax0
open Prelude1
open Sedlexing
open Parsing

let _ =
  try
    if Array.length Sys.argv < 1 then
      epr "input file expected@."
    else
      let src_name = Sys.argv.(1) in
      let src_ch = open_in src_name in
      let log_ch = open_out "log.tll" in
      let pre_ch = open_out "c/prelude.h" in
      let trg_ch = open_out "c/main.c" in
      let cur_phase = 0 in
      let all_phase = 7 in
      (* parsing *)
      let dcls0 = parse (Utf8.from_channel src_ch) in
      let cur_phase = cur_phase + 1 in
      pr "@.parsing success (%d/%d)@." cur_phase all_phase;
      Printf.fprintf log_ch "%s%s"
        (str "%a@.@." Pprint0.pp_dcls dcls0)
        (str "parsing success--------------------------@.@.");
      (* trans01 *)
      let _, dcls1 = Trans01.trans_dcls prelude_nspc dcls0 in
      let dcls1 = Prelude1.prelude_dcls @ dcls1 in
      let cur_phase = cur_phase + 1 in
      pr "trans01 success (%d/%d)@." cur_phase all_phase;
      Printf.fprintf log_ch "%s%s"
        (str "%a@.@." Pprint1.pp_dcls dcls1)
        (str "trans01 success--------------------------@.@.");
      (* trans1e *)
      let dcls1e = Trans1e.trans_dcls dcls1 in
      let cur_phase = cur_phase + 1 in
      pr "trans1e success (%d/%d)@." cur_phase all_phase;
      Printf.fprintf log_ch "%s%s"
        (str "%a@.@." Pprint1.pp_dcls dcls1e)
        (str "trans1e success--------------------------@.@.");
      (* trans12 *)
      let dcls2, res = Trans12.trans_dcls dcls1e in
      let cur_phase = cur_phase + 1 in
      pr "trans12 success (%d/%d)@." cur_phase all_phase;
      Printf.fprintf log_ch "%s%s"
        (str "%a@.@." Pprint2.pp_dcls dcls2)
        (str "trans12 success--------------------------@.@.");
      (* trans23 *)
      let dcls3 = Trans23.trans_dcls res dcls2 in
      let cur_phase = cur_phase + 1 in
      pr "trans23 success (%d/%d)@." cur_phase all_phase;
      Printf.fprintf log_ch "%s%s"
        (str "%a@.@." Pprint3.pp_dcls dcls3)
        (str "trans23 success--------------------------@.@.");
      (* trans3e *)
      let dcls3e = Trans3e.trans_dcls dcls3 in
      let cur_phase = cur_phase + 1 in
      pr "trans3e success (%d/%d)@." cur_phase all_phase;
      Printf.fprintf log_ch "%s%s"
        (str "%a@.@." Pprint3.pp_dcls dcls3e)
        (str "trans3e success--------------------------@.@.");
      (* trans34 *)
      let dcls4 = Trans34.trans_dcls dcls3e in
      let cur_phase = cur_phase + 1 in
      pr "trans34 success (%d/%d)@." cur_phase all_phase;
      Printf.fprintf pre_ch "%s" (str "%a@.@." Pprint4.pp_prelude res);
      Printf.fprintf trg_ch "%s" (str "%a@.@." Pprint4.pp_prog dcls4);
      Printf.fprintf log_ch "%s"
        (str "trans34 success--------------------------@.@.");
      pr "compilation finished@."
  with
  | Failure s ->
    let _ = pr "error -----------------------------------@.@." in
    pr "%s@." s
