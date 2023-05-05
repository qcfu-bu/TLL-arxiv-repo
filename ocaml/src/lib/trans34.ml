open Fmt
open Bindlib
open Names
open Syntax3
open Syntax4

(* temporary identifiers *)
module T : sig
  val mk : string -> string
end = struct
  let stamp = ref 0

  let mk s =
    incr stamp;
    str "%s_t%d" s !stamp
end

type vtbl = value VMap.t

let fv ctx m =
  let rec aux ctx = function
    (* core *)
    | Var x ->
      if VSet.mem x ctx then
        VSet.empty
      else
        VSet.singleton x
    | Const _ -> VSet.empty
    | Lam (_, bnd) ->
      let x, m = unbind bnd in
      aux (VSet.add x ctx) m
    | Call (_, ms) ->
      List.fold_left (fun acc m -> VSet.union acc (aux ctx m)) VSet.empty ms
    | App (_, m, n) -> VSet.union (aux ctx m) (aux ctx n)
    | Let (m, bnd) ->
      let x, n = unbind bnd in
      let fv1 = aux ctx m in
      let fv2 = aux (VSet.add x ctx) n in
      VSet.union fv1 fv2
      (* native *)
    | Int _ -> VSet.empty
    | Add (_, m) -> aux ctx m
    | Ifte (m, n1, n2) ->
      let fv0 = aux ctx m in
      let fv1 = aux ctx n1 in
      let fv2 = aux ctx n2 in
      VSet.union fv0 (VSet.union fv1 fv2)
    (* data *)
    | Pair (m, n) -> VSet.union (aux ctx m) (aux ctx n)
    | Cons (_, ms) ->
      List.fold_left (fun acc m -> VSet.union acc (aux ctx m)) VSet.empty ms
    | Match (_, m, cls) ->
      let fv1 = aux ctx m in
      let fv2 =
        List.fold_left
          (fun acc -> function
            | PPair bnd ->
              let xs, m = unmbind bnd in
              let fvs = aux (Array.fold_right VSet.add xs ctx) m in
              VSet.union fvs acc
            | PCons (_, bnd) ->
              let xs, m = unmbind bnd in
              let fvs = aux (Array.fold_right VSet.add xs ctx) m in
              VSet.union fvs acc)
          VSet.empty cls
      in
      VSet.union fv1 fv2
    (* effect *)
    | Open _ -> VSet.empty
    | Fork bnd ->
      let x, m = unbind bnd in
      aux (VSet.add x ctx) m
    | Recv m -> aux ctx m
    | Send (m, n) -> VSet.union (aux ctx m) (aux ctx n)
    | Close m -> aux ctx m
    | Sleep m -> aux ctx m
    | NULL -> VSet.empty
  in
  VSet.elements (aux ctx m)

let trans_prim = function
  | Syntax3.Stdin -> Stdin
  | Syntax3.Stdout -> Stdout
  | Syntax3.Stderr -> Stderr

let rec trans_tm procs (vtbl : vtbl) m =
  match m with
  (* core *)
  | Var x -> (procs, [], VMap.find x vtbl)
  | Const x -> (procs, [], Reg (I.to_string x))
  | Lam (_, bnd) ->
    let x, m = unbind bnd in
    let xid = V.to_string x in
    let fvs = fv (VSet.singleton x) m in
    let env = List.map (fun x -> VMap.find x vtbl) fvs in
    let vtbl =
      Util.fold_lefti
        (fun i acc x -> VMap.add x (Env i) acc)
        (VMap.singleton x (Reg xid))
        fvs
    in
    let procs, instr, ret = trans_tm procs vtbl m in
    let fname = T.mk "lam_fun" in
    let lhs = T.mk "lam_clo" in
    let proc = LFun { fname; param = Some xid; body = instr; return = ret } in
    (proc :: procs, [ Clo { lhs; fname; env } ], Reg lhs)
  | Call (x, ms) ->
    let xid = I.to_string x in
    let lhs = T.mk "call_ret" in
    let procs, ms_instr, ms_ret =
      List.fold_left
        (fun (procs, ms_instr, ms_ret) m ->
          let procs, m_instr, m_ret = trans_tm procs vtbl m in
          (procs, ms_instr @ m_instr, ms_ret @ [ m_ret ]))
        (procs, [], []) ms
    in
    (procs, ms_instr @ [ Call { lhs; fname = xid; aptrs = ms_ret } ], Reg lhs)
  | App (s, m, n) ->
    let procs, m_instr, m_ret = trans_tm procs vtbl m in
    let procs, n_instr, n_ret = trans_tm procs vtbl n in
    let ret = T.mk "app_ret" in
    let app_instr =
      match s with
      | U -> [ App { lhs = ret; fptr = m_ret; aptr = n_ret } ]
      | L -> [ App { lhs = ret; fptr = m_ret; aptr = n_ret }; FreeClo m_ret ]
    in
    (procs, m_instr @ n_instr @ app_instr, Reg ret)
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    let xid = V.to_string x in
    let procs, m_instr, m_ret = trans_tm procs vtbl m in
    let procs, n_instr, n_ret = trans_tm procs (VMap.add x (Reg xid) vtbl) n in
    (procs, m_instr @ [ Mov { lhs = xid; rhs = m_ret } ] @ n_instr, n_ret)
  (* native *)
  | Int i -> (procs, [], Int i)
  | Add (i, m) ->
    let procs, instr, ret = trans_tm procs vtbl m in
    let lhs = T.mk "add_ret" in
    (procs, instr @ [ Add { lhs; i; rhs = ret } ], Reg lhs)
  | Ifte (m, n1, n2) ->
    let procs, m_instr, m_ret = trans_tm procs vtbl m in
    let procs, n1_instr, n1_ret = trans_tm procs vtbl n1 in
    let procs, n2_instr, n2_ret = trans_tm procs vtbl n2 in
    let lhs = T.mk "ifte_ret" in
    ( procs
    , m_instr
      @ [ Ifte
            { cond = m_ret
            ; tcase = n1_instr @ [ Mov { lhs; rhs = n1_ret } ]
            ; fcase = n2_instr @ [ Mov { lhs; rhs = n2_ret } ]
            }
        ]
    , Reg lhs )
  (* data *)
  | Pair (m, n) ->
    let procs, m_instr, m_ret = trans_tm procs vtbl m in
    let procs, n_instr, n_ret = trans_tm procs vtbl n in
    let lhs = T.mk "pair_struct" in
    ( procs
    , m_instr @ n_instr
      @ [ Struct { lhs; ctag = 0; size = 2; data = [ m_ret; n_ret ] } ]
    , Reg lhs )
  | Cons (c, ms) ->
    let procs, ms_instr, ms_ret =
      List.fold_left
        (fun (procs, ms_instr, ms_ret) m ->
          let procs, m_instr, m_ret = trans_tm procs vtbl m in
          (procs, ms_instr @ m_instr, ms_ret @ [ m_ret ]))
        (procs, [], []) ms
    in
    let lhs = T.mk (C.get_name c) in
    ( procs
    , ms_instr
      @ [ Struct
            { lhs; ctag = C.get_id c; size = List.length ms; data = ms_ret }
        ]
    , Reg lhs )
  | Match (s, m, cls) ->
    let procs, m_instr, m_ret = trans_tm procs vtbl m in
    let ret = T.mk "switch_ret" in
    let procs, cls =
      List.fold_left
        (fun (procs, cls) cl ->
          let procs, cl = trans_cl procs vtbl ret m_ret cl s in
          (procs, cls @ [ cl ]))
        (procs, []) cls
    in
    (procs, m_instr @ [ Switch { cond = m_ret; cases = cls } ], Reg ret)
  (* effect *)
  | Open prim ->
    let lhs = T.mk "prim_ch" in
    (procs, [ Open { lhs; mode = trans_prim prim } ], Reg lhs)
  | Fork bnd ->
    let x, m = unbind bnd in
    let fvs = fv (VSet.singleton x) m in
    let env = List.map (fun x -> VMap.find x vtbl) fvs in
    let vtbl =
      Util.fold_lefti
        (fun i acc x -> VMap.add x (Env i) acc)
        VMap.empty (x :: fvs)
    in
    let procs, instr, ret = trans_tm procs vtbl m in
    let fname = T.mk "fork_fun" in
    let lhs = T.mk "fork_ch" in
    let tmp = T.mk "fork_ret" in
    let instr = instr @ [ Mov { lhs = tmp; rhs = ret }; FreeThread ] in
    let proc = LFun { fname; param = None; body = instr; return = Reg tmp } in
    (proc :: procs, [ Fork { lhs; fname; env } ], Reg lhs)
  | Recv m ->
    let lhs = T.mk "recv_msg" in
    let procs, instr, ret = trans_tm procs vtbl m in
    (procs, instr @ [ Recv { lhs; ch = ret } ], Reg lhs)
  | Send (m, n) ->
    let lhs = T.mk "send_ch" in
    let procs, m_instr, m_ret = trans_tm procs vtbl m in
    let procs, n_instr, n_ret = trans_tm procs vtbl n in
    ( procs
    , m_instr @ n_instr @ [ Send { lhs; ch = m_ret; msg = n_ret } ]
    , Reg lhs )
  | Close m ->
    let lhs = T.mk "close_tmp" in
    let procs, instr, ret = trans_tm procs vtbl m in
    (procs, instr @ [ Close { lhs; ch = ret } ], Reg lhs)
  | Sleep m ->
    let lhs = T.mk "sleep_tmp" in
    let procs, instr, ret = trans_tm procs vtbl m in
    (procs, instr @ [ Sleep { lhs; rhs = ret } ], Reg lhs)
  (* erausre *)
  | NULL -> (procs, [], NULL)

and trans_cl procs vtbl ret m_ret cl s =
  match cl with
  | PPair bnd ->
    let xs, rhs = unmbind bnd in
    let _, cl_instr, vtbl =
      Array.fold_left
        (fun (i, instr, vtbl) x ->
          let lhs = V.to_string x in
          ( i + 1
          , instr @ [ Mov { lhs; rhs = Idx (m_ret, i) } ]
          , VMap.add x (Reg lhs) vtbl ))
        (0, [], vtbl) xs
    in
    let procs, rhs_instr, rhs_ret = trans_tm procs vtbl rhs in
    let rhs_instr = rhs_instr @ [ Mov { lhs = ret; rhs = rhs_ret }; Break ] in
    let instr =
      match s with
      | U -> cl_instr @ rhs_instr
      | L -> cl_instr @ [ FreeStruct m_ret ] @ rhs_instr
    in
    (procs, (0, instr))
  | PCons (c, bnd) ->
    let xs, rhs = unmbind bnd in
    let _, cl_instr, vtbl =
      Array.fold_left
        (fun (i, instr, vtbl) x ->
          let lhs = V.to_string x in
          ( i + 1
          , instr @ [ Mov { lhs; rhs = Idx (m_ret, i) } ]
          , VMap.add x (Reg lhs) vtbl ))
        (0, [], vtbl) xs
    in
    let procs, rhs_instr, rhs_ret = trans_tm procs vtbl rhs in
    let rhs_instr = rhs_instr @ [ Mov { lhs = ret; rhs = rhs_ret }; Break ] in
    let instr =
      match s with
      | U -> cl_instr @ rhs_instr
      | L -> cl_instr @ [ FreeStruct m_ret ] @ rhs_instr
    in
    (procs, (C.get_id c, instr))

let trans_dcls dcls =
  let rec aux procs = function
    | [] -> (procs, [], NULL)
    | DFun (x, bnd) :: dcls when I.equal x Prelude1.lten_i ->
      let xs, _ = unmbind bnd in
      let xid = I.to_string x in
      let arg1 = V.to_string xs.(0) in
      let arg2 = V.to_string xs.(1) in
      let ret = T.mk "lten_ret" in
      let instr = [ LteN { lhs = ret; x = Reg arg1; y = Reg arg2 } ] in
      let proc =
        GFun
          { fname = xid
          ; param = [ arg1; arg2 ]
          ; body = instr
          ; return = Reg ret
          }
      in
      aux (proc :: procs) dcls
    | DFun (x, bnd) :: dcls when I.equal x Prelude1.gten_i ->
      let xs, _ = unmbind bnd in
      let xid = I.to_string x in
      let arg1 = V.to_string xs.(0) in
      let arg2 = V.to_string xs.(1) in
      let ret = T.mk "gten_ret" in
      let instr = [ GteN { lhs = ret; x = Reg arg1; y = Reg arg2 } ] in
      let proc =
        GFun
          { fname = xid
          ; param = [ arg1; arg2 ]
          ; body = instr
          ; return = Reg ret
          }
      in
      aux (proc :: procs) dcls
    | DFun (x, bnd) :: dcls when I.equal x Prelude1.ltn_i ->
      let xs, _ = unmbind bnd in
      let xid = I.to_string x in
      let arg1 = V.to_string xs.(0) in
      let arg2 = V.to_string xs.(1) in
      let ret = T.mk "ltn_ret" in
      let instr = [ LtN { lhs = ret; x = Reg arg1; y = Reg arg2 } ] in
      let proc =
        GFun
          { fname = xid
          ; param = [ arg1; arg2 ]
          ; body = instr
          ; return = Reg ret
          }
      in
      aux (proc :: procs) dcls
    | DFun (x, bnd) :: dcls when I.equal x Prelude1.gtn_i ->
      let xs, _ = unmbind bnd in
      let xid = I.to_string x in
      let arg1 = V.to_string xs.(0) in
      let arg2 = V.to_string xs.(1) in
      let ret = T.mk "gtn_ret" in
      let instr = [ GtN { lhs = ret; x = Reg arg1; y = Reg arg2 } ] in
      let proc =
        GFun
          { fname = xid
          ; param = [ arg1; arg2 ]
          ; body = instr
          ; return = Reg ret
          }
      in
      aux (proc :: procs) dcls
    | DFun (x, bnd) :: dcls when I.equal x Prelude1.eqn_i ->
      let xs, _ = unmbind bnd in
      let xid = I.to_string x in
      let arg1 = V.to_string xs.(0) in
      let arg2 = V.to_string xs.(1) in
      let ret = T.mk "eqn_ret" in
      let instr = [ EqN { lhs = ret; x = Reg arg1; y = Reg arg2 } ] in
      let proc =
        GFun
          { fname = xid
          ; param = [ arg1; arg2 ]
          ; body = instr
          ; return = Reg ret
          }
      in
      aux (proc :: procs) dcls
    | DFun (x, bnd) :: dcls when I.equal x Prelude1.addn_i ->
      let xs, _ = unmbind bnd in
      let xid = I.to_string x in
      let arg1 = V.to_string xs.(0) in
      let arg2 = V.to_string xs.(1) in
      let ret = T.mk "addn_ret" in
      let instr = [ AddN { lhs = ret; x = Reg arg1; y = Reg arg2 } ] in
      let proc =
        GFun
          { fname = xid
          ; param = [ arg1; arg2 ]
          ; body = instr
          ; return = Reg ret
          }
      in
      aux (proc :: procs) dcls
    | DFun (x, bnd) :: dcls when I.equal x Prelude1.muln_i ->
      let xs, _ = unmbind bnd in
      let xid = I.to_string x in
      let arg1 = V.to_string xs.(0) in
      let arg2 = V.to_string xs.(1) in
      let ret = T.mk "muln_ret" in
      let instr = [ MulN { lhs = ret; x = Reg arg1; y = Reg arg2 } ] in
      let proc =
        GFun
          { fname = xid
          ; param = [ arg1; arg2 ]
          ; body = instr
          ; return = Reg ret
          }
      in
      aux (proc :: procs) dcls
    | DFun (x, bnd) :: dcls when I.equal x Prelude1.divn_i ->
      let xs, _ = unmbind bnd in
      let xid = I.to_string x in
      let arg1 = V.to_string xs.(0) in
      let arg2 = V.to_string xs.(1) in
      let ret = T.mk "divn_ret" in
      let instr = [ DivN { lhs = ret; x = Reg arg1; y = Reg arg2 } ] in
      let proc =
        GFun
          { fname = xid
          ; param = [ arg1; arg2 ]
          ; body = instr
          ; return = Reg ret
          }
      in
      aux (proc :: procs) dcls
    | DFun (x, bnd) :: dcls when I.equal x Prelude1.modn_i ->
      let xs, _ = unmbind bnd in
      let xid = I.to_string x in
      let arg1 = V.to_string xs.(0) in
      let arg2 = V.to_string xs.(1) in
      let ret = T.mk "modn_ret" in
      let instr = [ ModN { lhs = ret; x = Reg arg1; y = Reg arg2 } ] in
      let proc =
        GFun
          { fname = xid
          ; param = [ arg1; arg2 ]
          ; body = instr
          ; return = Reg ret
          }
      in
      aux (proc :: procs) dcls
    | DFun (x, bnd) :: dcls ->
      let xs, m = unmbind bnd in
      let xs = Array.to_list xs in
      let xid = I.to_string x in
      let xids = List.map V.to_string xs in
      let vtbl =
        List.fold_left2
          (fun acc x xid -> VMap.add x (Reg xid) acc)
          VMap.empty xs xids
      in
      let procs, instr, ret = trans_tm procs vtbl m in
      let proc =
        GFun { fname = xid; param = xids; body = instr; return = ret }
      in
      aux (proc :: procs) dcls
    | DVal (x, m) :: dcls ->
      let xid = I.to_string x in
      let procs, m_instr, m_ret = trans_tm procs VMap.empty m in
      let procs, instr, ret = aux procs dcls in
      (procs, m_instr @ [ Init { lhs = xid; rhs = m_ret } ] @ instr, ret)
    | DMain m :: _ ->
      let procs, instr, ret = trans_tm procs VMap.empty m in
      (procs, instr, ret)
  in
  let procs, instr, ret = aux [] dcls in
  (List.rev procs, instr, ret)
