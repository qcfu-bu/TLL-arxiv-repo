open Fmt
open Bindlib
open Names
open Syntax1
open Equality1
open Pprint1

module Context = struct
  type t =
    { (* types and sorts for variables *)
      var : (tm * sort) VMap.t
    ; (* types and sorts for constants *)
      const : (tm * sort) IMap.t
    ; (* parameters for data *)
      data : (tm param * CSet.t) DMap.t
    ; (* parameterized telescopes for constructors *)
      cons : tele param CMap.t
    }

  let empty =
    { var = VMap.empty
    ; const = IMap.empty
    ; data = DMap.empty
    ; cons = CMap.empty
    }

  let add_var x a s ctx = { ctx with var = VMap.add x (a, s) ctx.var }
  let add_const x a s ctx = { ctx with const = IMap.add x (a, s) ctx.const }
  let add_data d ptm cs ctx = { ctx with data = DMap.add d (ptm, cs) ctx.data }
  let add_cons c ptl ctx = { ctx with cons = CMap.add c ptl ctx.cons }

  let find_var x ctx =
    match VMap.find_opt x ctx.var with
    | Some a -> a
    | None -> failwith "Context.find_var(%a)" V.pp x

  let find_const x ctx =
    match IMap.find_opt x ctx.const with
    | Some sch -> sch
    | None -> failwith "Context.find_const(%a)" I.pp x

  let find_data d ctx =
    match DMap.find_opt d ctx.data with
    | Some res -> res
    | None -> failwith "Context.find_data(%a)" D.pp d

  let find_cons c ctx =
    match CMap.find_opt c ctx.cons with
    | Some sch -> sch
    | None -> failwith "Context.find_cons(%a)" C.pp c
end

module Resolver = struct
  module Sorts = struct
    type t = sorts

    let compare ss1 ss2 =
      List.compare
        (fun s1 s2 ->
          match (s1, s2) with
          | SVar _, _ -> failwith "resolver"
          | _, SVar _ -> failwith "resolver"
          | SMeta _, _ -> failwith "resolver"
          | _, SMeta _ -> failwith "resolver"
          | _ -> compare s1 s2)
        ss1 ss2
  end

  module RMap = Map.Make (Sorts)

  type t =
    { (* resolver for constants *)
      const : I.t RMap.t IMap.t
    ; (* resolver for data *)
      data : D.t RMap.t DMap.t
    ; (* resolver for constants *)
      cons : C.t RMap.t CMap.t
    }

  let empty = { const = IMap.empty; data = DMap.empty; cons = CMap.empty }
  let add_const x rmap res = { res with const = IMap.add x rmap res.const }

  let add_data d0 ss d1 res =
    { res with
      data =
        DMap.add d0
          (match DMap.find_opt d0 res.data with
          | Some rmap -> RMap.add ss d1 rmap
          | None -> RMap.singleton ss d1)
          res.data
    }

  let add_cons c0 ss c1 res =
    { res with
      cons =
        CMap.add c0
          (match CMap.find_opt c0 res.cons with
          | Some rmap -> RMap.add ss c1 rmap
          | None -> RMap.singleton ss c1)
          res.cons
    }

  let find_const x0 ss res =
    match IMap.find_opt x0 res.const with
    | Some rmap -> (
      match RMap.find_opt ss rmap with
      | Some x1 -> x1
      | None -> failwith "Resolver.find_const(%a)" I.pp x0)
    | None -> failwith "Resolver.find_const(%a)" I.pp x0

  let find_data d0 ss res =
    match DMap.find_opt d0 res.data with
    | Some rmap -> (
      match RMap.find_opt ss rmap with
      | Some d1 -> d1
      | None -> failwith "Resolver.find_data(%a)" D.pp d0)
    | None -> failwith "Resolver.find_data(%a)" D.pp d0

  let find_cons c0 ss res =
    match CMap.find_opt c0 res.cons with
    | Some rmap -> (
      match RMap.find_opt ss rmap with
      | Some c1 -> c1
      | None ->
        failwith "Resolver.find_cons1(%a, %a)" C.pp c0 (list ~sep:sp pp_sort) ss
      )
    | None ->
      failwith "Resolver.find_cons0(%a, %a)" C.pp c0 (list ~sep:sp pp_sort) ss
end

module Usage = struct
  type t =
    { (* usage of variables *)
      var : (sort * bool) VMap.t
    ; (* usage of constants *)
      const : (sort * bool) IMap.t
    }

  let empty = { var = VMap.empty; const = IMap.empty }

  let var_singleton x entry =
    { var = VMap.singleton x entry; const = IMap.empty }

  let const_singleton x entry =
    { var = VMap.empty; const = IMap.singleton x entry }

  let merge usg1 usg2 =
    let aux _ opt1 opt2 =
      match (opt1, opt2) with
      | Some (L, false), Some (_, false) -> failwith "merge"
      | Some (_, false), Some (L, false) -> failwith "merge"
      | Some (s1, b1), Some (s2, b2) ->
        if eq_sort s1 s2 then
          Some (s1, b1 && b2)
        else
          failwith "merge"
      | Some b, None -> Some b
      | None, Some b -> Some b
      | _ -> None
    in
    { var = VMap.merge aux usg1.var usg2.var
    ; const = IMap.merge aux usg1.const usg2.const
    }

  let refine_usage usg1 usg2 =
    let aux _ opt1 opt2 =
      match (opt1, opt2) with
      | Some (U, false), None -> Some (U, false)
      | None, Some (U, false) -> Some (U, false)
      | Some (s1, b1), Some (s2, b2) when eq_sort s1 s2 -> Some (s1, b1 && b2)
      | Some (_, true), None -> None
      | None, Some (_, true) -> None
      | None, None -> None
      | _ -> failwith "refine_usage"
    in
    { var = VMap.merge aux usg1.var usg2.var
    ; const = IMap.merge aux usg1.const usg2.const
    }

  let assert_pure usg =
    let aux _ (s, b) = s = U || b in
    if VMap.for_all aux usg.var && IMap.for_all aux usg.const then
      ()
    else
      failwith "assert_pure"

  let assert_empty usg =
    let aux _ (_, b) = b in
    if VMap.for_all aux usg.var && IMap.for_all aux usg.const then
      ()
    else
      let aux0 fmt map =
        VMap.iter
          (fun x (s, b) -> pf fmt "{%a, %a, %b}@." V.pp x pp_sort s b)
          map
      in
      let aux1 fmt map =
        IMap.iter
          (fun x (s, b) -> pf fmt "{%a, %a, %b}@." I.pp x pp_sort s b)
          map
      in
      failwith "assert_empty@.%a@.%a" aux0 usg.var aux1 usg.const

  let remove_var x usg r s =
    match (r, s) with
    | N, _ ->
      if VMap.exists (fun y (_, b) -> eq_vars x y && not b) usg.var then
        failwith "remove_var(%a)" V.pp x
      else
        { usg with var = VMap.remove x usg.var }
    | R, U -> { usg with var = VMap.remove x usg.var }
    | R, L ->
      if VMap.exists (fun y _ -> eq_vars x y) usg.var then
        { usg with var = VMap.remove x usg.var }
      else
        failwith "remove_var(%a)" V.pp x
    | _ -> failwith "remove_var(%a)" V.pp x

  let remove_const x usg r s =
    match (r, s) with
    | N, _ ->
      if IMap.exists (fun y (_, b) -> I.equal x y && not b) usg.const then
        failwith "remove_const(%a)" I.pp x
      else
        { usg with const = IMap.remove x usg.const }
    | R, U -> { usg with const = IMap.remove x usg.const }
    | R, L ->
      if IMap.exists (fun y _ -> I.equal x y) usg.const then
        { usg with const = IMap.remove x usg.const }
      else
        failwith "remove_const(%a)" I.pp x
    | _ -> failwith "remove_const(%a)" I.pp x

  let of_ctx (ctx : Context.t) =
    { var = VMap.map (fun (_, s) -> (s, true)) ctx.var
    ; const = IMap.map (fun (_, s) -> (s, true)) ctx.const
    }
end

module Logical = struct
  let assert_sort = function
    | U -> ()
    | L -> ()
    | _ -> failwith "Logical.assert_sort"

  let assert_equal env m n =
    if eq_tm env m n then
      ()
    else
      failwith "Logical.assert_equal(%a, %a)" pp_tm m pp_tm n

  let rec infer_sort res ctx env a =
    let srt = infer_tm res ctx env a in
    match whnf env srt with
    | Type U -> U
    | Type L -> L
    | _ -> failwith "Logical.infer_sort(%a : %a)" pp_tm a pp_tm srt

  and infer_tm res ctx env m0 =
    match m0 with
    (* inference *)
    | Ann (m, a) ->
      let _ = infer_sort res ctx env a in
      let _ = check_tm res ctx env m a in
      a
    | Meta _ -> failwith "Logical.infer_Meta"
    (* core *)
    | Type U -> Type U
    | Type L -> Type U
    | Type _ -> failwith "Logical.infer_Type"
    | Var x -> fst (Context.find_var x ctx)
    | Const (x0, ss) ->
      let x1 = Resolver.find_const x0 ss res in
      fst (Context.find_const x1 ctx)
    | Pi (_, s, a, bnd) ->
      let _ = assert_sort s in
      let x, b = unbind bnd in
      let t = infer_sort res ctx env a in
      let _ = infer_sort res (Context.add_var x a t ctx) env b in
      Type s
    | Lam (rel, s, a, bnd) ->
      let _ = assert_sort s in
      let x, m = unbind bnd in
      let t = infer_sort res ctx env a in
      let b = infer_tm res (Context.add_var x a t ctx) env m in
      let bnd = bind_var x (lift_tm b) in
      Pi (rel, s, a, unbox bnd)
    | App (m, n) -> (
      let ty_m = infer_tm res ctx env m in
      match whnf env ty_m with
      | Pi (_, _, a, bnd) ->
        let _ = check_tm res ctx env n a in
        subst bnd n
      | _ -> failwith "Logical.infer_App")
    | Let (_, m, bnd) ->
      let x, n = unbind bnd in
      let a = infer_tm res ctx env m in
      let s = infer_sort res ctx env a in
      infer_tm res (Context.add_var x a s ctx) (Env.add_var x m env) n
    (* native *)
    | Unit -> Type U
    | UIt -> Unit
    | Bool -> Type U
    | BTrue -> Bool
    | BFalse -> Bool
    | Nat -> Type U
    | NZero -> Nat
    | NSucc (_, m) ->
      let _ = check_tm res ctx env m Nat in
      Nat
    (* data *)
    | Sigma (_, s, a, bnd) ->
      let _ = assert_sort s in
      let x, b = unbind bnd in
      let r = infer_sort res ctx env a in
      let _ = infer_sort res (Context.add_var x a r ctx) env b in
      Type s
    | Pair (rel, s, m, n) ->
      let _ = assert_sort s in
      let a = infer_tm res ctx env m in
      let b = infer_tm res ctx env n in
      let x = V.mk "_" in
      let bnd = bind_var x (lift_tm b) in
      Sigma (rel, s, a, unbox bnd)
    | Data (d0, ss, ms) ->
      let _ = List.iter assert_sort ss in
      let d1 = Resolver.find_data d0 ss res in
      let ptm, _ = Context.find_data d1 ctx in
      infer_ptm res ctx env ms ptm
    | Cons (c0, ss, ms, ns) ->
      let _ = List.iter assert_sort ss in
      let c1 = Resolver.find_cons c0 ss res in
      let ptl = Context.find_cons c1 ctx in
      infer_ptl res ctx env ms ns ptl
    | Match (m, mot, cls) -> (
      let ty_m = infer_tm res ctx env m in
      match whnf env ty_m with
      | Unit ->
        let _ = infer_unit res ctx env mot cls in
        subst mot m
      | Bool ->
        let _ = infer_bool res ctx env mot cls in
        subst mot m
      | Nat ->
        let _ = infer_nat res ctx env mot cls in
        subst mot m
      | Sigma (rel, s, a, bnd) ->
        let _ = infer_pair res ctx env rel s a bnd mot cls in
        subst mot m
      | Data (d0, ss, ms) ->
        let d1 = Resolver.find_data d0 ss res in
        let _, cs = Context.find_data d1 ctx in
        let _ = infer_cls res ctx env cs ss ms mot cls in
        subst mot m
      | _ -> failwith "Logical.infer_Match")
    (* equality *)
    | Eq (a, m, n) ->
      let _ = infer_sort res ctx env a in
      let _ = check_tm res ctx env m a in
      let _ = check_tm res ctx env n a in
      Type U
    | Refl m ->
      let a = infer_tm res ctx env m in
      Eq (a, m, m)
    | Rew (bnd, p, h) -> (
      let xs, mot = unmbind bnd in
      let ty_p = infer_tm res ctx env p in
      match (whnf env ty_p, xs) with
      | Eq (a, m, n), [| x; y |] ->
        let s = infer_sort res ctx env a in
        let ctx' = Context.add_var x a s ctx in
        let ctx' = Context.add_var y (Eq (a, m, Var x)) U ctx' in
        let _ = infer_sort res ctx' env mot in
        let _ = check_tm res ctx env h (msubst bnd [| m; Refl m |]) in
        msubst bnd [| n; p |]
      | _ -> failwith "Logical.infer_Rew")
    (* monadic *)
    | IO a ->
      let _ = infer_sort res ctx env a in
      Type L
    | Return m ->
      let a = infer_tm res ctx env m in
      IO a
    | MLet (m, bnd) -> (
      let x, n = unbind bnd in
      let ty_m = infer_tm res ctx env m in
      match whnf env ty_m with
      | IO a -> (
        let s = infer_sort res ctx env a in
        let ty_n = infer_tm res (Context.add_var x a s ctx) env n in
        match whnf env ty_n with
        | IO b -> IO b
        | _ -> failwith "Logical.infer_MLet")
      | _ -> failwith "Logical.infer_MLet")
    (* session *)
    | Proto -> Type U
    | End -> Proto
    | Act (_, _, a, bnd) ->
      let x, b = unbind bnd in
      let s = infer_sort res ctx env a in
      let _ = check_tm res (Context.add_var x a s ctx) env b Proto in
      Proto
    | Ch (_, a) ->
      let _ = check_tm res ctx env a Proto in
      Type L
    | Open Stdin -> IO (Ch (Pos, Const (Prelude1.stdin_t_i, [])))
    | Open Stdout -> IO (Ch (Pos, Const (Prelude1.stdout_t_i, [])))
    | Open Stderr -> IO (Ch (Pos, Const (Prelude1.stderr_t_i, [])))
    | Fork (a0, bnd) -> (
      let x, m = unbind bnd in
      let s = infer_sort res ctx env a0 in
      match whnf env a0 with
      | Ch (Pos, a) ->
        let ty = IO Unit in
        let _ = check_tm res (Context.add_var x a0 s ctx) env m ty in
        IO (Ch (Neg, a))
      | _ -> failwith "Logical.infer_Fork")
    | Recv m -> (
      let ty_m = infer_tm res ctx env m in
      match whnf env ty_m with
      | Ch (rol1, Act (rel, rol2, a, bnd)) when rol1 <> rol2 = true ->
        let x, b = unbind bnd in
        let bnd = unbox (bind_var x (lift_tm (Ch (rol1, b)))) in
        IO (Sigma (rel, L, a, bnd))
      | _ -> failwith "Logical.infer_Recv")
    | Send m -> (
      let ty_m = infer_tm res ctx env m in
      match whnf env ty_m with
      | Ch (rol1, Act (rel, rol2, a, bnd)) when rol1 <> rol2 = false ->
        let x, b = unbind bnd in
        let bnd = unbox (bind_var x (lift_tm (IO (Ch (rol1, b))))) in
        Pi (rel, L, a, bnd)
      | _ -> failwith "Logical.infer_Send")
    | Close m -> (
      let ty_m = infer_tm res ctx env m in
      match whnf env ty_m with
      | Ch (_, End) -> IO Unit
      | _ -> failwith "Logical.infer_Close")
    (* effects *)
    | Sleep m ->
      let _ = check_tm res ctx env m Nat in
      IO Unit
    | Rand (m, n) ->
      let _ = check_tm res ctx env m Nat in
      let _ = check_tm res ctx env n Nat in
      let n = mkApps (Const (Prelude1.addn_i, [])) [ m; n ] in
      IO (Data (Prelude1.between_d, [], [ m; n ]))

  and infer_unit res ctx env mot cls =
    match cls with
    | [ PIt rhs ] ->
      let mot = subst mot UIt in
      let _ = infer_sort res ctx env mot in
      check_tm res ctx env rhs mot
    | _ -> failwith "Logical.infer_unit"

  and infer_bool res ctx env mot cls =
    match cls with
    | [ PTrue rhs1; PFalse rhs2 ] ->
      let mot1 = subst mot BTrue in
      let mot2 = subst mot BFalse in
      let _ = infer_sort res ctx env mot1 in
      let _ = infer_sort res ctx env mot2 in
      let _ = check_tm res ctx env rhs1 mot1 in
      let _ = check_tm res ctx env rhs2 mot2 in
      ()
    | [ PFalse rhs2; PTrue rhs1 ] ->
      let mot1 = subst mot BTrue in
      let mot2 = subst mot BFalse in
      let _ = infer_sort res ctx env mot1 in
      let _ = infer_sort res ctx env mot2 in
      let _ = check_tm res ctx env rhs1 mot1 in
      let _ = check_tm res ctx env rhs2 mot2 in
      ()
    | _ -> failwith "Logical.infer_bool"

  and infer_nat res ctx1 env mot cls =
    match cls with
    | [ PZero rhs1; PSucc bnd ] ->
      let x, rhs2 = unbind bnd in
      let ctx2 = Context.(add_var x Nat U ctx1) in
      let mot1 = subst mot NZero in
      let mot2 = subst mot (NSucc (1, Var x)) in
      let _ = infer_sort res ctx1 env mot1 in
      let _ = infer_sort res ctx2 env mot2 in
      let _ = check_tm res ctx1 env rhs1 mot1 in
      let _ = check_tm res ctx2 env rhs2 mot2 in
      ()
    | [ PSucc bnd; PZero rhs1 ] ->
      let x, rhs2 = unbind bnd in
      let ctx2 = Context.(add_var x Nat U ctx1) in
      let mot1 = subst mot NZero in
      let mot2 = subst mot (NSucc (1, Var x)) in
      let _ = infer_sort res ctx1 env mot1 in
      let _ = infer_sort res ctx2 env mot2 in
      let _ = check_tm res ctx1 env rhs1 mot1 in
      let _ = check_tm res ctx2 env rhs2 mot2 in
      ()
    | _ -> failwith "trans1e.infer_nat"

  and infer_pair res ctx env rel s a bnd mot cls =
    match cls with
    | [ PPair (rel0, s0, bnd0) ] when rel = rel0 && eq_sort s s0 -> (
      let xs, rhs = unmbind bnd0 in
      match xs with
      | [| x; y |] ->
        let b = subst bnd (Var x) in
        let r = infer_sort res ctx env a in
        let ctx = Context.add_var x a r ctx in
        let t = infer_sort res ctx env b in
        let ctx = Context.add_var y b t ctx in
        let tm = Pair (rel, s, Var x, Var y) in
        let ty = Sigma (rel, s, a, bnd) in
        let mot = subst mot (Ann (tm, ty)) in
        let _ = infer_sort res ctx env mot in
        check_tm res ctx env rhs mot
      | _ -> failwith "Logical.infer_pair")
    | _ -> failwith "Logical.infer_pair"

  and infer_cls res ctx env cs ss ms mot cls =
    match cls with
    | [] when CSet.is_empty cs -> ()
    | PCons (c0, bnd) :: cls ->
      let c1 = Resolver.find_cons c0 ss res in
      if CSet.mem c1 cs then
        let _ = infer_cl res ctx env ss ms mot c0 bnd in
        infer_cls res ctx env (CSet.remove c1 cs) ss ms mot cls
      else
        failwith "Logical.infer_cls"
    | _ -> failwith "Logical.infer_cls"

  and infer_cl res ctx env ss ms mot c0 bnd =
    let rec init_param ms ptl =
      match (ms, ptl) with
      | [], PBase tl -> tl
      | m :: ms, PBind (a, bnd) -> init_param ms (subst bnd (Ann (m, a)))
      | _ -> failwith "Logical.init_param"
    in
    let rec init_tele ctx xs tl =
      match (xs, tl) with
      | [], TBase b -> (ctx, b)
      | x :: xs, TBind (_, a, bnd) ->
        let s = infer_sort res ctx env a in
        let ctx = Context.add_var x a s ctx in
        let tl = subst bnd (Var x) in
        init_tele ctx xs tl
      | _ -> failwith "Logical.init_tele"
    in
    let xs, rhs = unmbind bnd in
    let xs = Array.to_list xs in
    let c1 = Resolver.find_cons c0 ss res in
    let ptl = Context.find_cons c1 ctx in
    let tl = init_param ms ptl in
    let ctx, ty = init_tele ctx xs tl in
    let _ = infer_sort res ctx env ty in
    let mot = subst mot (Cons (c0, ss, ms, List.map var xs)) in
    let _ = infer_sort res ctx env mot in
    check_tm res ctx env rhs mot

  and infer_ptm res ctx env ms ptm =
    match (ms, ptm) with
    | [], PBase b ->
      let _ = infer_sort res ctx env b in
      b
    | m :: ms, PBind (a, bnd) ->
      let _ = check_tm res ctx env m a in
      infer_ptm res ctx env ms (subst bnd m)
    | _ -> failwith "Logical.infer_ptm(%a)" pp_ptm ptm

  and infer_ptl res ctx env ms ns ptl =
    match (ms, ptl) with
    | [], PBase tl -> infer_tele res ctx env ns tl
    | m :: ms, PBind (a, bnd) ->
      let _ = check_tm res ctx env m a in
      infer_ptl res ctx env ms ns (subst bnd m)
    | _ -> failwith "Logical.infer_ptl(%a)" pp_ptl ptl

  and infer_tele res ctx env ns tl =
    match (ns, tl) with
    | [], TBase b ->
      let _ = infer_sort res ctx env b in
      b
    | n :: ns, TBind (_, a, bnd) ->
      let _ = check_tm res ctx env n a in
      infer_tele res ctx env ns (subst bnd n)
    | _ -> failwith "Logical.infer_tele(%a)" pp_tele tl

  and check_tm res ctx env m0 a0 =
    match (m0, whnf env a0) with
    (* core *)
    | Lam (rel0, s0, a0, bnd0), Pi (rel1, s1, a1, bnd1)
      when rel0 = rel1 && eq_sort s0 s1 ->
      let _ = assert_sort s0 in
      let x, m, b = unbind2 bnd0 bnd1 in
      let t = infer_sort res ctx env a0 in
      let _ = assert_equal env a0 a1 in
      check_tm res (Context.add_var x a1 t ctx) env m b
    | Let (rel, m, bnd), a0 ->
      let x, n = unbind bnd in
      let a = infer_tm res ctx env m in
      let s = infer_sort res ctx env a in
      check_tm res (Context.add_var x a s ctx) (Env.add_var x m env) n a0
    (* data *)
    | Pair (rel0, s0, m, n), Sigma (rel1, s1, a, bnd)
      when rel0 = rel1 && eq_sort s0 s1 ->
      let _ = assert_sort s0 in
      let _ = check_tm res ctx env m a in
      check_tm res ctx env n (subst bnd (Ann (m, a)))
    | Match (m, mot, cls), a0 -> (
      let ty_m = infer_tm res ctx env m in
      let a1 = subst mot m in
      let _ = infer_sort res ctx env a1 in
      let _ = assert_equal env a0 a1 in
      match whnf env ty_m with
      | Sigma (rel, srt, a, bnd) -> infer_pair res ctx env rel srt a bnd mot cls
      | Data (d0, ss, ms) ->
        let d1 = Resolver.find_data d0 ss res in
        let _, cs = Context.find_data d1 ctx in
        infer_cls res ctx env cs ss ms mot cls
      | _ ->
        let a1 = infer_tm res ctx env m0 in
        assert_equal env a0 a1)
    (* core *)
    | m0, a0 ->
      let a1 = infer_tm res ctx env m0 in
      assert_equal env a0 a1
end

module Program = struct
  let trans_sort = function
    | U -> Syntax2.U
    | L -> Syntax2.L
    | _ -> failwith "Program.trans_sort"

  let trans_rel = function
    | N -> Syntax2.N
    | R -> Syntax2.R

  let trans_role = function
    | Pos -> Syntax2.Pos
    | Neg -> Syntax2.Neg

  let trans_var x = Syntax2.(copy_var x var (name_of x))
  let trans_mvar xs = Array.map trans_var xs

  let rec infer_tm res ctx env m =
    match m with
    (* inference *)
    | Ann (m, a) ->
      let _ = Logical.infer_sort res ctx env a in
      let m_elab, usg = check_tm res ctx env m a in
      (a, m_elab, usg)
    | Meta _ -> failwith "Program.infer_Meta"
    (* core *)
    | Type _ -> failwith "Program.infer_Type"
    | Var x ->
      let a, s = Context.find_var x ctx in
      Syntax2.(a, _Var (trans_var x), Usage.var_singleton x (s, false))
    | Const (x0, ss) ->
      let x1 = Resolver.find_const x0 ss res in
      let a, s = Context.find_const x1 ctx in
      Syntax2.(a, _Const x1, Usage.const_singleton x1 (s, false))
    | Pi _ -> failwith "Program.infer_Pi"
    | Lam (rel, s, a, bnd) -> (
      let _ = Logical.assert_sort s in
      let x, m = unbind bnd in
      let t = Logical.infer_sort res ctx env a in
      let b, m_elab, usg = infer_tm res (Context.add_var x a t ctx) env m in
      let usg = Usage.remove_var x usg rel t in
      let b_bnd = bind_var x (lift_tm b) in
      let m_bnd = Syntax2.(bind_var (trans_var x) m_elab) in
      match s with
      | U ->
        let _ = Usage.assert_pure usg in
        Syntax2.(Pi (rel, s, a, unbox b_bnd), _Lam U m_bnd, usg)
      | L -> Syntax2.(Pi (rel, s, a, unbox b_bnd), _Lam L m_bnd, usg)
      | _ -> failwith "Program.infer_Lam")
    | App (m, n) -> (
      let a, m_elab, usg1 = infer_tm res ctx env m in
      match whnf env a with
      | Pi (N, s, a, bnd) ->
        let _ = Logical.check_tm res ctx env n a in
        Syntax2.(subst bnd n, _App (trans_sort s) m_elab _NULL, usg1)
      | Pi (R, s, a, bnd) ->
        let n_elab, usg2 = check_tm res ctx env n a in
        Syntax2.
          (subst bnd n, _App (trans_sort s) m_elab n_elab, Usage.merge usg1 usg2)
      | _ -> failwith "Program.infer_App")
    | Let (N, m, bnd) ->
      let x, n = unbind bnd in
      let a = Logical.infer_tm res ctx env m in
      let s = Logical.infer_sort res ctx env a in
      let ctx = Context.add_var x a s ctx in
      let env = Env.add_var x m env in
      let b, n_elab, usg = infer_tm res ctx env n in
      let usg = Usage.remove_var x usg N s in
      Syntax2.(b, _Let _NULL (bind_var (trans_var x) n_elab), usg)
    | Let (R, m, bnd) ->
      let x, n = unbind bnd in
      let a, m_elab, usg1 = infer_tm res ctx env m in
      let s = Logical.infer_sort res ctx env a in
      let ctx = Context.add_var x a s ctx in
      let env = Env.add_var x m env in
      let b, n_elab, usg2 = infer_tm res ctx env n in
      let usg = Usage.(merge usg1 (remove_var x usg2 R s)) in
      Syntax2.(b, _Let m_elab (bind_var (trans_var x) n_elab), usg)
    (* native *)
    | Unit -> failwith "Program.infer_Unit"
    | UIt -> Syntax2.(Unit, _UIt, Usage.empty)
    | Bool -> failwith "Program.infer_Bool"
    | BTrue -> Syntax2.(Bool, _BTrue, Usage.empty)
    | BFalse -> Syntax2.(Bool, _BFalse, Usage.empty)
    | Nat -> failwith "Program.infer_Nat"
    | NZero -> Syntax2.(Nat, _NZero, Usage.empty)
    | NSucc (i, m) ->
      let m_elab, usg = check_tm res ctx env m Nat in
      Syntax2.(Nat, _NSucc i m_elab, usg)
    (* data *)
    | Sigma _ -> failwith "Program.infer_Sigma"
    | Pair (N, s, m, n) ->
      let _ = Logical.assert_sort s in
      let a = Logical.infer_tm res ctx env m in
      let b, n_elab, usg = infer_tm res ctx env n in
      let x = V.mk "_" in
      let bnd = bind_var x (lift_tm b) in
      Syntax2.(Sigma (N, s, a, unbox bnd), _Pair _NULL n_elab, usg)
    | Pair (R, s, m, n) ->
      let _ = Logical.assert_sort s in
      let a, m_elab, usg1 = infer_tm res ctx env m in
      let b, n_elab, usg2 = infer_tm res ctx env n in
      let x = V.mk "_" in
      let bnd = bind_var x (lift_tm b) in
      Syntax2.
        (Sigma (R, s, a, unbox bnd), _Pair m_elab n_elab, Usage.merge usg1 usg2)
    | Data _ -> failwith "Program.infer_Data"
    | Cons (c0, ss, ms, ns) ->
      let _ = List.iter Logical.assert_sort ss in
      let c1 = Resolver.find_cons c0 ss res in
      let ptl = Context.find_cons c1 ctx in
      let a, ns_elab, usg = infer_ptl res ctx env ms ns ptl in
      Syntax2.(a, _Cons c1 (box_list ns_elab), usg)
    | Match (m, mot, cls) -> (
      let ty_m, m_elab, usg1 = infer_tm res ctx env m in
      let s = Logical.infer_sort res ctx env ty_m in
      match whnf env ty_m with
      | Unit ->
        let cls_elab, usg2 = infer_unit res ctx env mot cls in
        let usg = Usage.merge usg1 usg2 in
        Syntax2.
          (subst mot m, _Match (trans_sort s) m_elab (box_list cls_elab), usg)
      | Bool ->
        let cls_elab, usg2 = infer_bool res ctx env mot cls in
        let usg = Usage.merge usg1 usg2 in
        Syntax2.
          (subst mot m, _Match (trans_sort s) m_elab (box_list cls_elab), usg)
      | Nat ->
        let cls_elab, usg2 = infer_nat res ctx env mot cls in
        let usg = Usage.merge usg1 usg2 in
        Syntax2.
          (subst mot m, _Match (trans_sort s) m_elab (box_list cls_elab), usg)
      | Sigma (rel, _, a, bnd) ->
        let cls_elab, usg2 = infer_pair res ctx env rel s a bnd mot cls in
        let usg = Usage.merge usg1 usg2 in
        Syntax2.
          (subst mot m, _Match (trans_sort s) m_elab (box_list cls_elab), usg)
      | Data (d0, ss, ms) ->
        let d1 = Resolver.find_data d0 ss res in
        let _, cs = Context.find_data d1 ctx in
        let cls_elab, usg2 = infer_cls res ctx env cs ss ms mot cls in
        let usg = Usage.merge usg1 usg2 in
        Syntax2.
          (subst mot m, _Match (trans_sort s) m_elab (box_list cls_elab), usg)
      | _ -> failwith "Program.infer_Match")
    (* equality *)
    | Eq _ -> failwith "Program.infer_Eq"
    | Refl _ -> failwith "Program.infer_Refl"
    | Rew (bnd, p, h) -> (
      let xs, mot = unmbind bnd in
      let ty_p = Logical.infer_tm res ctx env p in
      match (whnf env ty_p, xs) with
      | Eq (a, m, n), [| x; y |] ->
        let s = Logical.infer_sort res ctx env a in
        let ctx' = Context.add_var x a s ctx in
        let ctx' = Context.add_var y (Eq (a, m, Var x)) U ctx' in
        let _ = Logical.infer_sort res ctx' env mot in
        let h_elab, usg = check_tm res ctx env h (msubst bnd [| m; Refl m |]) in
        (msubst bnd [| n; p |], h_elab, usg)
      | _ -> failwith "Program.infer_Rew")
    (* monadic *)
    | IO _ -> failwith "Program.infer_IO"
    | Return m ->
      let a, m_elab, usg = infer_tm res ctx env m in
      Syntax2.(IO a, _Return m_elab, usg)
    | MLet (m, bnd) -> (
      let x, n = unbind bnd in
      let ty_m, m_elab, usg1 = infer_tm res ctx env m in
      match whnf env ty_m with
      | IO a -> (
        let s = Logical.infer_sort res ctx env a in
        let ty_n, n_elab, usg2 =
          infer_tm res (Context.add_var x a s ctx) env n
        in
        let usg = Usage.(merge usg1 (remove_var x usg2 R s)) in
        match whnf env ty_n with
        | IO b ->
          Syntax2.(IO b, _MLet m_elab (bind_var (trans_var x) n_elab), usg)
        | _ -> failwith "Program.infer_MLet0(%a)" pp_tm ty_n)
      | _ -> failwith "Program.infer_MLet1")
    (* session *)
    | Proto -> failwith "Program.infer_Proto"
    | End -> failwith "Program.infer_End"
    | Act _ -> failwith "Program.infer_Act"
    | Ch _ -> failwith "Program.infer_Ch"
    | Open Stdin ->
      let ty = IO (Ch (Pos, Const (Prelude1.stdin_t_i, []))) in
      Syntax2.(ty, _Open Stdin, Usage.empty)
    | Open Stdout ->
      let ty = IO (Ch (Pos, Const (Prelude1.stdout_t_i, []))) in
      Syntax2.(ty, _Open Stdout, Usage.empty)
    | Open Stderr ->
      let ty = IO (Ch (Pos, Const (Prelude1.stderr_t_i, []))) in
      Syntax2.(ty, _Open Stderr, Usage.empty)
    | Fork (a0, bnd) -> (
      let x, m = unbind bnd in
      let s = Logical.infer_sort res ctx env a0 in
      match whnf env a0 with
      | Ch (Pos, a) ->
        let ty = IO Unit in
        let m_elab, usg = check_tm res (Context.add_var x a0 s ctx) env m ty in
        let usg = Usage.(remove_var x usg R L) in
        Syntax2.(IO (Ch (Neg, a)), _Fork (bind_var (trans_var x) m_elab), usg)
      | _ -> failwith "Program.infer_Fork")
    | Recv m -> (
      let ty_m, m_elab, usg = infer_tm res ctx env m in
      match whnf env ty_m with
      | Ch (rol1, Act (rel, rol2, a, bnd)) when rol1 <> rol2 = true ->
        let x, b = unbind bnd in
        let bnd = unbox (bind_var x (lift_tm (Ch (rol1, b)))) in
        Syntax2.(IO (Sigma (rel, L, a, bnd)), _Recv (trans_rel rel) m_elab, usg)
      | _ -> failwith "Program.infer_Recv")
    | Send m -> (
      let ty_m, m_elab, usg = infer_tm res ctx env m in
      match whnf env ty_m with
      | Ch (rol1, Act (rel, rol2, a, bnd)) when rol1 <> rol2 = false ->
        let x, b = unbind bnd in
        let s = Logical.infer_sort res ctx env a in
        let bnd = unbox (bind_var x (lift_tm (IO (Ch (rol1, b))))) in
        Syntax2.
          (Pi (rel, L, a, bnd), _Send (trans_rel rel) (trans_sort s) m_elab, usg)
      | _ -> failwith "Program.infer_Send")
    | Close m -> (
      let ty_m, m_elab, usg = infer_tm res ctx env m in
      match whnf env ty_m with
      | Ch (rol, End) ->
        let ty = IO Unit in
        Syntax2.(ty, _Close (trans_role rol) m_elab, usg)
      | _ -> failwith "Program.infer_Close")
    (* effects *)
    | Sleep m ->
      let m_elab, usg = check_tm res ctx env m Nat in
      Syntax2.(IO Unit, _Sleep m_elab, usg)
    | Rand (m, n) ->
      let m_elab, usg1 = check_tm res ctx env m Nat in
      let n_elab, usg2 = check_tm res ctx env n Nat in
      let n = mkApps (Const (Prelude1.addn_i, [])) [ m; n ] in
      Syntax2.
        ( IO (Data (Prelude1.between_d, [], [ m; n ]))
        , _Rand m_elab n_elab
        , Usage.merge usg1 usg2 )

  and infer_unit res ctx env mot cls =
    match cls with
    | [ PIt rhs ] ->
      let mot = subst mot UIt in
      let _ = Logical.infer_sort res ctx env mot in
      let rhs_elab, usg = check_tm res ctx env rhs mot in
      Syntax2.([ _PIt rhs_elab ], usg)
    | _ -> failwith "Program.infer_unit"

  and infer_bool res ctx env mot cls =
    match cls with
    | [ PTrue rhs1; PFalse rhs2 ] ->
      let mot1 = subst mot BTrue in
      let mot2 = subst mot BFalse in
      let _ = Logical.infer_sort res ctx env mot1 in
      let _ = Logical.infer_sort res ctx env mot2 in
      let rhs1_elab, usg1 = check_tm res ctx env rhs1 mot1 in
      let rhs2_elab, usg2 = check_tm res ctx env rhs2 mot2 in
      Syntax2.
        ([ _PTrue rhs1_elab; _PFalse rhs2_elab ], Usage.refine_usage usg1 usg2)
    | [ PFalse rhs2; PTrue rhs1 ] ->
      let mot1 = subst mot BTrue in
      let mot2 = subst mot BFalse in
      let _ = Logical.infer_sort res ctx env mot1 in
      let _ = Logical.infer_sort res ctx env mot2 in
      let rhs1_elab, usg1 = check_tm res ctx env rhs1 mot1 in
      let rhs2_elab, usg2 = check_tm res ctx env rhs2 mot2 in
      Syntax2.
        ([ _PTrue rhs1_elab; _PFalse rhs2_elab ], Usage.refine_usage usg1 usg2)
    | _ -> failwith "Program.infer_bool"

  and infer_nat res ctx1 env mot cls =
    match cls with
    | [ PZero rhs1; PSucc bnd ] ->
      let x, rhs2 = unbind bnd in
      let ctx2 = Context.(add_var x Nat U ctx1) in
      let mot1 = subst mot NZero in
      let mot2 = subst mot (NSucc (1, Var x)) in
      let _ = Logical.infer_sort res ctx1 env mot1 in
      let _ = Logical.infer_sort res ctx2 env mot2 in
      let rhs1_elab, usg1 = check_tm res ctx1 env rhs1 mot1 in
      let rhs2_elab, usg2 = check_tm res ctx2 env rhs2 mot2 in
      let usg2 = Usage.(remove_var x usg2 R U) in
      let x = trans_var x in
      Syntax2.
        ( [ _PZero rhs1_elab; _PSucc (bind_var x rhs2_elab) ]
        , Usage.refine_usage usg1 usg2 )
    | [ PSucc bnd; PZero rhs1 ] ->
      let x, rhs2 = unbind bnd in
      let ctx2 = Context.(add_var x Nat U ctx1) in
      let mot1 = subst mot NZero in
      let mot2 = subst mot (NSucc (1, Var x)) in
      let _ = Logical.infer_sort res ctx1 env mot1 in
      let _ = Logical.infer_sort res ctx2 env mot2 in
      let rhs1_elab, usg1 = check_tm res ctx1 env rhs1 mot1 in
      let rhs2_elab, usg2 = check_tm res ctx2 env rhs2 mot2 in
      let usg2 = Usage.(remove_var x usg2 R U) in
      let x = trans_var x in
      Syntax2.
        ( [ _PZero rhs1_elab; _PSucc (bind_var x rhs2_elab) ]
        , Usage.refine_usage usg1 usg2 )
    | _ -> failwith "Program.infer_nat"

  and infer_pair res ctx env rel s a bnd mot cls =
    match (rel, cls) with
    | N, [ PPair (N, s0, bnd0) ] when eq_sort s s0 -> (
      let xs, rhs = unmbind bnd0 in
      match xs with
      | [| x; y |] ->
        let b = subst bnd (Var x) in
        let r = Logical.infer_sort res ctx env a in
        let ctx = Context.add_var x a r ctx in
        let t = Logical.infer_sort res ctx env b in
        let ctx = Context.add_var y b t ctx in
        let tm = Pair (N, s, Var x, Var y) in
        let ty = Sigma (N, s, a, bnd) in
        let mot = subst mot (Ann (tm, ty)) in
        let _ = Logical.infer_sort res ctx env mot in
        let rhs_elab, usg = check_tm res ctx env rhs mot in
        let usg = Usage.remove_var x usg N r in
        let usg = Usage.remove_var y usg R t in
        let x = trans_var x in
        let y = trans_var y in
        Syntax2.([ _PPair (bind_mvar [| x; y |] rhs_elab) ], usg)
      | _ -> failwith "Program.infer_pair")
    | R, [ PPair (R, s0, bnd0) ] when eq_sort s s0 -> (
      let xs, rhs = unmbind bnd0 in
      match xs with
      | [| x; y |] ->
        let b = subst bnd (Var x) in
        let r = Logical.infer_sort res ctx env a in
        let ctx = Context.add_var x a r ctx in
        let t = Logical.infer_sort res ctx env b in
        let ctx = Context.add_var y b t ctx in
        let tm = Pair (R, s, Var x, Var y) in
        let ty = Sigma (R, s, a, bnd) in
        let mot = subst mot (Ann (tm, ty)) in
        let _ = Logical.infer_sort res ctx env mot in
        let rhs_elab, usg = check_tm res ctx env rhs mot in
        let usg = Usage.remove_var x usg R r in
        let usg = Usage.remove_var y usg R t in
        let x = trans_var x in
        let y = trans_var y in
        Syntax2.([ _PPair (bind_mvar [| x; y |] rhs_elab) ], usg)
      | _ -> failwith "Program.infer_pair")
    | _ -> failwith "Program.infer_pair"

  and infer_cls res ctx env cs ss ms mot cls =
    match cls with
    | [] when CSet.is_empty cs -> ([], Usage.of_ctx ctx)
    | PCons (c0, bnd) :: cls ->
      let c1 = Resolver.find_cons c0 ss res in
      if CSet.mem c1 cs then
        let bnd_elab, usg1 = infer_cl res ctx env ss ms mot c0 bnd in
        let cls_elab, usg2 =
          infer_cls res ctx env (CSet.remove c1 cs) ss ms mot cls
        in
        Syntax2.(_PCons c1 bnd_elab :: cls_elab, Usage.refine_usage usg1 usg2)
      else
        failwith "Program.infer_cls"
    | _ -> failwith "Program.infer_cls"

  and infer_cl res ctx env ss ms mot c0 bnd =
    let rec init_param ms ptl =
      match (ms, ptl) with
      | [], PBase tl -> tl
      | m :: ms, PBind (a, bnd) -> init_param ms (subst bnd (Ann (m, a)))
      | _ -> failwith "Program.infer_cl"
    in
    let rec init_tele ctx xs tl =
      match (xs, tl) with
      | [], TBase b -> (ctx, [], b)
      | x :: xs, TBind (rel, a, bnd) ->
        let s = Logical.infer_sort res ctx env a in
        let ctx = Context.add_var x a s ctx in
        let tl = subst bnd (Var x) in
        let ctx, xrs, b = init_tele ctx xs tl in
        (ctx, (x, rel, s) :: xrs, b)
      | _ -> failwith "Program.init_tele"
    in
    let xs0, rhs = unmbind bnd in
    let xs1 = Array.to_list xs0 in
    let c1 = Resolver.find_cons c0 ss res in
    let ptl = Context.find_cons c1 ctx in
    let tl = init_param ms ptl in
    let ctx, xrs, ty = init_tele ctx xs1 tl in
    let _ = Logical.infer_sort res ctx env ty in
    let mot = subst mot (Cons (c0, ss, ms, List.map var xs1)) in
    let _ = Logical.infer_sort res ctx env mot in
    let rhs_elab, usg = check_tm res ctx env rhs mot in
    let usg =
      List.fold_left
        (fun acc (x, rel, s) -> Usage.remove_var x acc rel s)
        usg xrs
    in
    (bind_mvar (trans_mvar xs0) rhs_elab, usg)

  and infer_ptl res ctx env ms ns ptl =
    match (ms, ptl) with
    | [], PBase tl -> infer_tele res ctx env ns tl
    | m :: ms, PBind (a, bnd) ->
      let _ = Logical.check_tm res ctx env m a in
      infer_ptl res ctx env ms ns (subst bnd m)
    | _ -> failwith "Program.infer_ptl"

  and infer_tele res ctx env ns tl =
    match (ns, tl) with
    | [], TBase b ->
      let _ = Logical.infer_sort res ctx env b in
      (b, [], Usage.empty)
    | n :: ns, TBind (N, a, bnd) ->
      let _ = Logical.check_tm res ctx env n a in
      let b, ns_elab, usg = infer_tele res ctx env ns (subst bnd n) in
      Syntax2.(b, _NULL :: ns_elab, usg)
    | n :: ns, TBind (R, a, bnd) ->
      let n_elab, usg1 = check_tm res ctx env n a in
      let b, ns_elab, usg2 = infer_tele res ctx env ns (subst bnd n) in
      (b, n_elab :: ns_elab, Usage.merge usg1 usg2)
    | _ -> failwith "Logical.infer_tele"

  and check_tm res ctx env m0 a0 =
    match (m0, whnf env a0) with
    (* core *)
    | Lam (rel0, s0, a0, bnd0), Pi (rel1, s1, a1, bnd1)
      when rel0 = rel1 && eq_sort s0 s1 -> (
      let _ = Logical.assert_sort s0 in
      let x, m, b = unbind2 bnd0 bnd1 in
      let t = Logical.infer_sort res ctx env a0 in
      let _ = Logical.assert_equal env a0 a1 in
      let m_elab, usg = check_tm res (Context.add_var x a1 t ctx) env m b in
      let usg = Usage.remove_var x usg rel0 t in
      let m_bnd = Syntax2.(bind_var (trans_var x) m_elab) in
      match s0 with
      | U ->
        let _ = Usage.assert_pure usg in
        Syntax2.(_Lam U m_bnd, usg)
      | L -> Syntax2.(_Lam L m_bnd, usg)
      | _ -> failwith "Program.check_Lam")
    | Let (N, m, bnd), a0 ->
      let x, n = unbind bnd in
      let a = Logical.infer_tm res ctx env m in
      let s = Logical.infer_sort res ctx env a in
      let ctx = Context.add_var x a s ctx in
      let env = Env.add_var x m env in
      let n_elab, usg = check_tm res ctx env n a0 in
      let usg = Usage.remove_var x usg N s in
      Syntax2.(_Let _NULL (bind_var (trans_var x) n_elab), usg)
    | Let (R, m, bnd), a0 ->
      let x, n = unbind bnd in
      let a, m_elab, usg1 = infer_tm res ctx env m in
      let s = Logical.infer_sort res ctx env a in
      let ctx = Context.add_var x a s ctx in
      let env = Env.add_var x m env in
      let n_elab, usg2 = check_tm res ctx env n a0 in
      let usg = Usage.(merge usg1 (remove_var x usg2 R s)) in
      Syntax2.(_Let m_elab (bind_var (trans_var x) n_elab), usg)
    (* data *)
    | Pair (N, s0, m, n), Sigma (N, s1, a, bnd) when eq_sort s0 s1 ->
      let _ = Logical.assert_sort s0 in
      let _ = Logical.check_tm res ctx env m a in
      let n_elab, usg = check_tm res ctx env n (subst bnd (Ann (m, a))) in
      Syntax2.(_Pair _NULL n_elab, usg)
    | Pair (R, s0, m, n), Sigma (R, s1, a, bnd) when eq_sort s0 s1 ->
      let _ = Logical.assert_sort s0 in
      let m_elab, usg1 = check_tm res ctx env m a in
      let n_elab, usg2 = check_tm res ctx env n (subst bnd (Ann (m, a))) in
      Syntax2.(_Pair m_elab n_elab, Usage.merge usg1 usg2)
    | Match (m, mot, cls), a0 -> (
      let ty_m, m_elab, usg1 = infer_tm res ctx env m in
      let a1 = subst mot m in
      let _ = Logical.infer_sort res ctx env a1 in
      let _ = Logical.assert_equal env a0 a1 in
      let s = Logical.infer_sort res ctx env ty_m in
      match whnf env ty_m with
      | Unit ->
        let cls_elab, usg2 = infer_unit res ctx env mot cls in
        let usg = Usage.merge usg1 usg2 in
        Syntax2.(_Match (trans_sort s) m_elab (box_list cls_elab), usg)
      | Bool ->
        let cls_elab, usg2 = infer_bool res ctx env mot cls in
        let usg = Usage.merge usg1 usg2 in
        Syntax2.(_Match (trans_sort s) m_elab (box_list cls_elab), usg)
      | Nat ->
        let cls_elab, usg2 = infer_nat res ctx env mot cls in
        let usg = Usage.merge usg1 usg2 in
        Syntax2.(_Match (trans_sort s) m_elab (box_list cls_elab), usg)
      | Sigma (rel, _, a, bnd) ->
        let cls_elab, usg2 = infer_pair res ctx env rel s a bnd mot cls in
        let usg = Usage.merge usg1 usg2 in
        Syntax2.(_Match (trans_sort s) m_elab (box_list cls_elab), usg)
      | Data (d0, ss, ms) ->
        let d1 = Resolver.find_data d0 ss res in
        let _, cs = Context.find_data d1 ctx in
        let cls_elab, usg2 = infer_cls res ctx env cs ss ms mot cls in
        let usg = Usage.merge usg1 usg2 in
        Syntax2.(_Match (trans_sort s) m_elab (box_list cls_elab), usg)
      | _ -> failwith "Program.check_Match")
    (* core *)
    | m0, a0 ->
      let a1, m_elab, usg = infer_tm res ctx env m0 in
      let _ = Logical.assert_equal env a0 a1 in
      (m_elab, usg)
end

let const_extend x ss =
  match ss with
  | [] -> x
  | _ ->
    let ss = String.concat "" (List.map (str "%a" pp_sort) ss) in
    I.extend x ss

let data_extend d ss =
  match ss with
  | [] -> d
  | _ ->
    let ss = String.concat "" (List.map (str "%a" pp_sort) ss) in
    D.extend d ss

let cons_extend c ss =
  match ss with
  | [] -> c
  | _ ->
    let ss = String.concat "" (List.map (str "%a" pp_sort) ss) in
    C.extend c ss

let make_init xs =
  let rec loop xs =
    match xs with
    | [] -> [ [] ]
    | _ :: xs ->
      let ss = loop xs in
      let ssU = List.(map (cons U)) ss in
      let ssL = List.(map (cons L)) ss in
      ssU @ ssL
  in
  loop (Array.to_list xs)

let rec check_dcls res ctx env = function
  | [] -> ([], res, Usage.empty)
  | DTm (R, x0, false, sch) :: _ when I.is_main x0 -> (
    let sargs, (a, m) = unmbind sch in
    match sargs with
    | [||] ->
      let ty = IO Unit in
      let _ = Logical.assert_equal env a ty in
      let m_elab, usg = Program.check_tm res ctx env m a in
      Syntax2.([ _DMain m_elab ], res, usg)
    | _ -> failwith "check_dcls_Main")
  | DTm (N, x0, guard, sch) :: dcls ->
    let sargs, _ = unmbind sch in
    let init = make_init sargs in
    let res_acc, ctx, env_acc, xs =
      List.fold_right
        (fun ss (res_acc, ctx_acc, env_acc, xs) ->
          let x1 = const_extend x0 ss in
          try
            let a, m = msubst sch (Array.of_list ss) in
            let s = Logical.infer_sort res ctx env a in
            let _ =
              if guard then
                let res = Resolver.(add_const x0 (RMap.singleton ss x1) res) in
                let ctx = Context.(add_const x1 a s ctx) in
                Logical.check_tm res ctx env m a
              else
                Logical.check_tm res ctx env m a
            in
            Resolver.
              ( RMap.add ss x1 res_acc
              , Context.add_const x1 a s ctx_acc
              , RMap.add ss m env_acc
              , (x1, s) :: xs )
          with
          | e ->
            let _ = epr "pruned_const(%a, %a)@." I.pp x1 exn e in
            (res_acc, ctx_acc, env_acc, xs))
        init
        Resolver.(RMap.empty, ctx, RMap.empty, [])
    in
    let res = Resolver.add_const x0 res_acc res in
    let env =
      Env.add_const x0
        { scheme = (fun ss -> Resolver.RMap.find ss env_acc); guarded = guard }
        env
    in
    let dcls_elab, res, usg = check_dcls res ctx env dcls in
    let usg =
      List.fold_left (fun acc (x, s) -> Usage.remove_const x acc N s) usg xs
    in
    (dcls_elab, res, usg)
  | DTm (R, x0, guard, sch) :: dcls ->
    let sargs, _ = unmbind sch in
    let init = make_init sargs in
    let dtm_elab, res_acc, ctx, env_acc, xs, usg1 =
      List.fold_right
        (fun ss (dtm_elab, res_acc, ctx_acc, env_acc, xs, usg_acc) ->
          let x1 = const_extend x0 ss in
          try
            let a, m = msubst sch (Array.of_list ss) in
            let s = Logical.infer_sort res ctx env a in
            let m_elab, usg =
              if guard then
                let res = Resolver.(add_const x0 (RMap.singleton ss x1) res) in
                let ctx = Context.(add_const x1 a s ctx) in
                let m_elab, usg = Program.check_tm res ctx env m a in
                let usg = Usage.remove_const x1 usg R s in
                let _ = Usage.assert_pure usg in
                (m_elab, usg)
              else
                Program.check_tm res ctx env m a
            in
            Resolver.
              ( Syntax2.(_DTm x1 m_elab) :: dtm_elab
              , RMap.add ss x1 res_acc
              , Context.add_const x1 a s ctx_acc
              , RMap.add ss m env_acc
              , (x1, s) :: xs
              , Usage.merge usg usg_acc )
          with
          | e ->
            let _ = epr "pruned_const(%a, %a)@." I.pp x1 exn e in
            (dtm_elab, res_acc, ctx_acc, env_acc, xs, usg_acc))
        init
        Resolver.([], RMap.empty, ctx, RMap.empty, [], Usage.empty)
    in
    let res = Resolver.add_const x0 res_acc res in
    let env =
      Env.add_const x0
        { scheme = (fun ss -> Resolver.RMap.find ss env_acc); guarded = guard }
        env
    in
    let dcls_elab, res, usg2 = check_dcls res ctx env dcls in
    let usg2 =
      List.fold_left (fun acc (x, s) -> Usage.remove_const x acc R s) usg2 xs
    in
    (dtm_elab @ dcls_elab, res, Usage.merge usg1 usg2)
  | DData (d0, sch, dconss) :: dcls ->
    let sargs, _ = unmbind sch in
    let init = make_init sargs in
    let ddata_elab, res, ctx =
      List.fold_right
        (fun ss (ddata_elab, res_acc, ctx_acc) ->
          let d1 = data_extend d0 ss in
          try
            let ptm = msubst sch (Array.of_list ss) in
            let _ = check_ptm res ctx env ptm in
            let res = Resolver.(add_data d0 ss d1 res) in
            let ctx = Context.(add_data d1 ptm CSet.empty ctx) in
            let dconss_elab, res_acc, ctx_acc, cs =
              check_dconss ss res ctx env d0 dconss res_acc ctx_acc
            in
            let res_acc = Resolver.(add_data d0 ss d1 res_acc) in
            let ctx_acc = Context.(add_data d1 ptm cs ctx_acc) in
            match dconss_elab with
            | [] -> (ddata_elab, res_acc, ctx_acc)
            | _ ->
              Syntax2.
                ( _DData d1 (box_list dconss_elab) :: ddata_elab
                , res_acc
                , ctx_acc )
          with
          | e ->
            let _ = epr "pruned_data(%a, %a)@." D.pp d1 exn e in
            (ddata_elab, res_acc, ctx_acc))
        init
        Resolver.([], res, ctx)
    in
    let dcls_elab, res, usg = check_dcls res ctx env dcls in
    (ddata_elab @ dcls_elab, res, usg)

and check_ptm res ctx env ptm =
  match ptm with
  | PBase (Type U) -> ()
  | PBase (Type L) -> ()
  | PBind (a, bnd) ->
    let x, ptm = unbind bnd in
    let s = Logical.infer_sort res ctx env a in
    check_ptm res (Context.add_var x a s ctx) env ptm
  | _ -> failwith "check_ptm"

and check_dconss ss res ctx env d0 dconss res_acc ctx_acc =
  match dconss with
  | [] -> ([], res_acc, ctx_acc, CSet.empty)
  | DCons (c0, sch) :: dconss -> (
    let c1 = cons_extend c0 ss in
    let opt =
      try
        let ptl = msubst sch (Array.of_list ss) in
        let i = check_ptl res ctx env d0 ptl in
        Some Syntax2.(_DCons c1 i, ptl)
      with
      | e ->
        let _ = epr "pruned_cons(%a, %a)@." C.pp c1 exn e in
        None
    in
    let dconss_elab, res_acc, ctx_acc, cs =
      check_dconss ss res ctx env d0 dconss res_acc ctx_acc
    in
    match opt with
    | Some (dcons_elab, ptl) ->
      let res_acc = Resolver.add_cons c0 ss c1 res_acc in
      let ctx_acc = Context.add_cons c1 ptl ctx_acc in
      Syntax2.(dcons_elab :: dconss_elab, res_acc, ctx_acc, CSet.add c1 cs)
    | None -> (dconss_elab, res_acc, ctx_acc, cs))

and check_ptl res ctx env d0 ptl =
  match ptl with
  | PBase tl -> fst (check_tl res ctx env d0 tl)
  | PBind (a, bnd) ->
    let x, ptl = unbind bnd in
    let s = Logical.infer_sort res ctx env a in
    check_ptl res (Context.add_var x a s ctx) env d0 ptl

and check_tl res ctx env d0 tl =
  match tl with
  | TBase (Data (d, _, _) as a) when D.equal d d0 ->
    let t = Logical.infer_sort res ctx env a in
    (0, t)
  | TBind (N, a, bnd) ->
    let x, tl = unbind bnd in
    let s = Logical.infer_sort res ctx env a in
    let i, t = check_tl res (Context.add_var x a s ctx) env d0 tl in
    (i + 1, t)
  | TBind (R, a, bnd) ->
    let x, tl = unbind bnd in
    let s = Logical.infer_sort res ctx env a in
    let i, t = check_tl res (Context.add_var x a s ctx) env d0 tl in
    if s <= t then
      (i + 1, t)
    else
      failwith "check_tl"
  | _ -> failwith "check_tl"

let trans_dcls dcls =
  let dcls, res, usg = check_dcls Resolver.empty Context.empty Env.empty dcls in
  let _ = Usage.assert_empty usg in
  (unbox (box_list dcls), res)
