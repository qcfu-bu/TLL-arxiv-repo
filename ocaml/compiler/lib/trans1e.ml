open Fmt
open Bindlib
open Names
open Syntax1
open Equality1
open Unify1
open Pprint1

type ctx =
  { (* types for variables *)
    var : tm VMap.t
  ; (* sort variables in scope *)
    svar : SVSet.t
  ; (* type-schemes for constants *)
    const : tm scheme IMap.t
  ; (* type-schemes for data *)
    data : (tm param scheme * CSet.t) DMap.t
  ; (* type-schemes for constructors *)
    cons : tele param scheme CMap.t
  }

(* context of meta-variables *)
type mctx = tm MMap.t

let add_var x a ctx = { ctx with var = VMap.add x a ctx.var }

let add_svar xs ctx =
  let svar = SVSet.of_list (Array.to_list xs) in
  { ctx with svar = SVSet.union svar ctx.svar }

let add_const x sch ctx = { ctx with const = IMap.add x sch ctx.const }
let add_data d sch cs ctx = { ctx with data = DMap.add d (sch, cs) ctx.data }
let add_cons c sch ctx = { ctx with cons = CMap.add c sch ctx.cons }

let find_var x ctx =
  match VMap.find_opt x ctx.var with
  | Some a -> a
  | None -> failwith "trans1e.find_var(%a)" V.pp x

let find_const x ctx =
  match IMap.find_opt x ctx.const with
  | Some sch -> sch
  | None -> failwith "trans1e.find_const(%a)" I.pp x

let find_data d ctx =
  match DMap.find_opt d ctx.data with
  | Some res -> res
  | None -> failwith "trans1e.find_data(%a)" D.pp d

let find_cons c ctx =
  match CMap.find_opt c ctx.cons with
  | Some sch -> sch
  | None -> failwith "trans1e.find_cons(%a)" C.pp c

let smeta_mk ctx =
  let x = M.mk () in
  let ss = ctx.svar |> SVSet.elements |> List.map (fun x -> SVar x) in
  (SMeta (x, ss), x)

let meta_mk ctx =
  let x = M.mk () in
  let ss = ctx.svar |> SVSet.elements |> List.map (fun x -> SVar x) in
  let xs = ctx.var |> VMap.bindings |> List.map (fun x -> Var (fst x)) in
  (Meta (x, ss, xs), x)

(* monad for collecting unification constraints *)
type 'a trans1e = mctx * eqns * map0 * map1 -> 'a * mctx * eqns * map0 * map1

let return (a : 'a) : 'a trans1e =
 fun (mctx, eqns, map0, map1) -> (a, mctx, eqns, map0, map1)

let ( >>= ) (m : 'a trans1e) (f : 'a -> 'b trans1e) : 'b trans1e =
 fun (mctx, eqns, map0, map1) ->
  let a, mctx, eqns, map0, map1 = m (mctx, eqns, map0, map1) in
  (f a) (mctx, eqns, map0, map1)

let ( >> ) (m : 'a trans1e) (n : 'b trans1e) : 'b trans1e =
 fun (mctx, eqns, map0, map1) ->
  let _, mctx, eqns, map0, map1 = m (mctx, eqns, map0, map1) in
  n (mctx, eqns, map0, map1)

let ( let* ) = ( >>= )

let run_trans1e (m : 'a trans1e) : 'a * mctx * eqns * map0 * map1 =
  m (MMap.empty, [], MMap.empty, MMap.empty)

let find_meta x ctx : tm trans1e =
 fun (mctx, eqns, map0, map1) ->
  match MMap.find_opt x mctx with
  | Some a -> (a, mctx, eqns, map0, map1)
  | None ->
    let a, _ = meta_mk ctx in
    (a, MMap.add x a mctx, eqns, map0, map1)

let add_meta env x a : unit trans1e =
 fun (mctx, eqns, map0, map1) ->
  match MMap.find_opt x mctx with
  | Some b -> ((), mctx, Eqn1 (env, a, b) :: eqns, map0, map1)
  | None -> ((), MMap.add x a mctx, eqns, map0, map1)

let unify : unit trans1e =
 fun (mctx, eqns, map0, map1) ->
  let map0, map1 = unify (map0, map1) eqns in
  ((), mctx, eqns, map0, map1)

let resolve_ptm ptm : tm param trans1e =
 fun (mctx, eqns, map0, map1) ->
  let ptm = resolve_param lift_tm resolve_tm (map0, map1) ptm in
  (ptm, mctx, eqns, map0, map1)

let resolve_ptl ptl : tele param trans1e =
 fun (mctx, eqns, map0, map1) ->
  let ptl = resolve_param lift_tele resolve_tele (map0, map1) ptl in
  (ptl, mctx, eqns, map0, map1)

let resolve_tm m : tm trans1e =
 fun (mctx, eqns, map0, map1) ->
  let m = resolve_tm (map0, map1) m in
  (m, mctx, eqns, map0, map1)

(* assert equality between two sorts *)
let assert_equal0 s1 s2 : unit trans1e =
 fun (mctx, eqns, map0, map1) ->
  if eq_sort s1 s2 then
    ((), mctx, eqns, map0, map1)
  else
    ((), mctx, Eqn0 (s1, s2) :: eqns, map0, map1)

(* assert equality between two terms *)
let rec assert_equal1 ctx env m n : unit trans1e =
 fun (mctx, eqns, map0, map1) ->
  if eq_tm env m n then
    ((), mctx, eqns, map0, map1)
  else
    let m = Unify1.resolve_tm (map0, map1) m in
    let n = Unify1.resolve_tm (map0, map1) n in
    let eqns1 = simpl (Eqn1 (env, m, n)) in
    let mctx, eqns, map0, map1 =
      List.fold_left
        (fun (mctx, eqns, map0, map1) eqn ->
          match eqn with
          | Eqn0 _ -> (mctx, eqn :: eqns, map0, map1)
          | Eqn1 (env, m, n) ->
            let a, mctx, eqns, map0, map1 =
              infer_tm ctx env m (mctx, eqns, map0, map1)
            in
            let b, mctx, eqns, map0, map =
              infer_tm ctx env n (mctx, eqns, map0, map1)
            in
            (mctx, Eqn1 (env, a, b) :: eqn :: eqns, map0, map1))
        (mctx, eqns, map0, map1) eqns1
    in
    ((), mctx, eqns, map0, map1)

(* assert equality between terms and their sorts *)
and assert_equal ctx env (m, s1) (n, s2) : unit trans1e =
  (* let _ = pr "assert_equal(%a ==== %a)@." pp_tm m pp_tm n in *)
  let* _ = assert_equal0 s1 s2 in
  let* _ = assert_equal1 ctx env m n in
  return ()

(* assert the sort of a type *)
and infer_sort ctx env a : sort trans1e =
  let* srt = infer_tm ctx env a in
  let* srt = resolve_tm srt in
  match whnf env srt with
  | Type s -> return s
  | _ ->
    let s, _ = smeta_mk ctx in
    let* _ = assert_equal1 ctx env srt (Type s) in
    return s

and infer_tm ctx env m0 : tm trans1e =
  (* let _ = pr "infer_tm(%a)@." pp_tm m0 in *)
  match m0 with
  (* inference *)
  | Ann (m, a) ->
    let* _ = infer_sort ctx env a in
    let* _ = check_tm ctx env m a in
    return a
  | Meta (x, _, _) -> find_meta x ctx
  (* core *)
  | Type _ -> return (Type U)
  | Var x -> return (find_var x ctx)
  | Const (x, ss) ->
    let sch = find_const x ctx in
    return (msubst sch (Array.of_list ss))
  | Pi (rel, s, a, bnd) ->
    let x, b = unbind bnd in
    let* _ = infer_sort ctx env a in
    let* _ = infer_sort (add_var x a ctx) env b in
    return (Type s)
  | Lam (rel, s, a, bnd) ->
    let x, m = unbind bnd in
    let* _ = infer_sort ctx env a in
    let* b = infer_tm (add_var x a ctx) env m in
    let bnd = bind_var x (lift_tm b) in
    return (Pi (rel, s, a, unbox bnd))
  | App (m, n) -> (
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf env ty_m with
    | Pi (_, _, a, bnd) ->
      let* _ = check_tm ctx env n a in
      return (subst bnd n)
    | _ -> failwith "trans1e.infer_App(%a)" pp_tm m0)
  | Let (rel, m, bnd) ->
    let x, n = unbind bnd in
    let* a = infer_tm ctx env m in
    let* a = unify >> resolve_tm a in
    infer_tm (add_var x a ctx) (Env.add_var x m env) n
  (* native *)
  | Unit s -> return (Type s)
  | UIt s -> return (Unit s)
  | Bool -> return (Type U)
  | BTrue -> return Bool
  | BFalse -> return Bool
  | Nat -> return (Type U)
  | NZero -> return Nat
  | NSucc (_, m) ->
    let* _ = check_tm ctx env m Nat in
    return Nat
  (* data *)
  | Sigma (_, _, s, a, bnd) ->
    let x, b = unbind bnd in
    let* _ = infer_sort ctx env a in
    let* _ = infer_sort (add_var x a ctx) env b in
    return (Type s)
  | Pair (rel1, rel2, s, m, n) ->
    let* a = infer_tm ctx env m in
    let* b = infer_tm ctx env n in
    let x = V.mk "_" in
    let bnd = bind_var x (lift_tm b) in
    return (Sigma (rel1, rel2, s, a, unbox bnd))
  | Data (d, ss, ms) ->
    let sch, _ = find_data d ctx in
    let ptm = msubst sch (Array.of_list ss) in
    infer_ptm ctx env ms ptm
  | Cons (c, ss, ms, ns) ->
    let sch = find_cons c ctx in
    let ptl = msubst sch (Array.of_list ss) in
    infer_ptl ctx env ms ns ptl
  | Match (_, m, mot, cls) -> (
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf env ty_m with
    | Unit s ->
      let* _ = infer_unit ctx env mot cls s in
      return (subst mot m)
    | Bool ->
      let* _ = infer_bool ctx env mot cls in
      return (subst mot m)
    | Nat ->
      let* _ = infer_nat ctx env mot cls in
      return (subst mot m)
    | Sigma (rel1, rel2, s, a, bnd) ->
      let* _ = infer_pair ctx env rel1 rel2 s a bnd mot cls in
      return (subst mot m)
    | Data (d, ss, ms) ->
      let _, cs = find_data d ctx in
      let* _ = infer_cls ctx env cs ss ms mot cls in
      return (subst mot m)
    | _ -> failwith "trans1e.infer_Match(%a, %a)" pp_tm m0 pp_tm ty_m)
  (* absurd *)
  | Bot -> return (Type U)
  | Absurd (a, m) ->
    let* _ = infer_sort ctx env a in
    let* _ = check_tm ctx env m Bot in
    return a
  (* equality *)
  | Eq (a, m, n) ->
    let* _ = infer_sort ctx env a in
    let* _ = check_tm ctx env m a in
    let* _ = check_tm ctx env n a in
    return (Type U)
  | Refl m ->
    let* a = infer_tm ctx env m in
    return (Eq (a, m, m))
  | Rew (bnd, p, h) -> (
    let xs, mot = unmbind bnd in
    let* ty_p = infer_tm ctx env p in
    let* ty_p = unify >> resolve_tm ty_p in
    match (whnf env ty_p, xs) with
    | Eq (a, m, n), [| x; y |] ->
      let ctx' = add_var x a ctx in
      let ctx' = add_var y (Eq (a, m, Var x)) ctx' in
      let* _ = infer_sort ctx' env mot in
      let* _ = check_tm ctx env h (msubst bnd [| m; Refl m |]) in
      return (msubst bnd [| n; p |])
    | _ -> failwith "trans1e.infer_Rew(%a)" pp_tm m0)
  (* monadic *)
  | IO a ->
    let* _ = infer_sort ctx env a in
    return (Type L)
  | Return m ->
    let* a = infer_tm ctx env m in
    return (IO a)
  | MLet (m, bnd) -> (
    let x, n = unbind bnd in
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf env ty_m with
    | IO a -> (
      let* ty_n = infer_tm (add_var x a ctx) env n in
      let* ty_n = unify >> resolve_tm ty_n in
      match whnf env ty_n with
      | IO b -> return (IO b)
      | ty_n ->
        let b, _ = meta_mk ctx in
        let* _ = assert_equal ctx env (ty_n, L) (IO b, L) in
        return (IO b))
    | _ -> failwith "trans1e.infer_MLet(%a, %a)" pp_tm m pp_tm ty_m)
  (* session *)
  | Proto -> return (Type U)
  | End -> return Proto
  | Act (_, _, a, bnd) ->
    let x, b = unbind bnd in
    let* _ = infer_sort ctx env a in
    let* _ = check_tm (add_var x a ctx) env b Proto in
    return Proto
  | Ch (_, a) ->
    let* _ = check_tm ctx env a Proto in
    return (Type L)
  | Open Stdin -> return (IO (Ch (Pos, Const (Prelude1.stdin_t_i, []))))
  | Open Stdout -> return (IO (Ch (Pos, Const (Prelude1.stdout_t_i, []))))
  | Open Stderr -> return (IO (Ch (Pos, Const (Prelude1.stderr_t_i, []))))
  | Fork (a0, bnd) -> (
    let x, m = unbind bnd in
    let* _ = infer_sort ctx env a0 in
    let* a0 = unify >> resolve_tm a0 in
    match whnf env a0 with
    | Ch (Pos, a) ->
      let ty = IO (Unit U) in
      let* _ = check_tm (add_var x a0 ctx) env m ty in
      return (IO (Ch (Neg, a)))
    | _ -> failwith "trans1e.infer_Fork")
  | Recv m -> (
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf env ty_m with
    | Ch (rol1, Act (rel, rol2, a, bnd)) when rol1 <> rol2 = true ->
      let x, b = unbind bnd in
      let bnd = unbox (bind_var x (lift_tm (Ch (rol1, b)))) in
      return (IO (Sigma (rel, R, L, a, bnd)))
    | ty -> failwith "trans1e.infer_Recv(%a)" pp_tm ty)
  | Send m -> (
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf env ty_m with
    | Ch (rol1, Act (rel, rol2, a, bnd)) when rol1 <> rol2 = false ->
      let x, b = unbind bnd in
      let bnd = unbox (bind_var x (lift_tm (IO (Ch (rol1, b))))) in
      return (Pi (rel, L, a, bnd))
    | ty -> failwith "trans1e.infer_Send(%a)" pp_tm ty)
  | Close m -> (
    let* ty_m = infer_tm ctx env m in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf env ty_m with
    | Ch (_, End) -> return (IO (Unit U))
    | ty -> failwith "trans1e.infer_Close(%a)" pp_tm ty)
  (* effects *)
  | Sleep m ->
    let* _ = check_tm ctx env m Nat in
    return (IO (Unit U))
  | Rand (m, n) ->
    let* _ = check_tm ctx env m Nat in
    let* _ = check_tm ctx env n Nat in
    let n = mkApps (Const (Prelude1.addn_i, [])) [ m; n ] in
    return (IO (Data (Prelude1.between_d, [], [ m; n ])))

and infer_unit ctx env mot cls s0 =
  match cls with
  | [ PIt (s, rhs) ] when eq_sort s s0 ->
    let mot = subst mot (UIt s0) in
    let* _ = infer_sort ctx env mot in
    check_tm ctx env rhs mot
  | _ -> failwith "trans1e.infer_unit"

and infer_bool ctx env mot cls =
  match cls with
  | [ PTrue rhs1; PFalse rhs2 ] ->
    let mot1 = subst mot BTrue in
    let mot2 = subst mot BFalse in
    let* _ = infer_sort ctx env mot1 in
    let* _ = infer_sort ctx env mot2 in
    let* _ = check_tm ctx env rhs1 mot1 in
    let* _ = check_tm ctx env rhs2 mot2 in
    return ()
  | [ PFalse rhs2; PTrue rhs1 ] ->
    let mot1 = subst mot BTrue in
    let mot2 = subst mot BFalse in
    let* _ = infer_sort ctx env mot1 in
    let* _ = infer_sort ctx env mot2 in
    let* _ = check_tm ctx env rhs1 mot1 in
    let* _ = check_tm ctx env rhs2 mot2 in
    return ()
  | _ -> failwith "trans1e.infer_bool"

and infer_nat ctx1 env mot cls =
  match cls with
  | [ PZero rhs1; PSucc bnd ] ->
    let x, rhs2 = unbind bnd in
    let ctx2 = add_var x Nat ctx1 in
    let mot1 = subst mot NZero in
    let mot2 = subst mot (NSucc (1, Var x)) in
    let* _ = infer_sort ctx1 env mot1 in
    let* _ = infer_sort ctx2 env mot2 in
    let* _ = check_tm ctx1 env rhs1 mot1 in
    let* _ = check_tm ctx2 env rhs2 mot2 in
    return ()
  | [ PSucc bnd; PZero rhs1 ] ->
    let x, rhs2 = unbind bnd in
    let ctx2 = add_var x Nat ctx1 in
    let mot1 = subst mot NZero in
    let mot2 = subst mot (NSucc (1, Var x)) in
    let* _ = infer_sort ctx1 env mot1 in
    let* _ = infer_sort ctx2 env mot2 in
    let* _ = check_tm ctx1 env rhs1 mot1 in
    let* _ = check_tm ctx2 env rhs2 mot2 in
    return ()
  | _ -> failwith "trans1e.infer_nat"

and infer_pair ctx env rel1 rel2 s a b mot cls =
  match cls with
  | [ PPair (r1, r2, s0, bnd) ] when r1 = rel1 && r2 = rel2 -> (
    let* _ = assert_equal0 s s0 in
    let xs, rhs = unmbind bnd in
    match xs with
    | [| x; y |] ->
      let ctx = add_var x a ctx in
      let ctx = add_var y (subst b (Var x)) ctx in
      let tm = Pair (rel1, rel2, s, Var x, Var y) in
      let ty = Sigma (rel1, rel2, s, a, b) in
      let mot = subst mot (Ann (tm, ty)) in
      let* _ = infer_sort ctx env mot in
      check_tm ctx env rhs mot
    | _ -> failwith "trans1e.infer_pair0")
  | _ ->
    failwith "trans1e.infer_pair1(%a, %a, %a)" pp_cls cls pp_rel rel1 pp_rel
      rel2

and infer_cls ctx env cs ss ms mot cls =
  match cls with
  | [] -> return ()
  | PCons (c, bnd) :: cls -> (
    match CSet.find_opt c cs with
    | Some _ ->
      let* _ = infer_cl ctx env ss ms mot c bnd in
      infer_cls ctx env cs ss ms mot cls
    | _ -> failwith "trans1e.infer_cls")
  | _ -> failwith "trans1e.infer_cls"

and infer_cl ctx env ss ms mot c bnd =
  let rec init_param ms ptl =
    match (ms, ptl) with
    | [], PBase tl -> tl
    | m :: ms, PBind (a, bnd) -> init_param ms (subst bnd (Ann (m, a)))
    | _ -> failwith "trans1e.init_param"
  in
  let rec init_tele ctx xs tl =
    match (xs, tl) with
    | [], TBase b -> (ctx, b)
    | x :: xs, TBind (_, a, bnd) ->
      let ctx = add_var x a ctx in
      let tl = subst bnd (Var x) in
      init_tele ctx xs tl
    | _ -> failwith "trans1e.init_tele"
  in
  let xs, rhs = unmbind bnd in
  let xs = Array.to_list xs in
  let sch = find_cons c ctx in
  let ptl = msubst sch (Array.of_list ss) in
  let tl = init_param ms ptl in
  let ctx, ty = init_tele ctx xs tl in
  let* _ = infer_sort ctx env ty in
  let mot = subst mot (Cons (c, ss, ms, List.map var xs)) in
  let* _ = infer_sort ctx env mot in
  let* _ = check_tm ctx env rhs mot in
  return ()

and infer_ptm ctx env ms ptm =
  match (ms, ptm) with
  | [], PBase b ->
    let* _ = infer_sort ctx env b in
    return b
  | m :: ms, PBind (a, bnd) ->
    let* _ = check_tm ctx env m a in
    infer_ptm ctx env ms (subst bnd m)
  | _ -> failwith "trans1e.infer_ptm(%a)" pp_ptm ptm

and infer_ptl ctx env ms ns ptl =
  match (ms, ptl) with
  | [], PBase tl -> infer_tele ctx env ns tl
  | m :: ms, PBind (a, bnd) ->
    let* _ = check_tm ctx env m a in
    infer_ptl ctx env ms ns (subst bnd m)
  | _ -> failwith "trans1e.infer_ptl(%a)" pp_ptl ptl

and infer_tele ctx env ns tl =
  match (ns, tl) with
  | [], TBase b ->
    let* _ = infer_sort ctx env b in
    return b
  | n :: ns, TBind (_, a, bnd) ->
    let* _ = check_tm ctx env n a in
    infer_tele ctx env ns (subst bnd n)
  | _ -> failwith "trans1e.infer_tele(%a)" pp_tele tl

and check_tm ctx env m0 a0 : unit trans1e =
  (* let _ = pr "check_tm(%a <====== %a)@." pp_tm m0 pp_tm a0 in *)
  let* a0 = unify >> resolve_tm a0 in
  match (m0, whnf env a0) with
  (* inference *)
  | Meta (x, _, _), a0 -> add_meta env x a0
  | Ann (m, a1), a0 ->
    let* s0 = infer_sort ctx env a0 in
    let* s1 = infer_sort ctx env a1 in
    let* _ = assert_equal ctx env (a0, s0) (a1, s1) in
    let* a1 = unify >> resolve_tm a1 in
    check_tm ctx env m a1
  (* core *)
  | Lam (rel0, s0, a0, bnd0), Pi (rel1, s1, a1, bnd1) when rel0 = rel1 ->
    let x, m, b = unbind2 bnd0 bnd1 in
    let* t0 = infer_sort ctx env a0 in
    let* t1 = infer_sort ctx env a1 in
    let* _ = assert_equal0 s0 s1 in
    let* _ = assert_equal ctx env (a0, t0) (a1, t1) in
    check_tm (add_var x a1 ctx) env m b
  | Let (rel, m, bnd), a0 ->
    let x, n = unbind bnd in
    let* a = infer_tm ctx env m in
    let* a = unify >> resolve_tm a in
    let* m = unify >> resolve_tm m in
    check_tm (add_var x a ctx) (Env.add_var x m env) n a0
  (* data *)
  | Pair (rel11, rel12, s0, m, n), Sigma (rel21, rel22, s1, a, bnd)
    when rel11 = rel21 && rel12 = rel22 ->
    let* _ = assert_equal0 s0 s1 in
    let* _ = check_tm ctx env m a in
    check_tm ctx env n (subst bnd (Ann (m, a)))
  | Cons (c, ss0, ms0, ns), (Data (d, ss1, ms1) as a0) ->
    let sch = find_cons c ctx in
    let ptl = msubst sch (Array.of_list ss0) in
    check_ptl ctx env ms0 ns ptl ms1 a0
  | Match (_, m, mot, cls), a0 -> (
    let* ty_m = infer_tm ctx env m in
    let a1 = subst mot m in
    let* s0 = infer_sort ctx env a0 in
    let* s1 = infer_sort ctx env a1 in
    let* _ = assert_equal ctx env (a0, s0) (a1, s1) in
    let* ty_m = unify >> resolve_tm ty_m in
    match whnf env ty_m with
    | Unit s -> infer_unit ctx env mot cls s
    | Bool -> infer_bool ctx env mot cls
    | Nat -> infer_nat ctx env mot cls
    | Sigma (rel1, rel2, srt, a, bnd) ->
      infer_pair ctx env rel1 rel2 srt a bnd mot cls
    | Data (d, ss, ms) ->
      let _, cs = find_data d ctx in
      infer_cls ctx env cs ss ms mot cls
    | _ ->
      let* a1 = infer_tm ctx env m0 in
      let* s0 = infer_sort ctx env a0 in
      let* s1 = infer_sort ctx env a1 in
      let* _ = assert_equal ctx env (a0, s0) (a1, s1) in
      return ())
  (* other *)
  | m0, a0 ->
    let* a1 = infer_tm ctx env m0 in
    let* s0 = infer_sort ctx env a0 in
    let* s1 = infer_sort ctx env a1 in
    let* _ = assert_equal ctx env (a0, s0) (a1, s1) in
    return ()

and check_ptl ctx env ms0 ns ptl ms1 a =
  (* let _ = pr "check_ptl(%a)@." pp_ptl ptl in *)
  match (ms0, ms1, ptl) with
  | [], [], PBase b -> check_tele ctx env ns b a
  | m0 :: ms0, m1 :: ms1, PBind (a0, bnd) ->
    let* _ = check_tm ctx env m0 a0 in
    let* _ = assert_equal1 ctx env m0 m1 in
    check_ptl ctx env ms0 ns (subst bnd m0) ms1 a
  | _ -> failwith "trans1e.check_ptl(%a)" pp_ptl ptl

and check_tele ctx env ns tl a =
  match (ns, tl) with
  | [], TBase b ->
    let* s0 = infer_sort ctx env a in
    let* s1 = infer_sort ctx env b in
    let* _ = unify >> resolve_tm b in
    let* _ = assert_equal ctx env (a, s0) (b, s1) in
    return ()
  | n :: ns, TBind (_, a0, bnd) ->
    let* _ = check_tm ctx env n a0 in
    check_tele ctx env ns (subst bnd n) a
  | _ -> failwith "trans1e.check_tele(%a)" pp_tele tl

let rec check_dcls ctx env dcls =
  match dcls with
  | [] -> return ()
  | DTm (_, x, guard, sch) :: dcls ->
    let xs, (a, m) = unmbind sch in
    let sch_a = unbox (bind_mvar xs (lift_tm a)) in
    let ctx' = add_svar xs ctx in
    let* _ = infer_sort ctx' env a in
    let* _ =
      if guard then
        check_tm (add_const x sch_a ctx') env m a
      else
        check_tm ctx' env m a
    in
    let* a = unify >> resolve_tm a in
    let* m = unify >> resolve_tm m in
    let sch_a = unbox (bind_mvar xs (lift_tm a)) in
    let sch_m = unbox (bind_mvar xs (lift_tm m)) in
    let ctx = add_const x sch_a ctx in
    let env =
      Env.add_const x
        { scheme = (fun ss -> msubst sch_m (Array.of_list ss))
        ; guarded = guard
        }
        env
    in
    check_dcls ctx env dcls
  | DData (rel, d, sch, dconss) :: dcls ->
    let xs, ptm = unmbind sch in
    let ctx' = add_svar xs ctx in
    let* _ = check_ptm ctx' env ptm in
    let* ptm = unify >> resolve_ptm ptm in
    let sch = unbox (bind_mvar xs (lift_param lift_tm ptm)) in
    let ctx' = add_data d sch CSet.empty ctx' in
    let* dconss = check_dconss ctx' env d dconss in
    let ctx, cs =
      List.fold_right
        (fun (c, sch) (ctx, cs) -> (add_cons c sch ctx, CSet.add c cs))
        dconss (ctx, CSet.empty)
    in
    check_dcls (add_data d sch cs ctx) env dcls

and check_ptm ctx env ptm =
  match ptm with
  | PBase (Type s) -> return s
  | PBind (a, bnd) ->
    let x, ptm = unbind bnd in
    let* _ = infer_sort ctx env a in
    check_ptm (add_var x a ctx) env ptm
  | _ -> failwith "trans1e.check_ptm"

and check_dconss ctx env d dconss =
  match dconss with
  | [] -> return []
  | DCons (c, sch) :: dconss ->
    let xs, ptl = unmbind sch in
    let* _ = check_ptl ctx env d ptl in
    let* dconss = check_dconss ctx env d dconss in
    let* _ = unify >> resolve_ptl ptl in
    let sch = unbox (bind_mvar xs (lift_param lift_tele ptl)) in
    return ((c, sch) :: dconss)

and check_ptl ctx env d ptl =
  match ptl with
  | PBase tl -> check_tl ctx env d tl
  | PBind (a, bnd) ->
    let x, ptl = unbind bnd in
    let* _ = infer_sort ctx env a in
    check_ptl (add_var x a ctx) env d ptl

and check_tl ctx env d0 tl =
  match tl with
  | TBase (Data (d, _, _) as a) when D.equal d d0 -> infer_sort ctx env a
  | TBind (_, a, bnd) ->
    let x, tl = unbind bnd in
    let* _ = infer_sort ctx env a in
    check_tl (add_var x a ctx) env d0 tl
  | _ -> failwith "trans1e.check_tl"

let trans_dcls dcls =
  let ctx =
    { var = VMap.empty
    ; svar = SVSet.empty
    ; const = IMap.empty
    ; data = DMap.empty
    ; cons = CMap.empty
    }
  in
  let _, _, eqns, map0, map1 = run_trans1e (check_dcls ctx Env.empty dcls) in
  let map0, map1 = Unify1.unify (map0, map1) eqns in
  resolve_dcls (map0, map1) dcls
