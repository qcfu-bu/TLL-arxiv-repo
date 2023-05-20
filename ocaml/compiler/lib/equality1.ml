open Bindlib
open Names
open Syntax1

module Env = struct
  type const_entry =
    { scheme : sorts -> tm
    ; guarded : bool
    }

  type t =
    { var : tm VMap.t
    ; const : const_entry IMap.t
    }

  let empty = { var = VMap.empty; const = IMap.empty }
  let find_var x env = VMap.find_opt x env.var
  let find_const x env = IMap.find_opt x env.const
  let add_var x m env = { env with var = VMap.add x m env.var }
  let add_const x entry env = { env with const = IMap.add x entry env.const }
end

let rec is_nat = function
  | NZero -> true
  | NSucc (_, m) -> is_nat m
  | _ -> false

let rec get_nat = function
  | NZero -> 0
  | NSucc (i, m) -> i + get_nat m
  | _ -> failwith "get_nat"

let tm_of_bool = function
  | true -> BTrue
  | false -> BFalse

let tm_of_int i =
  if i <= 0 then
    NZero
  else
    NSucc (i, NZero)

let rec whnf ?(expand_const = true) (env : Env.t) = function
  (* inference *)
  | Ann (m, a) -> whnf ~expand_const env m
  (* core *)
  | Var x -> (
    match Env.find_var x env with
    | Some m -> whnf ~expand_const env m
    | _ -> Var x)
  | Const (x, ss) -> (
    match Env.find_const x env with
    | Some entry when expand_const && not entry.guarded ->
      whnf ~expand_const env (entry.scheme ss)
    | _ -> Const (x, ss))
  | App _ as m -> (
    let hd, sp = unApps m in
    let hd = whnf ~expand_const env hd in
    let sp = List.map (whnf ~expand_const env) sp in
    match (hd, sp) with
    | Lam (_, _, _, bnd), n :: sp ->
      whnf ~expand_const env (mkApps (subst bnd n) sp)
    | Const (x, []), [ m; n ]
      when I.equal x Prelude1.lten_i && is_nat m && is_nat n ->
      let m = get_nat m in
      let n = get_nat n in
      tm_of_bool (m <= n)
    | Const (x, []), [ m; n ]
      when I.equal x Prelude1.gten_i && is_nat m && is_nat n ->
      let m = get_nat m in
      let n = get_nat n in
      tm_of_bool (m >= n)
    | Const (x, []), [ m; n ]
      when I.equal x Prelude1.ltn_i && is_nat m && is_nat n ->
      let m = get_nat m in
      let n = get_nat n in
      tm_of_bool (m < n)
    | Const (x, []), [ m; n ]
      when I.equal x Prelude1.gtn_i && is_nat m && is_nat n ->
      let m = get_nat m in
      let n = get_nat n in
      tm_of_bool (m > n)
    | Const (x, []), [ m; n ]
      when I.equal x Prelude1.eqn_i && is_nat m && is_nat n ->
      let m = get_nat m in
      let n = get_nat n in
      tm_of_bool (m = n)
    | Const (x, []), [ m; n ]
      when I.equal x Prelude1.addn_i && is_nat m && is_nat n ->
      let m = get_nat m in
      let n = get_nat n in
      tm_of_int (m + n)
    | Const (x, []), [ m; n ]
      when I.equal x Prelude1.subn_i && is_nat m && is_nat n ->
      let m = get_nat m in
      let n = get_nat n in
      tm_of_int (m - n)
    | Const (x, []), [ m; n ]
      when I.equal x Prelude1.muln_i && is_nat m && is_nat n ->
      let m = get_nat m in
      let n = get_nat n in
      tm_of_int (m * n)
    | Const (x, []), [ m; n ]
      when I.equal x Prelude1.divn_i && is_nat m && is_nat n ->
      let m = get_nat m in
      let n = get_nat n in
      tm_of_int (m / n)
    | Const (x, []), [ m; n ]
      when I.equal x Prelude1.modn_i && is_nat m && is_nat n ->
      let m = get_nat m in
      let n = get_nat n in
      tm_of_int (m mod n)
    | Const (x, ss), _ when expand_const -> (
      match Env.find_const x env with
      | Some entry -> whnf ~expand_const env (mkApps (entry.scheme ss) sp)
      | None -> mkApps hd sp)
    | _ -> mkApps hd sp)
  | Let (r, m, bnd) ->
    let m = whnf ~expand_const env m in
    whnf ~expand_const env (subst bnd m)
  (* native *)
  | NSucc (0, m) -> whnf ~expand_const env m
  | NSucc (i, m) -> (
    let m = whnf ~expand_const env m in
    match m with
    | NSucc (j, m) -> NSucc (i + j, m)
    | _ -> NSucc (i, m))
  (* data *)
  | Match (rel, m, mot, cls) -> (
    let m = whnf ~expand_const env m in
    match match_cls cls m with
    | Some m -> whnf ~expand_const env m
    | _ -> Match (rel, m, mot, cls))
  (* equality *)
  | Rew (bnd, pf, m) -> (
    let pf = whnf ~expand_const env pf in
    match pf with
    | Refl _ -> whnf ~expand_const env m
    | _ -> Rew (bnd, pf, m))
  (* monadic *)
  | MLet (m, bnd) -> (
    let m = whnf ~expand_const env m in
    match m with
    | Return m -> whnf ~expand_const env (subst bnd m)
    | _ -> MLet (m, bnd))
  (* session *)
  | Ch (rol, a) -> Ch (rol, whnf ~expand_const env a)
  (* other *)
  | m -> m

and match_cls cls m =
  List.fold_left
    (fun acc cl ->
      Option.fold
        ~some:(fun _ -> acc)
        ~none:
          (match (cl, m) with
          | PIt (s1, rhs), UIt s2 when eq_sort s1 s2 -> Some rhs
          | PTrue rhs, BTrue -> Some rhs
          | PFalse rhs, BFalse -> Some rhs
          | PZero rhs, NZero -> Some rhs
          | PSucc bnd, NSucc (1, m) -> Some (subst bnd m)
          | PSucc bnd, NSucc (i, m) -> Some (subst bnd (NSucc (i - 1, m)))
          | PPair (rel11, rel12, s1, bnd), Pair (rel21, rel22, s2, m1, m2)
            when rel11 = rel21 && rel12 = rel22 && eq_sort s1 s2 ->
            Some (msubst bnd [| m1; m2 |])
          | PCons (c1, bnd), Cons (c2, _, _, ms) when C.equal c1 c2 ->
            Some (msubst bnd (Array.of_list ms))
          | _ -> acc)
        acc)
    None cls

(* alpha equivalence *)
let rec aeq tm1 tm2 =
  if tm1 == tm2 then
    true
  else
    match (tm1, tm2) with
    (* inference *)
    | Ann (m1, a1), Ann (m2, a2) -> aeq m1 m2 && aeq a1 a2
    | Meta (x1, _, _), Meta (x2, _, _) -> M.equal x1 x2
    (* core *)
    | Type s1, Type s2 -> eq_sort s1 s2
    | Var x1, Var x2 -> eq_vars x1 x2
    | Const (x1, ss1), Const (x2, ss2) ->
      I.equal x1 x2 && List.equal eq_sort ss1 ss2
    | Pi (rel1, s1, a1, bnd1), Pi (rel2, s2, a2, bnd2) ->
      rel1 = rel2 && eq_sort s1 s2 && aeq a1 a2 && eq_binder aeq bnd1 bnd2
    | Lam (rel1, s1, a1, bnd1), Lam (rel2, s2, a2, bnd2) ->
      rel1 = rel2 && eq_sort s1 s2 && aeq a1 a2 && eq_binder aeq bnd1 bnd2
    | App (m1, n1), App (m2, n2) -> aeq m1 m2 && aeq n1 n2
    | Let (rel1, m1, bnd1), Let (rel2, m2, bnd2) ->
      rel1 = rel2 && aeq m1 m2 && eq_binder aeq bnd1 bnd2
    (* native *)
    | Unit s1, Unit s2 -> eq_sort s1 s2
    | UIt s1, UIt s2 -> eq_sort s1 s2
    | Bool, Bool -> true
    | BTrue, BTrue -> true
    | BFalse, BFalse -> true
    | Nat, Nat -> true
    | NZero, NZero -> true
    | NSucc (i1, m1), NSucc (i2, m2) -> i1 = i2 && aeq m1 m2
    (* data *)
    | Sigma (rel11, rel12, s1, a1, bnd1), Sigma (rel21, rel22, s2, a2, bnd2) ->
      rel11 = rel21 && rel12 = rel22 && eq_sort s1 s2 && aeq a1 a2
      && eq_binder aeq bnd1 bnd2
    | Pair (rel11, rel12, s1, m1, n1), Pair (rel21, rel22, s2, m2, n2) ->
      rel11 = rel21 && rel12 = rel22 && s1 = s2 && aeq m1 m2 && aeq n1 n2
    | Data (d1, ss1, ms1), Data (d2, ss2, ms2) ->
      D.equal d1 d2 && List.equal eq_sort ss1 ss2 && List.equal aeq ms1 ms2
    | Cons (c1, ss1, ms1, ns1), Cons (c2, ss2, ms2, ns2) ->
      C.equal c1 c2 && List.equal eq_sort ss1 ss2 && List.equal aeq ms1 ms2
      && List.equal aeq ns1 ns2
    | Match (rel1, m1, bnd1, cls1), Match (rel2, m2, bnd2, cls2) ->
      rel1 = rel2 && aeq m1 m2 && eq_binder aeq bnd1 bnd2
      && List.equal
           (fun cl1 cl2 ->
             match (cl1, cl2) with
             | PIt (s1, rhs1), PIt (s2, rhs2) -> eq_sort s1 s2 && aeq rhs1 rhs2
             | PTrue rhs1, PTrue rhs2 -> aeq rhs1 rhs2
             | PFalse rhs1, PFalse rhs2 -> aeq rhs1 rhs2
             | PZero rhs1, PZero rhs2 -> aeq rhs1 rhs2
             | PSucc bnd1, PSucc bnd2 -> eq_binder aeq bnd1 bnd2
             | PPair (rel11, rel12, s1, bnd1), PPair (rel21, rel22, s2, bnd2) ->
               rel11 = rel21 && rel12 = rel22 && eq_sort s1 s2
               && eq_mbinder aeq bnd1 bnd2
             | PCons (c1, bnd1), PCons (c2, bnd2) ->
               C.equal c1 c2 && eq_mbinder aeq bnd1 bnd2
             | _ -> false)
           cls1 cls2
    (* absurd *)
    | Bot, Bot -> true
    | Absurd (a1, m1), Absurd (a2, m2) -> aeq a1 a2 && aeq m1 m2
    (* equality *)
    | Eq (a1, m1, n1), Eq (a2, m2, n2) -> aeq a1 a2 && aeq m1 m2 && aeq n1 n2
    | Refl m1, Refl m2 -> aeq m1 m2
    | Rew (bnd1, p1, m1), Rew (bnd2, p2, m2) ->
      eq_mbinder aeq bnd1 bnd2 && aeq p1 p2 && aeq m1 m2
    (* monadic *)
    | IO a1, IO a2 -> aeq a1 a2
    | Return m1, Return m2 -> aeq m1 m2
    | MLet (m1, bnd1), MLet (m2, bnd2) -> aeq m1 m2 && eq_binder aeq bnd1 bnd2
    (* session *)
    | Proto, Proto -> true
    | End, End -> true
    | Act (rel1, rol1, a1, bnd1), Act (rel2, rol2, a2, bnd2) ->
      rel1 = rel2 && rol1 = rol2 && aeq a1 a2 && eq_binder aeq bnd1 bnd2
    | Ch (rol1, a1), Ch (rol2, a2) -> rol1 = rol2 && aeq a1 a2
    | Open prim1, Open prim2 -> prim1 = prim2
    | Fork (a1, bnd1), Fork (a2, bnd2) -> aeq a1 a2 && eq_binder aeq bnd1 bnd2
    | Recv m1, Recv m2 -> aeq m1 m2
    | Send m1, Send m2 -> aeq m1 m2
    | Close m1, Close m2 -> aeq m1 m2
    | Sleep m1, Sleep m2 -> aeq m1 m2
    | Rand (m1, n1), Rand (m2, n2) -> aeq m1 m2 && aeq n1 n2
    (* other *)
    | _ -> false

(* Beta/Delta/Iota equaltiy *)
let rec eq_tm ?(expand_const = false) env m1 m2 =
  let rec equal m1 m2 =
    if aeq m1 m2 then
      true
    else
      let m1 = whnf ~expand_const env m1 in
      let m2 = whnf ~expand_const env m2 in
      match (m1, m2) with
      (* inference *)
      | Ann (m1, a1), Ann (m2, a2) -> equal m1 m2 && equal a1 a2
      | Meta (x1, _, _), Meta (x2, _, _) -> M.equal x1 x2
      (* core *)
      | Type s1, Type s2 -> eq_sort s1 s2
      | Var x1, Var x2 -> eq_vars x1 x2
      | Const (x1, ss1), Const (x2, ss2) ->
        I.equal x1 x2 && List.equal eq_sort ss1 ss2
      | Pi (rel1, s1, a1, bnd1), Pi (rel2, s2, a2, bnd2) ->
        rel1 = rel2 && eq_sort s1 s2 && equal a1 a2 && eq_binder equal bnd1 bnd2
      | Lam (rel1, s1, a1, bnd1), Lam (rel2, s2, a2, bnd2) ->
        rel1 = rel2 && eq_sort s1 s2 && equal a1 a2 && eq_binder equal bnd1 bnd2
      | App (m1, n1), App (m2, n2) -> equal m1 m2 && equal n1 n2
      | Let (rel1, m1, bnd1), Let (rel2, m2, bnd2) ->
        rel1 = rel2 && equal m1 m2 && eq_binder equal bnd1 bnd2
      (* native *)
      | Unit s1, Unit s2 -> eq_sort s1 s2
      | UIt s1, UIt s2 -> eq_sort s1 s2
      | Bool, Bool -> true
      | BTrue, BTrue -> true
      | BFalse, BFalse -> true
      | Nat, Nat -> true
      | NZero, NZero -> true
      | NSucc (i1, m1), NSucc (i2, m2) -> i1 = i2 && equal m1 m2
      (* data *)
      | Sigma (rel11, rel12, s1, a1, bnd1), Sigma (rel21, rel22, s2, a2, bnd2)
        ->
        rel11 = rel21 && rel12 = rel22 && eq_sort s1 s2 && equal a1 a2
        && eq_binder equal bnd1 bnd2
      | Pair (rel11, rel12, s1, m1, n1), Pair (rel21, rel22, s2, m2, n2) ->
        rel11 = rel21 && rel12 = rel22 && eq_sort s1 s2 && equal m1 m2
        && equal n1 n2
      | Data (d1, ss1, ms1), Data (d2, ss2, ms2) ->
        D.equal d1 d2 && List.equal eq_sort ss1 ss2 && List.equal equal ms1 ms2
      | Cons (c1, ss1, ms1, ns1), Cons (c2, ss2, ms2, ns2) ->
        C.equal c1 c2 && List.equal eq_sort ss1 ss2 && List.equal equal ms1 ms2
        && List.equal equal ns1 ns2
      | Match (rel1, m1, bnd1, cls1), Match (rel2, m2, bnd2, cls2) ->
        rel1 = rel2 && equal m1 m2 && eq_binder equal bnd1 bnd2
        && List.equal
             (fun cl1 cl2 ->
               match (cl1, cl2) with
               | PIt (s1, rhs1), PIt (s2, rhs2) ->
                 eq_sort s1 s2 && equal rhs1 rhs2
               | PTrue rhs1, PTrue rhs2 -> equal rhs1 rhs2
               | PFalse rhs1, PFalse rhs2 -> equal rhs1 rhs2
               | PZero rhs1, PZero rhs2 -> equal rhs1 rhs2
               | PSucc bnd1, PSucc bnd2 -> eq_binder equal bnd1 bnd2
               | PPair (rel11, rel12, s1, bnd1), PPair (rel21, rel22, s2, bnd2)
                 ->
                 rel11 = rel21 && rel12 = rel22 && eq_sort s1 s2
                 && eq_mbinder equal bnd1 bnd2
               | PCons (c1, bnd1), PCons (c2, bnd2) ->
                 C.equal c1 c2 && eq_mbinder equal bnd1 bnd2
               | _ -> false)
             cls1 cls2
      (* absurd *)
      | Bot, Bot -> true
      | Absurd (a1, m1), Absurd (a2, m2) -> equal a1 a2 && equal m1 m2
      (* equality *)
      | Eq (a1, m1, n1), Eq (a2, m2, n2) ->
        equal a1 a2 && equal m1 m2 && equal n1 n2
      | Refl m1, Refl m2 -> equal m1 m2
      | Rew (bnd1, p1, m1), Rew (bnd2, p2, m2) ->
        eq_mbinder equal bnd1 bnd2 && equal p1 p2 && equal m1 m2
      (* monadic *)
      | IO a1, IO a2 -> equal a1 a2
      | Return m1, Return m2 -> equal m1 m2
      | MLet (m1, bnd1), MLet (m2, bnd2) ->
        equal m1 m2 && eq_binder equal bnd1 bnd2
      (* session *)
      | Proto, Proto -> true
      | End, End -> true
      | Act (rel1, rol1, a1, bnd1), Act (rel2, rol2, a2, bnd2) ->
        rel1 = rel2 && rol1 = rol2 && equal a1 a2 && eq_binder equal bnd1 bnd2
      | Ch (rol1, a1), Ch (rol2, a2) -> rol1 = rol2 && equal a1 a2
      | Open prim1, Open prim2 -> prim1 = prim2
      | Fork (a1, bnd1), Fork (a2, bnd2) ->
        equal a1 a2 && eq_binder equal bnd1 bnd2
      | Recv m1, Recv m2 -> equal m1 m2
      | Send m1, Send m2 -> equal m1 m2
      | Close m1, Close m2 -> equal m1 m2
      | Sleep m1, Sleep m2 -> equal m1 m2
      | Rand (m1, n1), Rand (m2, n2) -> equal m1 m2 && equal n1 n2
      (* other *)
      | _ -> false
  in
  if equal m1 m2 then
    true
  else if expand_const then
    false
  else
    eq_tm ~expand_const:true env m1 m2
