open Fmt
open Bindlib
open Names
open Syntax1
open Equality1
open Pprint1

type eqn =
  | Eqn0 of sort * sort (* sort equations *)
  | Eqn1 of Env.t * tm * tm (* term equations *)

type eqns = eqn list
type map0 = (sort, sort) mbinder MMap.t
type map1 = (sort, (tm, tm) mbinder) mbinder MMap.t

let pp_eqns fmt (eqns : eqns) =
  let aux fmt (eqns : eqns) =
    List.iter
      (function
        | Eqn0 (s1, s2) -> pf fmt "[%a ?== %a]@;<1 0>" pp_sort s1 pp_sort s2
        | Eqn1 (_, m1, m2) -> pf fmt "[%a ?== %a]@;<1 0>" pp_tm m1 pp_tm m2)
      eqns
  in
  pf fmt "@[<v 0>{@;<1 2>@[<v 0>%a@]@;<1 0>}@]" aux eqns

let pp_map0 fmt (map0 : map0) =
  let aux fmt (map0 : map0) =
    MMap.iter
      (fun x bnd ->
        let xs, s = unmbind bnd in
        pf fmt "%a := @[[%a]@]%a@;<1 0>" M.pp x (array ~sep:comma SV.pp) xs
          pp_sort s)
      map0
  in
  pf fmt "@[<v 0>{@;<1 2>@[<v 0>%a@]@;<1 0>}@]" aux map0

let pp_map1 fmt (map1 : map1) =
  let aux fmt map1 =
    MMap.iter
      (fun x bnd ->
        let _, bnd = unmbind bnd in
        let _, m = unmbind bnd in
        pf fmt "%a := @[%a@] : ??@;<1 0>" M.pp x pp_tm m)
      map1
  in
  pf fmt "@[<v 0>{@;<1 2>@[<v 0>%a@]@;<1 0>}@]" aux map1

let bad_magic env m1 m2 =
  pr "@[bad_magic(@;<1 2>%a@;<1 0>::::::@;<1 2>%a)@]@.@." pp_tm m1 pp_tm m2

(* free sort variables *)
let rec fsv = function
  | SVar x -> SVSet.singleton x
  | SMeta (_, ss) ->
    List.fold_left (fun acc s -> SVSet.union acc (fsv s)) SVSet.empty ss
  | _ -> SVSet.empty

let rec fsvs ss =
  List.fold_left (fun acc s -> SVSet.union acc (fsv s)) SVSet.empty ss

(* free term variables *)
let rec fv ctx = function
  (* inference *)
  | Ann (m, a) ->
    let fsv1, fv1 = fv ctx m in
    let fsv2, fv2 = fv ctx a in
    (SVSet.union fsv1 fsv2, VSet.union fv1 fv2)
  | Meta (_, ss, ms) ->
    let fsv = fsvs ss in
    List.fold_left
      (fun (acc0, acc1) m ->
        let sfv, fv = fv ctx m in
        (SVSet.union acc0 sfv, VSet.union acc1 fv))
      (fsv, VSet.empty) ms
  (* core *)
  | Type s -> (fsv s, VSet.empty)
  | Var x -> (
    match VSet.find_opt x ctx with
    | Some _ -> (SVSet.empty, VSet.empty)
    | None -> (SVSet.empty, VSet.singleton x))
  | Const (_, ss) -> (fsvs ss, VSet.empty)
  | Pi (_, s, a, bnd) ->
    let x, b = unbind bnd in
    let fsv0 = fsv s in
    let fsv1, fv1 = fv ctx a in
    let fsv2, fv2 = fv (VSet.add x ctx) b in
    (SVSet.union (SVSet.union fsv0 fsv1) fsv2, VSet.union fv1 fv2)
  | Lam (_, s, a, bnd) ->
    let x, m = unbind bnd in
    let fsv0 = fsv s in
    let fsv1, fv1 = fv ctx a in
    let fsv2, fv2 = fv (VSet.add x ctx) m in
    (SVSet.union (SVSet.union fsv0 fsv1) fsv2, VSet.union fv1 fv2)
  | App (m, n) ->
    let fsv1, fv1 = fv ctx m in
    let fsv2, fv2 = fv ctx n in
    (SVSet.union fsv1 fsv2, VSet.union fv1 fv2)
  | Let (_, m, bnd) ->
    let x, n = unbind bnd in
    let fsv1, fv1 = fv ctx m in
    let fsv2, fv2 = fv (VSet.add x ctx) n in
    (SVSet.union fsv1 fsv2, VSet.union fv1 fv2)
  (* native *)
  | Unit -> (SVSet.empty, VSet.empty)
  | UIt -> (SVSet.empty, VSet.empty)
  | Bool -> (SVSet.empty, VSet.empty)
  | BTrue -> (SVSet.empty, VSet.empty)
  | BFalse -> (SVSet.empty, VSet.empty)
  | Nat -> (SVSet.empty, VSet.empty)
  | NZero -> (SVSet.empty, VSet.empty)
  | NSucc (i, m) -> fv ctx m
  (* data *)
  | Sigma (_, s, a, bnd) ->
    let x, b = unbind bnd in
    let fsv0 = fsv s in
    let fsv1, fv1 = fv ctx a in
    let fsv2, fv2 = fv (VSet.add x ctx) b in
    (SVSet.union (SVSet.union fsv0 fsv1) fsv2, VSet.union fv1 fv2)
  | Pair (_, s, m, n) ->
    let fsv0 = fsv s in
    let fsv1, fv1 = fv ctx m in
    let fsv2, fv2 = fv ctx m in
    (SVSet.union (SVSet.union fsv0 fsv1) fsv2, VSet.union fv1 fv2)
  | Data (_, ss, ms) ->
    let fsv = fsvs ss in
    List.fold_left
      (fun (acc0, acc1) m ->
        let fsv, fv = fv ctx m in
        (SVSet.union fsv acc0, VSet.union fv acc1))
      (fsv, VSet.empty) ms
  | Cons (_, ss, ms, ns) ->
    let fsv = fsvs ss in
    List.fold_left
      (fun (acc0, acc1) m ->
        let fsv, fv = fv ctx m in
        (SVSet.union fsv acc0, VSet.union fv acc1))
      (fsv, VSet.empty) (ms @ ns)
  | Match (m, bnd, cls) ->
    let x, mot = unbind bnd in
    let fsv1, fv1 = fv ctx m in
    let fsv2, fv2 = fv (VSet.add x ctx) mot in
    let fsv3, fv3 =
      List.fold_left
        (fun (acc0, acc1) -> function
          | PIt rhs ->
            let fsv, fv = fv ctx m in
            (SVSet.union fsv acc0, VSet.union fv acc1)
          | PTrue rhs ->
            let fsv, fv = fv ctx m in
            (SVSet.union fsv acc0, VSet.union fv acc1)
          | PFalse rhs ->
            let fsv, fv = fv ctx m in
            (SVSet.union fsv acc0, VSet.union fv acc1)
          | PZero rhs ->
            let fsv, fv = fv ctx m in
            (SVSet.union fsv acc0, VSet.union fv acc1)
          | PSucc bnd ->
            let x, m = unbind bnd in
            let fsv, fv = fv (VSet.add x ctx) m in
            (SVSet.union fsv acc0, VSet.union fv acc1)
          | PPair (_, s, bnd) ->
            let xs, m = unmbind bnd in
            let fsv1 = fsv s in
            let fsv2, fv = fv (Array.fold_right VSet.add xs ctx) m in
            (SVSet.union (SVSet.union fsv1 fsv2) acc0, VSet.union fv acc1)
          | PCons (_, bnd) ->
            let xs, m = unmbind bnd in
            let fsv, fv = fv (Array.fold_right VSet.add xs ctx) m in
            (SVSet.union fsv acc0, VSet.union fv acc1))
        (SVSet.empty, VSet.empty) cls
    in
    ( SVSet.union (SVSet.union fsv1 fsv2) fsv3
    , VSet.union (VSet.union fv1 fv2) fv3 )
  (* equality *)
  | Eq (a, m, n) ->
    let fsv1, fv1 = fv ctx a in
    let fsv2, fv2 = fv ctx m in
    let fsv3, fv3 = fv ctx n in
    ( SVSet.union (SVSet.union fsv1 fsv2) fsv3
    , VSet.union (VSet.union fv1 fv2) fv3 )
  | Refl m -> fv ctx m
  | Rew (bnd, p, m) ->
    let xs, mot = unmbind bnd in
    let fsv1, fv1 = fv (Array.fold_right VSet.add xs ctx) mot in
    let fsv2, fv2 = fv ctx p in
    let fsv3, fv3 = fv ctx m in
    ( SVSet.union (SVSet.union fsv1 fsv2) fsv3
    , VSet.union (VSet.union fv1 fv2) fv3 )
  (* monadic *)
  | IO a -> fv ctx a
  | Return m -> fv ctx m
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    let fsv1, fv1 = fv ctx m in
    let fsv2, fv2 = fv (VSet.add x ctx) n in
    (SVSet.union fsv1 fsv2, VSet.union fv1 fv2)
  (* session *)
  | Proto -> (SVSet.empty, VSet.empty)
  | End -> (SVSet.empty, VSet.empty)
  | Act (_, _, a, bnd) ->
    let x, b = unbind bnd in
    let fsv1, fv1 = fv ctx a in
    let fsv2, fv2 = fv (VSet.add x ctx) b in
    (SVSet.union fsv1 fsv2, VSet.union fv1 fv2)
  | Ch (_, a) -> fv ctx a
  | Open _ -> (SVSet.empty, VSet.empty)
  | Fork (a, bnd) ->
    let x, m = unbind bnd in
    let fsv1, fv1 = fv ctx a in
    let fsv2, fv2 = fv (VSet.add x ctx) m in
    (SVSet.union fsv1 fsv2, VSet.union fv1 fv2)
  | Recv m -> fv ctx m
  | Send m -> fv ctx m
  | Close m -> fv ctx m
  | Sleep m -> fv ctx m
  | Rand (m, n) ->
    let fsv1, fv1 = fv ctx m in
    let fsv2, fv2 = fv ctx n in
    (SVSet.union fsv1 fsv2, VSet.union fv1 fv2)

(* meta variable occurences *)
let rec occurs_sort x = function
  | SMeta (y, ss) -> M.equal x y || List.exists (occurs_sort x) ss
  | _ -> false

let rec occurs_tm x = function
  (* inference *)
  | Ann (m, a) -> occurs_tm x m || occurs_tm x a
  | Meta (y, _, ms) -> M.equal x y || List.exists (occurs_tm x) ms
  (* core *)
  | Pi (_, _, a, bnd) ->
    let _, b = unbind bnd in
    occurs_tm x a || occurs_tm x b
  | Lam (_, _, a, bnd) ->
    let _, m = unbind bnd in
    occurs_tm x a || occurs_tm x m
  | App (m, n) -> occurs_tm x m || occurs_tm x n
  | Let (_, m, bnd) ->
    let _, n = unbind bnd in
    occurs_tm x m || occurs_tm x n
  (* native *)
  | NSucc (_, m) -> occurs_tm x m
  (* data *)
  | Sigma (_, _, a, bnd) ->
    let _, b = unbind bnd in
    occurs_tm x a || occurs_tm x b
  | Pair (_, _, m, n) -> occurs_tm x m || occurs_tm x n
  | Data (_, _, ms) -> List.exists (occurs_tm x) ms
  | Cons (_, _, ms, ns) -> List.exists (occurs_tm x) (ms @ ns)
  | Match (m, bnd, cls) ->
    let _, a = unbind bnd in
    occurs_tm x m || occurs_tm x a
    || List.exists
         (function
           | PIt rhs -> occurs_tm x rhs
           | PTrue rhs -> occurs_tm x rhs
           | PFalse rhs -> occurs_tm x rhs
           | PZero rhs -> occurs_tm x rhs
           | PSucc bnd ->
             let _, m = unbind bnd in
             occurs_tm x m
           | PPair (_, _, bnd) ->
             let _, m = unmbind bnd in
             occurs_tm x m
           | PCons (_, bnd) ->
             let _, m = unmbind bnd in
             occurs_tm x m)
         cls
  (* equality *)
  | Eq (a, m, n) -> occurs_tm x a || occurs_tm x m || occurs_tm x n
  | Refl m -> occurs_tm x m
  | Rew (bnd, p, m) ->
    let _, mot = unmbind bnd in
    occurs_tm x mot || occurs_tm x p || occurs_tm x m
  (* monadic *)
  | IO a -> occurs_tm x a
  | Return m -> occurs_tm x m
  | MLet (m, bnd) ->
    let _, n = unbind bnd in
    occurs_tm x m || occurs_tm x n
  (* session *)
  | Act (_, _, a, bnd) ->
    let _, b = unbind bnd in
    occurs_tm x a || occurs_tm x b
  | Ch (_, a) -> occurs_tm x a
  | Fork (a, bnd) ->
    let _, m = unbind bnd in
    occurs_tm x a || occurs_tm x m
  | Recv m -> occurs_tm x m
  | Send m -> occurs_tm x m
  | Close m -> occurs_tm x m
  | Sleep m -> occurs_tm x m
  | Rand (m, n) -> occurs_tm x m || occurs_tm x n
  (* other *)
  | _ -> false

(* equation simplification *)
let rec simpl ?(expand_const = false) eqn =
  match eqn with
  | Eqn0 (s1, s2) -> (
    if eq_sort s1 s2 then
      []
    else
      match (s1, s2) with
      | SMeta (x, _), SMeta (y, _) when M.compare x y < 0 -> [ Eqn0 (s2, s1) ]
      | SMeta (x, _), SMeta (y, _) when M.compare x y > 0 -> [ Eqn0 (s1, s2) ]
      | SMeta (x, _), SMeta (y, _) when M.compare x y = 0 -> []
      | SMeta _, _ -> [ Eqn0 (s1, s2) ]
      | _, SMeta _ -> [ Eqn0 (s2, s1) ]
      | _ -> failwith "simpl_Eqn0(%a, %a)" pp_sort s1 pp_sort s2)
  | Eqn1 (env, m1, m2) -> (
    let m1 = whnf ~expand_const env m1 in
    let m2 = whnf ~expand_const env m2 in
    match (m1, m2) with
    (* inference *)
    | Meta (x, _, _), Meta (y, _, _) when M.compare x y < 0 ->
      [ Eqn1 (env, m2, m1) ]
    | Meta (x, _, _), Meta (y, _, _) when M.compare x y > 0 ->
      [ Eqn1 (env, m1, m2) ]
    | Meta (x, _, _), Meta (y, _, _) when M.compare x y = 0 -> []
    | Meta _, _ -> [ Eqn1 (env, m1, m2) ]
    | _, Meta _ -> [ Eqn1 (env, m2, m1) ]
    (* core *)
    | Type s1, Type s2 -> simpl (Eqn0 (s1, s2))
    | Var x1, Var x2 when eq_vars x1 x2 -> []
    | Const (x1, ss1), Const (x2, ss2) when I.equal x1 x2 ->
      List.fold_right2 (fun s1 s2 acc -> simpl (Eqn0 (s1, s2)) @ acc) ss1 ss2 []
    | Const (x, ss), _ -> (
      match Env.find_const x env with
      | Some entry -> simpl (Eqn1 (env, entry.scheme ss, m2))
      | None -> [])
    | _, Const (y, ss) -> (
      match Env.find_const y env with
      | Some entry -> simpl (Eqn1 (env, m1, entry.scheme ss))
      | None -> [])
    | Pi (rel1, s1, a1, bnd1), Pi (rel2, s2, a2, bnd2) when rel1 = rel2 ->
      let _, b1, b2 = unbind2 bnd1 bnd2 in
      let eqns0 = simpl (Eqn0 (s1, s2)) in
      let eqns1 = simpl (Eqn1 (env, a1, a2)) in
      let eqns2 = simpl (Eqn1 (env, b1, b2)) in
      eqns0 @ eqns1 @ eqns2
    | Lam (rel1, s1, a1, bnd1), Lam (rel2, s2, a2, bnd2) when rel1 = rel2 ->
      let _, m1, m2 = unbind2 bnd1 bnd2 in
      let eqns0 = simpl (Eqn0 (s1, s2)) in
      let eqns1 = simpl (Eqn1 (env, a1, a2)) in
      let eqns2 = simpl (Eqn1 (env, m1, m2)) in
      eqns0 @ eqns1 @ eqns2
    | _, App _
    | App _, _ -> (
      try
        let hd1, sp1 = unApps m1 in
        let hd2, sp2 = unApps m2 in
        let eqns1 = simpl (Eqn1 (env, hd1, hd2)) in
        let eqns2 =
          List.fold_right2
            (fun m n acc -> simpl (Eqn1 (env, m, n)) @ acc)
            sp1 sp2 []
        in
        eqns1 @ eqns2
      with
      | _ ->
        if expand_const then
          failwith "simpl_App(%a, %a)@." pp_tm m1 pp_tm m2
        else
          simpl ~expand_const:true (Eqn1 (env, m1, m2)))
    | Let (rel1, m1, bnd1), Let (rel2, m2, bnd2) when rel1 = rel2 ->
      let _, n1, n2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl (Eqn1 (env, m1, m2)) in
      let eqns2 = simpl (Eqn1 (env, n1, n2)) in
      eqns1 @ eqns2
    (* native *)
    | Unit, Unit -> []
    | UIt, UIt -> []
    | Bool, Bool -> []
    | BTrue, BTrue -> []
    | BFalse, BFalse -> []
    | Nat, Nat -> []
    | NZero, NZero -> []
    | NSucc (i1, m1), NSucc (i2, m2) when i1 = i2 -> simpl (Eqn1 (env, m1, m2))
    (* data *)
    | Sigma (rel1, s1, a1, bnd1), Sigma (rel2, s2, a2, bnd2) when rel1 = rel2 ->
      let _, b1, b2 = unbind2 bnd1 bnd2 in
      let eqns0 = simpl (Eqn0 (s1, s2)) in
      let eqns1 = simpl (Eqn1 (env, a1, a2)) in
      let eqns2 = simpl (Eqn1 (env, b1, b2)) in
      eqns0 @ eqns1 @ eqns2
    | Pair (rel1, s1, m1, n1), Pair (rel2, s2, m2, n2) when rel1 = rel2 ->
      let eqns0 = simpl (Eqn0 (s1, s2)) in
      let eqns1 = simpl (Eqn1 (env, m1, m2)) in
      let eqns2 = simpl (Eqn1 (env, n1, n2)) in
      eqns0 @ eqns1 @ eqns2
    | Data (d1, ss1, ms1), Data (d2, ss2, ms2) when D.equal d1 d2 ->
      let eqns1 =
        List.fold_right2
          (fun s1 s2 acc -> simpl (Eqn0 (s1, s2)) @ acc)
          ss1 ss2 []
      in
      let eqns2 =
        List.fold_right2
          (fun m1 m2 acc -> simpl (Eqn1 (env, m1, m2)) @ acc)
          ms1 ms2 []
      in
      eqns1 @ eqns2
    | Cons (c1, ss1, ms1, ns1), Cons (c2, ss2, ms2, ns2) when C.equal c1 c2 ->
      let eqns1 =
        List.fold_right2
          (fun s1 s2 acc -> simpl (Eqn0 (s1, s2)) @ acc)
          ss1 ss2 []
      in
      let eqns2 =
        List.fold_right2
          (fun m1 m2 acc -> simpl (Eqn1 (env, m1, m2)) @ acc)
          (ms1 @ ns1) (ms2 @ ns2) []
      in
      eqns1 @ eqns2
    | Match (m1, bnd1, cls1), Match (m2, bnd2, cls2) ->
      let _, mot1, mot2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl (Eqn1 (env, m1, m2)) in
      let eqns2 = simpl (Eqn1 (env, mot1, mot2)) in
      let eqns3 =
        List.fold_right2
          (fun cl1 cl2 acc ->
            match (cl1, cl2) with
            | PIt rhs1, PIt rhs2 -> simpl (Eqn1 (env, rhs1, rhs2))
            | PTrue rhs1, PTrue rhs2 -> simpl (Eqn1 (env, rhs1, rhs2))
            | PFalse rhs1, PFalse rhs2 -> simpl (Eqn1 (env, rhs1, rhs2))
            | PZero rhs1, PZero rhs2 -> simpl (Eqn1 (env, rhs1, rhs2))
            | PSucc bnd1, PSucc bnd2 ->
              let _, m1, m2 = unbind2 bnd1 bnd2 in
              simpl (Eqn1 (env, m1, m2))
            | PPair (rel1, s1, bnd1), PPair (rel2, s2, bnd2) when rel1 = rel2 ->
              let _, m1, m2 = unmbind2 bnd1 bnd2 in
              simpl (Eqn0 (s1, s2)) @ simpl (Eqn1 (env, m1, m2)) @ acc
            | PCons (c1, bnd1), PCons (c2, bnd2) when C.equal c1 c2 ->
              let _, m1, m2 = unmbind2 bnd1 bnd2 in
              simpl (Eqn1 (env, m1, m2)) @ acc
            | _ -> failwith "simpl_Match")
          cls1 cls2 []
      in
      eqns1 @ eqns2 @ eqns3
    (* equality *)
    | Eq (a1, m1, n1), Eq (a2, m2, n2) ->
      let eqns1 = simpl (Eqn1 (env, a1, a2)) in
      let eqns2 = simpl (Eqn1 (env, m1, m2)) in
      let eqns3 = simpl (Eqn1 (env, n1, n2)) in
      eqns1 @ eqns2 @ eqns3
    | Refl m1, Refl m2 -> simpl (Eqn1 (env, m1, m2))
    | Rew (bnd1, p1, m1), Rew (bnd2, p2, m2) ->
      let _, mot1, mot2 = unmbind2 bnd1 bnd2 in
      let eqns1 = simpl (Eqn1 (env, mot1, mot2)) in
      let eqns2 = simpl (Eqn1 (env, p1, p2)) in
      let eqns3 = simpl (Eqn1 (env, m1, m2)) in
      eqns1 @ eqns2 @ eqns3
    (* monadic *)
    | IO a1, IO a2 -> simpl (Eqn1 (env, a1, a2))
    | Return m1, Return m2 -> simpl (Eqn1 (env, m1, m2))
    | MLet (m1, bnd1), MLet (m2, bnd2) ->
      let _, n1, n2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl (Eqn1 (env, m1, m2)) in
      let eqns2 = simpl (Eqn1 (env, n1, n2)) in
      eqns1 @ eqns2
    (* session *)
    | Proto, Proto -> []
    | End, End -> []
    | Act (rel1, rol1, a1, bnd1), Act (rel2, rol2, a2, bnd2)
      when rel1 = rel2 && rol1 = rol2 ->
      let _, b1, b2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl (Eqn1 (env, a1, a2)) in
      let eqns2 = simpl (Eqn1 (env, b1, b2)) in
      eqns1 @ eqns2
    | Ch (rol1, a1), Ch (rol2, a2) when rol1 = rol2 ->
      simpl (Eqn1 (env, a1, a2))
    | Open prim1, Open prim2 when prim1 = prim2 -> []
    | Fork (a1, bnd1), Fork (a2, bnd2) ->
      let _, m1, m2 = unbind2 bnd1 bnd2 in
      let eqns1 = simpl (Eqn1 (env, a1, a2)) in
      let eqns2 = simpl (Eqn1 (env, m1, m2)) in
      eqns1 @ eqns2
    | Recv m1, Recv m2 -> simpl (Eqn1 (env, m1, m2))
    | Send m1, Send m2 -> simpl (Eqn1 (env, m1, m2))
    | Close m1, Close m2 -> simpl (Eqn1 (env, m1, m2))
    | Sleep m1, Sleep m2 -> simpl (Eqn1 (env, m1, m2))
    | Rand (m1, n1), Rand (m2, n2) ->
      let eqns1 = simpl (Eqn1 (env, m1, m2)) in
      let eqns2 = simpl (Eqn1 (env, n1, n2)) in
      eqns1 @ eqns2
    (* other *)
    | _ -> failwith "simpl(%a, %a)" pp_tm m1 pp_tm m2)

let solve ((map0, map1) : map0 * map1) eqn =
  let meta_sspine sp =
    List.map
      (function
        | SVar x -> x
        | _ -> SV.mk "_")
      sp
  in
  let meta_vspine sp =
    List.map
      (function
        | Var x -> x
        | _ -> V.mk "_")
      sp
  in
  match eqn with
  | Eqn0 (s1, s2) -> (
    match (s1, s2) with
    | SMeta (x, xs), _ ->
      if occurs_sort x s2 then
        (map0, map1)
      else
        let xs = meta_sspine xs in
        if SVSet.subset (fsv s2) (SVSet.of_list xs) then
          let bnd = bind_mvar (Array.of_list xs) (lift_sort s2) in
          (MMap.add x (unbox bnd) map0, map1)
        else
          (map0, map1)
    | _ -> (map0, map1))
  | Eqn1 (env, m1, m2) -> (
    match (m1, m2) with
    | Meta (x, ss, xs), _ ->
      if occurs_tm x m2 then
        (map0, map1)
      else
        let ss = meta_sspine ss in
        let xs = meta_vspine xs in
        let fsv, fv = fv VSet.empty m2 in
        if
          SVSet.subset fsv (SVSet.of_list ss)
          && VSet.subset fv (VSet.of_list xs)
        then
          let bnd = bind_mvar (Array.of_list xs) (lift_tm m2) in
          let bnd = bind_mvar (Array.of_list ss) bnd in
          (map0, MMap.add x (unbox bnd) map1)
        else
          (map0, map1)
    | _ -> (map0, map1))

let rec resolve_sort (map0 : map0) = function
  | SMeta (x, ss) as s -> (
    match MMap.find_opt x map0 with
    | Some bnd ->
      let s = msubst bnd (Array.of_list ss) in
      resolve_sort map0 s
    | None -> s)
  | s -> s

let resolve_tm ((map0, map1) : map0 * map1) m =
  let rec resolve = function
    (* inference *)
    | Ann (m, a) -> Ann (resolve m, resolve a)
    | Meta (x, ss, xs) as m -> (
      match MMap.find_opt x map1 with
      | Some bnd ->
        let bnd = msubst bnd (Array.of_list ss) in
        let m = msubst bnd (Array.of_list xs) in
        resolve m
      | _ -> m)
    (* core *)
    | Type s -> Type (resolve_sort map0 s)
    | Const (x, ss) ->
      let ss = List.map (resolve_sort map0) ss in
      Const (x, ss)
    | Pi (rel, s, a, bnd) ->
      let x, b = unbind bnd in
      let s = resolve_sort map0 s in
      let a = resolve a in
      let b = lift_tm (resolve b) in
      Pi (rel, s, a, unbox (bind_var x b))
    | Lam (rel, s, a, bnd) ->
      let x, m = unbind bnd in
      let s = resolve_sort map0 s in
      let a = resolve a in
      let m = lift_tm (resolve m) in
      Lam (rel, s, a, unbox (bind_var x m))
    | App (m, n) -> App (resolve m, resolve n)
    | Let (rel, m, bnd) ->
      let x, n = unbind bnd in
      let m = resolve m in
      let n = lift_tm (resolve n) in
      Let (rel, m, unbox (bind_var x n))
    (* native *)
    | NSucc (i, m) -> NSucc (i, resolve m)
    (* data *)
    | Sigma (rel, s, a, bnd) ->
      let x, b = unbind bnd in
      let s = resolve_sort map0 s in
      let a = resolve a in
      let b = lift_tm (resolve b) in
      Sigma (rel, s, a, unbox (bind_var x b))
    | Pair (rel, s, m, n) ->
      let s = resolve_sort map0 s in
      let m = resolve m in
      let n = resolve n in
      Pair (rel, s, m, n)
    | Data (d, ss, ms) ->
      let ss = List.map (resolve_sort map0) ss in
      let ms = List.map resolve ms in
      Data (d, ss, ms)
    | Cons (c, ss, ms, ns) ->
      let ss = List.map (resolve_sort map0) ss in
      let ms = List.map resolve ms in
      let ns = List.map resolve ns in
      Cons (c, ss, ms, ns)
    | Match (m, bnd, cls) ->
      let x, mot = unbind bnd in
      let m = resolve m in
      let mot = lift_tm (resolve mot) in
      let cls =
        List.map
          (function
            | PIt rhs -> PIt (resolve rhs)
            | PTrue rhs -> PTrue (resolve rhs)
            | PFalse rhs -> PFalse (resolve rhs)
            | PZero rhs -> PZero (resolve rhs)
            | PSucc bnd ->
              let x, rhs = unbind bnd in
              let rhs = lift_tm (resolve rhs) in
              PSucc (unbox (bind_var x rhs))
            | PPair (rel, s, bnd) ->
              let xs, n = unmbind bnd in
              let s = resolve_sort map0 s in
              let n = lift_tm (resolve n) in
              PPair (rel, s, unbox (bind_mvar xs n))
            | PCons (c, bnd) ->
              let xs, n = unmbind bnd in
              let n = lift_tm (resolve n) in
              PCons (c, unbox (bind_mvar xs n)))
          cls
      in
      Match (m, unbox (bind_var x mot), cls)
    (* equality *)
    | Eq (a, m, n) -> Eq (resolve a, resolve m, resolve n)
    | Refl m -> Refl (resolve m)
    | Rew (bnd, p, m) ->
      let xs, mot = unmbind bnd in
      let mot = lift_tm (resolve mot) in
      let p = resolve p in
      let m = resolve m in
      Rew (unbox (bind_mvar xs mot), p, m)
    (* monadic *)
    | IO a -> IO (resolve a)
    | Return m -> Return (resolve m)
    | MLet (m, bnd) ->
      let x, n = unbind bnd in
      let m = resolve m in
      let n = lift_tm (resolve n) in
      MLet (m, unbox (bind_var x n))
    (* session *)
    | Act (rel, rol, a, bnd) ->
      let x, b = unbind bnd in
      let a = resolve a in
      let b = lift_tm (resolve b) in
      Act (rel, rol, a, unbox (bind_var x b))
    | Ch (rol, a) -> Ch (rol, resolve a)
    | Fork (a, bnd) ->
      let x, m = unbind bnd in
      let a = resolve a in
      let m = lift_tm (resolve m) in
      Fork (a, unbox (bind_var x m))
    | Recv m -> Recv (resolve m)
    | Send m -> Send (resolve m)
    | Close m -> Close (resolve m)
    | Sleep m -> Sleep (resolve m)
    | Rand (m, n) -> Rand (resolve m, resolve n)
    (* other *)
    | m -> m
  in
  resolve m

let rec resolve_param lift resolve map = function
  | PBase a -> PBase (resolve map a)
  | PBind (a, bnd) ->
    let x, b = unbind bnd in
    let a = resolve_tm map a in
    let b = lift_param lift (resolve_param lift resolve map b) in
    PBind (a, unbox (bind_var x b))

let rec resolve_tele map = function
  | TBase a -> TBase (resolve_tm map a)
  | TBind (rel, a, bnd) ->
    let x, b = unbind bnd in
    let a = resolve_tm map a in
    let b = lift_tele (resolve_tele map b) in
    TBind (rel, a, unbox (bind_var x b))

let resolve_dcons map (DCons (c, sch)) =
  let xs, ptl = unmbind sch in
  let ptl = resolve_param lift_tele resolve_tele map ptl in
  DCons (c, unbox (bind_mvar xs (lift_param lift_tele ptl)))

let resolve_dcl map = function
  | DTm (rel, x, guard, sch) ->
    let xs, (a, m) = unmbind sch in
    let a = lift_tm (resolve_tm map a) in
    let m = lift_tm (resolve_tm map m) in
    DTm (rel, x, guard, unbox (bind_mvar xs (box_pair a m)))
  | DData (d, sch, dconss) ->
    let xs, ptm = unmbind sch in
    let ptm = resolve_param lift_tm resolve_tm map ptm in
    let sch = bind_mvar xs (lift_param lift_tm ptm) in
    let dconss = List.map (resolve_dcons map) dconss in
    DData (d, unbox sch, dconss)

let resolve_dcls map dcls = List.map (resolve_dcl map) dcls

let rec unify ((map0, map1) as map : map0 * map1) eqns =
  let eqns =
    List.map
      (function
        | Eqn0 (s1, s2) -> Eqn0 (resolve_sort map0 s1, resolve_sort map0 s2)
        | Eqn1 (env, m1, m2) -> Eqn1 (env, resolve_tm map m1, resolve_tm map m2))
      eqns
  in
  match List.concat_map simpl eqns with
  | [] -> map
  | eqn :: eqns ->
    let map = solve map eqn in
    unify map eqns
