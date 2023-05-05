open Fmt
open Bindlib
open Names
open Trans12
open Syntax2

type 'a trans23 = (int * I.t) IMap.t * Resolver.t -> 'a

let return m : 'a trans23 = fun arity -> m

let ( >>= ) (m : 'a trans23) (f : 'a -> 'b trans23) : 'b trans23 =
 fun arity -> f (m arity) arity

let ( let* ) = ( >>= )

let get_arity x : (int * I.t) option trans23 =
 fun (arity, _) -> IMap.find_opt x arity

let resolve_c c : C.t trans23 = fun (_, res) -> Resolver.find_cons c [] res

let set_arity x i (m : 'a trans23) : 'a trans23 =
 fun (arity, res) -> m (IMap.add x i arity, res)

let rec mapM (f : 'a -> 'b trans23) (xs : 'a list) : 'b list trans23 =
  match xs with
  | [] -> return []
  | x :: xs ->
    let* x = f x in
    let* xs = mapM f xs in
    return (x :: xs)

let rec foldM xs acc f : 'b trans23 =
  match xs with
  | [] -> return acc
  | x :: xs -> foldM xs acc f >>= f x

let trans_sort = function
  | U -> Syntax3.U
  | L -> Syntax3.L

let trans_prim = function
  | Stdin -> Syntax3.Stdin
  | Stdout -> Syntax3.Stdout
  | Stderr -> Syntax3.Stderr

let trans_var x = Syntax3.(copy_var x var (name_of x))
let trans_mvar xs = Array.map trans_var xs

let rec gather_mlet = function
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    let xs, n = gather_mlet n in
    ((x, m) :: xs, n)
  | m -> ([], m)

let rec gather_lam m =
  match m with
  | Lam (s, bnd) ->
    let x, m = unbind bnd in
    let xs, m = gather_lam m in
    ((x, s) :: xs, m)
  | _ -> ([], m)

let rec trans_tm = function
  | Var x -> return Syntax3.(_Var (trans_var x))
  | Const x -> return Syntax3.(_Const x)
  | Lam (s, bnd) ->
    let x, m = unbind bnd in
    let* m = trans_tm m in
    let bnd = bind_var (trans_var x) m in
    return Syntax3.(_Lam (trans_sort s) bnd)
  | App (s, m, n) as tm -> (
    let hd, sp = unApps tm in
    match hd with
    | Const x0 -> (
      let* opt = get_arity x0 in
      match opt with
      | Some (i, x1) ->
        let* sp =
          mapM
            (fun (n, s) ->
              let* n = trans_tm n in
              let s = trans_sort s in
              return (n, s))
            sp
        in
        if i = List.length sp then
          let sp = List.map fst sp in
          return Syntax3.(_Call x0 (box_list sp))
        else
          return Syntax3.(_mkApps (_Const x1) sp)
      | _ ->
        let* m = trans_tm m in
        let* n = trans_tm n in
        return Syntax3.(_App (trans_sort s) m n))
    | _ ->
      let* m = trans_tm m in
      let* n = trans_tm n in
      return Syntax3.(_App (trans_sort s) m n))
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    let* m = trans_tm m in
    let* n = trans_tm n in
    let bnd = bind_var (trans_var x) n in
    return Syntax3.(_Let m bnd)
  (* native *)
  | UIt -> return Syntax3.(_NULL)
  | BTrue -> return Syntax3.(_Int 1)
  | BFalse -> return Syntax3.(_Int 0)
  | NZero -> return Syntax3.(_Int 0)
  | NSucc (i, m) ->
    let* m = trans_tm m in
    return Syntax3.(_Add i m)
  (* data *)
  | Pair (m, n) ->
    let* m = trans_tm m in
    let* n = trans_tm n in
    return Syntax3.(_Pair m n)
  | Cons (c, ms) ->
    let* ms = mapM trans_tm ms in
    return Syntax3.(_Cons c (box_list ms))
  | Match (_, m, [ PIt rhs ]) ->
    let* m = trans_tm m in
    let* rhs = trans_tm rhs in
    let arg = Syntax3.(V.mk "_") in
    let bnd = bind_var arg rhs in
    return Syntax3.(_Let m bnd)
  | Match (_, m, [ PTrue rhs1; PFalse rhs2 ]) ->
    let* m = trans_tm m in
    let* n1 = trans_tm rhs1 in
    let* n2 = trans_tm rhs2 in
    return Syntax3.(_Ifte m n1 n2)
  | Match (_, m, [ PZero rhs1; PSucc bnd ]) ->
    let arg = Syntax3.(V.mk "_") in
    let x, rhs2 = unbind bnd in
    let* m = trans_tm m in
    let* n1 = trans_tm rhs1 in
    let* n2 = trans_tm rhs2 in
    let bnd =
      Syntax3.(
        bind_var arg
          (_Ifte (_Var arg)
             (_Let (_Add (-1) (_Var arg)) (bind_var (trans_var x) n2))
             n1))
    in
    return Syntax3.(_Let m bnd)
  | Match (s, m, cls) ->
    let s = trans_sort s in
    let* m = trans_tm m in
    let* cls =
      mapM
        (function
          | PPair bnd ->
            let xs, rhs = unmbind bnd in
            let* rhs = trans_tm rhs in
            let bnd = bind_mvar (trans_mvar xs) rhs in
            return Syntax3.(_PPair bnd)
          | PCons (c, bnd) ->
            let xs, rhs = unmbind bnd in
            let* rhs = trans_tm rhs in
            let bnd = bind_mvar (trans_mvar xs) rhs in
            return Syntax3.(_PCons c bnd)
          | _ -> failwith "trans23.trans_tm.Match")
        cls
    in
    return Syntax3.(_Match s m (box_list cls))
  (* monadic *)
  | Return m ->
    let arg = Syntax3.(V.mk "_") in
    let* m = trans_tm m in
    let bnd = bind_var arg m in
    return Syntax3.(_Lam L bnd)
  | MLet _ as m ->
    let arg = Syntax3.(V.mk "_") in
    let xs, n = gather_mlet m in
    let* n = trans_tm n in
    let* m =
      foldM xs
        Syntax3.(_App L n _NULL)
        (fun (x, m) acc ->
          let x = trans_var x in
          let* m = trans_tm m in
          let bnd = Syntax3.(bind_var x acc) in
          return Syntax3.(_Let (_App L m _NULL) bnd))
    in
    let bnd = bind_var arg m in
    return Syntax3.(_Lam L bnd)
  (* session *)
  | Open prim ->
    let arg = Syntax3.(V.mk "_") in
    let prim = trans_prim prim in
    let bnd = Syntax3.(bind_var arg (_Open prim)) in
    return Syntax3.(_Lam L bnd)
  | Fork bnd ->
    let arg = Syntax3.(V.mk "_") in
    let x, m = unbind bnd in
    let* m = trans_tm m in
    let bnd = Syntax3.(bind_var (trans_var x) (_App L m _NULL)) in
    let bnd = Syntax3.(bind_var arg (_Fork bnd)) in
    return Syntax3.(_Lam L bnd)
  | Recv (R, m) ->
    let arg = Syntax3.(V.mk "_") in
    let* m = trans_tm m in
    let bnd = Syntax3.(bind_var arg (_Recv m)) in
    return Syntax3.(_Lam L bnd)
  | Recv (N, m) ->
    let arg = Syntax3.(V.mk "_") in
    let* m = trans_tm m in
    let bnd = Syntax3.(bind_var arg (_Pair _NULL m)) in
    return Syntax3.(_Lam L bnd)
  | Send (R, s, m) ->
    let arg = Syntax3.(V.mk "_") in
    let x = Syntax3.(V.mk "x") in
    let* m = trans_tm m in
    let bnd = Syntax3.(bind_var arg (_Send m (_Var x))) in
    let bnd = Syntax3.(bind_var x (_Lam L bnd)) in
    return Syntax3.(_Lam (trans_sort s) bnd)
  | Send (N, s, m) ->
    let arg = Syntax3.(V.mk "_") in
    let x = Syntax3.(V.mk "x") in
    let* m = trans_tm m in
    let bnd = Syntax3.(bind_var arg m) in
    let bnd = Syntax3.(bind_var x (_Lam L bnd)) in
    return Syntax3.(_Lam (trans_sort s) bnd)
  | Close (Pos, m) ->
    let arg = Syntax3.(V.mk "_") in
    let* m = trans_tm m in
    let bnd = Syntax3.(bind_var arg _NULL) in
    let bnd = Syntax3.(bind_var arg (_Let m bnd)) in
    return Syntax3.(_Lam L bnd)
  | Close (Neg, m) ->
    let arg = Syntax3.(V.mk "_") in
    let* m = trans_tm m in
    let bnd = Syntax3.(bind_var arg (_Close m)) in
    return Syntax3.(_Lam L bnd)
  | Sleep m ->
    let arg = Syntax3.(V.mk "_") in
    let* m = trans_tm m in
    let bnd = Syntax3.(bind_var arg (_Sleep m)) in
    return Syntax3.(_Lam L bnd)
  (* erasure *)
  | NULL -> return Syntax3._NULL

let trans_dcls res dcls =
  let rec aux = function
    | DTm (x0, (Lam _ as m)) :: dcls ->
      let xs0, m = gather_lam m in
      let xs1 = List.map (fun (x, s) -> trans_var x) xs0 in
      let x1 = I.extend x0 "clo" in
      let* m = set_arity x0 (List.length xs0, x1) (trans_tm m) in
      let bnd = bind_mvar (Array.of_list xs1) m in
      let clo =
        List.fold_right
          (fun (x, s) acc ->
            Syntax3.(_Lam (trans_sort s) (bind_var (trans_var x) acc)))
          xs0
          Syntax3.(_Call x0 (box_list (List.map _Var xs1)))
      in
      let* dcls = set_arity x0 (List.length xs0, x1) (aux dcls) in
      return Syntax3.(_DFun x0 bnd :: _DVal x1 clo :: dcls)
    | DTm (x0, m) :: dcls ->
      let* m = trans_tm m in
      let* dcls = aux dcls in
      return Syntax3.(_DVal x0 m :: dcls)
    | DData _ :: dcls -> aux dcls
    | DMain m :: _ ->
      let* m = trans_tm m in
      return Syntax3.[ _DMain (_App L m _NULL) ]
    | [] -> return []
  in
  let dcls = aux dcls (IMap.empty, res) in
  unbox (box_list dcls)
