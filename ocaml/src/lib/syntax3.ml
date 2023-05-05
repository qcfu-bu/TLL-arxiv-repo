open Fmt
open Bindlib
open Names

type sort =
  | U
  | L

type prim =
  | Stdin
  | Stdout
  | Stderr

type tm =
  (* core *)
  | Var of tm var
  | Const of I.t
  | Lam of sort * (tm, tm) binder
  | Call of I.t * tms
  | App of sort * tm * tm
  | Let of tm * (tm, tm) binder
  (* native *)
  | Int of int
  | Add of int * tm
  | Ifte of tm * tm * tm
  (* data *)
  | Pair of tm * tm
  | Cons of C.t * tms
  | Match of sort * tm * cls
  (* effect (non-monadic) *)
  | Open of prim
  | Fork of (tm, tm) binder
  | Recv of tm
  | Send of tm * tm
  | Close of tm
  | Sleep of tm
  (* erasure *)
  | NULL

and tms = tm list

and cl =
  | PPair of (tm, tm) mbinder
  | PCons of C.t * (tm, tm) mbinder

and cls = cl list

type dcl =
  | DFun of I.t * (tm, tm) mbinder
  | DVal of I.t * tm
  | DMain of tm

module V = struct
  type t = tm var

  let mk = new_var (fun x -> Var x)
  let compare = compare_vars
  let pp fmt x = pf fmt "%s_v%d" (name_of x) (uid_of x)
  let to_string x = to_to_string pp x
end

module VSet = Set.Make (V)
module VMap = Map.Make (V)

(* smart constructors *)
let var x = Var x

(* prim *)
let _Stdin = box Stdin
let _Stdout = box Stdout
let _Stderr = box Stderr

(* core *)
let _Var = box_var
let _Const x = box (Const x)
let _Lam s = box_apply (fun bnd -> Lam (s, bnd))
let _Call x = box_apply (fun ms -> Call (x, ms))
let _App s = box_apply2 (fun m n -> App (s, m, n))
let _Let = box_apply2 (fun m bnd -> Let (m, bnd))

(* native *)
let _Int i = box (Int i)
let _Add i = box_apply (fun m -> Add (i, m))
let _Ifte = box_apply3 (fun m n1 n2 -> Ifte (m, n1, n2))

(* data *)
let _Pair = box_apply2 (fun m n -> Pair (m, n))
let _Cons c = box_apply (fun ms -> Cons (c, ms))
let _Match s = box_apply2 (fun m cls -> Match (s, m, cls))

(* effect *)
let _Open prim = box (Open prim)
let _Fork = box_apply (fun bnd -> Fork bnd)
let _Recv = box_apply (fun m -> Recv m)
let _Send = box_apply2 (fun m n -> Send (m, n))
let _Close = box_apply (fun m -> Close m)
let _Sleep = box_apply (fun m -> Sleep m)

(* erasure *)
let _NULL = box NULL

(* cl *)
let _PPair = box_apply (fun bnd -> PPair bnd)
let _PCons c = box_apply (fun bnd -> PCons (c, bnd))

(* dcl *)
let _DFun x = box_apply (fun bnd -> DFun (x, bnd))
let _DVal x = box_apply (fun m -> DVal (x, m))
let _DMain = box_apply (fun m -> DMain m)

let rec lift_tm = function
  (* core *)
  | Var x -> _Var x
  | Const x -> _Const x
  | Lam (s, bnd) -> _Lam s (box_binder lift_tm bnd)
  | Call (x, ms) ->
    let ms = List.map lift_tm ms in
    _Call x (box_list ms)
  | App (s, m, n) -> _App s (lift_tm m) (lift_tm n)
  | Let (m, bnd) -> _Let (lift_tm m) (box_binder lift_tm bnd)
  (* native *)
  | Int i -> _Int i
  | Add (i, m) -> _Add i (lift_tm m)
  | Ifte (m, n1, n2) -> _Ifte (lift_tm m) (lift_tm n1) (lift_tm n2)
  (* data *)
  | Pair (m, n) -> _Pair (lift_tm m) (lift_tm n)
  | Cons (c, ms) ->
    let ms = List.map lift_tm ms in
    _Cons c (box_list ms)
  | Match (s, m, cls) ->
    let cls =
      List.map
        (function
          | PPair bnd -> _PPair (box_mbinder lift_tm bnd)
          | PCons (c, bnd) -> _PCons c (box_mbinder lift_tm bnd))
        cls
    in
    _Match s (lift_tm m) (box_list cls)
  (* effect *)
  | Open prim -> _Open prim
  | Fork bnd -> _Fork (box_binder lift_tm bnd)
  | Recv m -> _Recv (lift_tm m)
  | Send (m, n) -> _Send (lift_tm m) (lift_tm n)
  | Close m -> _Close (lift_tm m)
  | Sleep m -> _Sleep (lift_tm m)
  (* erasure *)
  | NULL -> _NULL

let lift_dcl = function
  | DFun (x, bnd) -> _DFun x (box_mbinder lift_tm bnd)
  | DVal (x, m) -> _DVal x (lift_tm m)
  | DMain m -> _DMain (lift_tm m)

let lift_dcls dcls = box_list (List.map lift_dcl dcls)
let _mkApps hd sp = List.fold_left (fun hd (m, s) -> _App s hd m) hd sp

let unApps m =
  let rec aux m ns =
    match m with
    | App (s, m, n) -> aux m ((n, s) :: ns)
    | _ -> (m, ns)
  in
  aux m []
