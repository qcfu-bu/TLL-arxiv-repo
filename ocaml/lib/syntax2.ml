open Fmt
open Bindlib
open Names

type sort =
  | U
  | L

type rel =
  | N
  | R

type role =
  | Pos
  | Neg

type prim =
  | Stdin
  | Stdout
  | Stderr

type tm =
  (* core *)
  | Var of tm var
  | Const of I.t
  | Lam of sort * (tm, tm) binder
  | App of sort * tm * tm
  | Let of tm * (tm, tm) binder
  (* native *)
  | UIt
  | BTrue
  | BFalse
  | NZero
  | NSucc of int * tm
  (* data *)
  | Pair of tm * tm
  | Cons of C.t * tms
  | Match of sort * tm * cls
  (* monadic *)
  | Return of tm
  | MLet of tm * (tm, tm) binder
  (* session *)
  | Open of prim
  | Fork of (tm, tm) binder
  | Recv of rel * tm
  | Send of rel * sort * tm
  | Close of role * tm
  | Sleep of tm
  (* erasure *)
  | NULL

and tms = tm list

and cl =
  | PIt of tm
  | PTrue of tm
  | PFalse of tm
  | PZero of tm
  | PSucc of (tm, tm) binder
  | PPair of (tm, tm) mbinder
  | PCons of C.t * (tm, tm) mbinder

and cls = cl list

type dcl =
  | DTm of I.t * tm
  | DData of D.t * dconss
  | DMain of tm

and dcons = DCons of C.t * int
and dconss = dcons list

module V = struct
  type t = tm var

  let mk = new_var (fun x -> Var x)
  let compare = compare_vars
  let pp fmt x = pf fmt "%s_v%d" (name_of x) (uid_of x)
  let to_string x = to_to_string pp x
end

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
let _App s = box_apply2 (fun m n -> App (s, m, n))
let _Let = box_apply2 (fun m bnd -> Let (m, bnd))

(* native *)
let _UIt = box UIt
let _BTrue = box BTrue
let _BFalse = box BFalse
let _NZero = box NZero
let _NSucc i = box_apply (fun m -> NSucc (i, m))

(* data *)
let _Pair = box_apply2 (fun m n -> Pair (m, n))
let _Cons c = box_apply (fun ms -> Cons (c, ms))
let _Match s = box_apply2 (fun m cls -> Match (s, m, cls))

(* monadic *)
let _Return = box_apply (fun m -> Return m)
let _MLet = box_apply2 (fun m bnd -> MLet (m, bnd))

(* session *)
let _Open prim = box (Open prim)
let _Fork = box_apply (fun bnd -> Fork bnd)
let _Recv rel = box_apply (fun m -> Recv (rel, m))
let _Send rel s = box_apply (fun m -> Send (rel, s, m))
let _Close rol = box_apply (fun m -> Close (rol, m))
let _Sleep = box_apply (fun m -> Sleep m)

(* erasure *)
let _NULL = box NULL

(* cl *)
let _PIt = box_apply (fun rhs -> PIt rhs)
let _PTrue = box_apply (fun rhs -> PTrue rhs)
let _PFalse = box_apply (fun rhs -> PFalse rhs)
let _PZero = box_apply (fun rhs -> PZero rhs)
let _PSucc = box_apply (fun bnd -> PSucc bnd)
let _PPair = box_apply (fun bnd -> PPair bnd)
let _PCons c = box_apply (fun bnd -> PCons (c, bnd))

(* dcl *)
let _DTm x = box_apply (fun m -> DTm (x, m))
let _DData d = box_apply (fun dconss -> DData (d, dconss))
let _DMain = box_apply (fun m -> DMain m)

(* dcons *)
let _DCons c i = box (DCons (c, i))

let rec lift_tm = function
  (* core *)
  | Var x -> _Var x
  | Const x -> _Const x
  | Lam (s, bnd) -> _Lam s (box_binder lift_tm bnd)
  | App (s, m, n) -> _App s (lift_tm m) (lift_tm n)
  | Let (m, bnd) -> _Let (lift_tm m) (box_binder lift_tm bnd)
  (* native *)
  | UIt -> _UIt
  | BTrue -> _BTrue
  | BFalse -> _BFalse
  | NZero -> _NZero
  | NSucc (i, m) -> _NSucc i (lift_tm m)
  (* data *)
  | Pair (m, n) -> _Pair (lift_tm m) (lift_tm n)
  | Cons (c, ms) ->
    let ms = List.map lift_tm ms in
    _Cons c (box_list ms)
  | Match (s, m, cls) ->
    let cls =
      List.map
        (function
          | PIt rhs -> _PIt (lift_tm rhs)
          | PTrue rhs -> _PTrue (lift_tm rhs)
          | PFalse rhs -> _PFalse (lift_tm rhs)
          | PZero rhs -> _PZero (lift_tm rhs)
          | PSucc bnd -> _PSucc (box_binder lift_tm bnd)
          | PPair bnd -> _PPair (box_mbinder lift_tm bnd)
          | PCons (c, bnd) -> _PCons c (box_mbinder lift_tm bnd))
        cls
    in
    _Match s (lift_tm m) (box_list cls)
  (* monadic *)
  | Return m -> _Return (lift_tm m)
  | MLet (m, bnd) -> _MLet (lift_tm m) (box_binder lift_tm bnd)
  (* session *)
  | Open prim -> _Open prim
  | Fork bnd -> _Fork (box_binder lift_tm bnd)
  | Recv (rel, m) -> _Recv rel (lift_tm m)
  | Send (rel, s, m) -> _Send rel s (lift_tm m)
  | Close (rol, m) -> _Close rol (lift_tm m)
  | Sleep m -> _Sleep (lift_tm m)
  (* erasure *)
  | NULL -> _NULL

let lift_dcons (DCons (c, i)) = _DCons c i
let lift_dconss dconss = box_list (List.map lift_dcons dconss)

let lift_dcl = function
  | DTm (x, m) -> _DTm x (lift_tm m)
  | DData (d, dconss) -> _DData d (lift_dconss dconss)
  | DMain m -> _DMain (lift_tm m)

let lift_dcls dcls = box_list (List.map lift_dcl dcls)

let unApps m =
  let rec aux m ns =
    match m with
    | App (s, m, n) -> aux m ((n, s) :: ns)
    | _ -> (m, ns)
  in
  aux m []
