open Fmt
open Bindlib
open Names

(* syntax definitions *)
type sort =
  | U
  | L
  | SVar of sort var
  | SMeta of M.t * sorts

and sorts = sort list

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
  (* inference *)
  | Ann of tm * tm
  | Meta of M.t * sorts * tms
  (* core *)
  | Type of sort
  | Var of tm var
  | Const of I.t * sorts
  | Pi of rel * sort * tm * (tm, tm) binder
  | Lam of rel * sort * tm * (tm, tm) binder
  | App of tm * tm
  | Let of rel * tm * (tm, tm) binder
  (* native *)
  | Unit of sort
  | UIt of sort
  | Bool
  | BTrue
  | BFalse
  | Nat
  | NZero
  | NSucc of int * tm
  (* data *)
  | Sigma of rel * rel * sort * tm * (tm, tm) binder
  | Pair of rel * rel * sort * tm * tm
  | Data of D.t * sorts * tms
  | Cons of C.t * sorts * tms * tms
  | Match of rel * tm * (tm, tm) binder * cls
  (* absurd *)
  | Bot
  | Absurd of tm * tm
  (* equality *)
  | Eq of tm * tm * tm
  | Refl of tm
  | Rew of (tm, tm) mbinder * tm * tm
  (* monadic *)
  | IO of tm
  | Return of tm
  | MLet of tm * (tm, tm) binder
  (* session *)
  | Proto
  | End
  | Act of rel * role * tm * (tm, tm) binder
  | Ch of role * tm
  | Open of prim
  | Fork of tm * (tm, tm) binder
  | Recv of tm
  | Send of tm
  | Close of tm
  (* effects *)
  | Sleep of tm
  | Rand of tm * tm

and tms = tm list

and cl =
  | PIt of sort * tm
  | PTrue of tm
  | PFalse of tm
  | PZero of tm
  | PSucc of (tm, tm) binder
  | PPair of rel * rel * sort * (tm, tm) mbinder
  | PCons of C.t * (tm, tm) mbinder

and cls = cl list

type dcl =
  | DTm of rel * I.t * bool * (tm * tm) scheme
  | DData of rel * D.t * tm param scheme * dconss

and 'a scheme = (sort, 'a) mbinder
and dcls = dcl list
and dcons = DCons of C.t * tele param scheme
and dconss = dcons list

and 'a param =
  | PBase of 'a
  | PBind of tm * (tm, 'a param) binder

and tele =
  | TBase of tm
  | TBind of rel * tm * (tm, tele) binder

(* sort equality *)
let eq_sort s1 s2 =
  match (s1, s2) with
  | SVar x, SVar y -> eq_vars x y
  | SMeta (x, _), SMeta (y, _) -> M.equal x y
  | _ -> s1 = s2

(* variable set/map *)
module SV = struct
  type t = sort var

  let mk = new_var (fun x -> SVar x)
  let compare = compare_vars
  let pp fmt x = pf fmt "%s_s%d" (name_of x) (uid_of x)
end

module SVSet = Set.Make (SV)
module SVMap = Map.Make (SV)

module V = struct
  type t = tm var

  let mk = new_var (fun x -> Var x)
  let compare = compare_vars
  let pp fmt x = pf fmt "%s_v%d" (name_of x) (uid_of x)
end

module VSet = Set.Make (V)
module VMap = Map.Make (V)

(* smart constructors *)
let var x = Var x

(* sort *)
let _U = box U
let _L = box L
let _SVar = box_var
let _SMeta x = box_apply (fun ss -> SMeta (x, ss))

(* rel *)
let _N = box N
let _R = box R

(* role *)
let _Pos = box Pos
let _Neg = box Neg

(* prim *)
let _Stdin = box Stdin
let _Stdout = box Stdout
let _Stderr = box Stderr

(* inference *)
let _Ann = box_apply2 (fun m a -> Ann (m, a))
let _Meta x = box_apply2 (fun ss ms -> Meta (x, ss, ms))

(* core *)
let _Type = box_apply (fun s -> Type s)
let _Var = box_var
let _Const x = box_apply (fun ss -> Const (x, ss))
let _Pi rel = box_apply3 (fun s a bnd -> Pi (rel, s, a, bnd))
let _Lam rel = box_apply3 (fun s a bnd -> Lam (rel, s, a, bnd))
let _App = box_apply2 (fun m n -> App (m, n))
let _Let rel = box_apply2 (fun m bnd -> Let (rel, m, bnd))

(* native *)
let _Unit = box_apply (fun s -> Unit s)
let _UIt = box_apply (fun s -> UIt s)
let _Bool = box Bool
let _BTrue = box BTrue
let _BFalse = box BFalse
let _Nat = box Nat
let _NZero = box NZero
let _NSucc i = box_apply (fun m -> NSucc (i, m))

(* data *)
let _Sigma rel1 rel2 = box_apply3 (fun s a bnd -> Sigma (rel1, rel2, s, a, bnd))
let _Pair rel1 rel2 = box_apply3 (fun s m n -> Pair (rel1, rel2, s, m, n))
let _Data d = box_apply2 (fun ss ms -> Data (d, ss, ms))
let _Cons c = box_apply3 (fun ss ms ns -> Cons (c, ss, ms, ns))
let _Match rel = box_apply3 (fun m bnd cls -> Match (rel, m, bnd, cls))

(* absurd *)
let _Bot = box Bot
let _Absurd = box_apply2 (fun a m -> Absurd (a, m))

(* equality *)
let _Eq = box_apply3 (fun a m n -> Eq (a, m, n))
let _Refl = box_apply (fun m -> Refl m)
let _Rew = box_apply3 (fun bnd pf m -> Rew (bnd, pf, m))

(* monadic *)
let _IO = box_apply (fun a -> IO a)
let _Return = box_apply (fun m -> Return m)
let _MLet = box_apply2 (fun m bnd -> MLet (m, bnd))

(* session *)
let _Proto = box Proto
let _End = box End
let _Act rel rol = box_apply2 (fun a bnd -> Act (rel, rol, a, bnd))
let _Ch rol = box_apply (fun a -> Ch (rol, a))
let _Open prim = box (Open prim)
let _Fork = box_apply2 (fun a bnd -> Fork (a, bnd))
let _Recv = box_apply (fun m -> Recv m)
let _Send = box_apply (fun m -> Send m)
let _Close = box_apply (fun m -> Close m)

(* effects *)
let _Sleep = box_apply (fun m -> Sleep m)
let _Rand = box_apply2 (fun m n -> Rand (m, n))

(* cl *)
let _PIt = box_apply2 (fun s m -> PIt (s, m))
let _PTrue = box_apply (fun m -> PTrue m)
let _PFalse = box_apply (fun m -> PFalse m)
let _PZero = box_apply (fun m -> PZero m)
let _PSucc = box_apply (fun m -> PSucc m)
let _PPair rel1 rel2 = box_apply2 (fun s bnd -> PPair (rel1, rel2, s, bnd))
let _PCons c = box_apply (fun bnd -> PCons (c, bnd))

(* dcl *)
let _DTm rel x guard = box_apply (fun sch -> DTm (rel, x, guard, sch))
let _DData rel d = box_apply2 (fun sch dconss -> DData (rel, d, sch, dconss))

(* dcons *)
let _DCons c = box_apply (fun sch -> DCons (c, sch))

(* param *)
let _PBase a = box_apply (fun a -> PBase a) a
let _PBind a bnd = box_apply2 (fun a bnd -> PBind (a, bnd)) a bnd

(* tele *)
let _TBase = box_apply (fun a -> TBase a)
let _TBind rel = box_apply2 (fun a bnd -> TBind (rel, a, bnd))

(* lifting *)
let rec lift_sort = function
  | U -> _U
  | L -> _L
  | SVar x -> _SVar x
  | SMeta (x, ss) ->
    let ss = List.map lift_sort ss in
    _SMeta x (box_list ss)

let rec lift_tm = function
  (* inference *)
  | Ann (m, a) -> _Ann (lift_tm m) (lift_tm a)
  | Meta (x, ss, ms) ->
    let ss = List.map lift_sort ss in
    let ms = List.map lift_tm ms in
    _Meta x (box_list ss) (box_list ms)
  (* core *)
  | Type s -> _Type (lift_sort s)
  | Var x -> _Var x
  | Const (x, ss) ->
    let ss = List.map lift_sort ss in
    _Const x (box_list ss)
  | Pi (rel, s, a, bnd) ->
    _Pi rel (lift_sort s) (lift_tm a) (box_binder lift_tm bnd)
  | Lam (rel, s, a, bnd) ->
    _Lam rel (lift_sort s) (lift_tm a) (box_binder lift_tm bnd)
  | App (m, n) -> _App (lift_tm m) (lift_tm n)
  | Let (rel, m, bnd) -> _Let rel (lift_tm m) (box_binder lift_tm bnd)
  (* native *)
  | Unit s -> _Unit (lift_sort s)
  | UIt s -> _UIt (lift_sort s)
  | Bool -> _Bool
  | BTrue -> _BTrue
  | BFalse -> _BFalse
  | Nat -> _Nat
  | NZero -> _NZero
  | NSucc (i, m) -> _NSucc i (lift_tm m)
  (* data *)
  | Sigma (rel1, rel2, s, a, bnd) ->
    _Sigma rel1 rel2 (lift_sort s) (lift_tm a) (box_binder lift_tm bnd)
  | Pair (rel1, rel2, s, m, n) ->
    _Pair rel1 rel2 (lift_sort s) (lift_tm m) (lift_tm n)
  | Data (d, ss, ms) ->
    let ss = List.map lift_sort ss in
    let ms = List.map lift_tm ms in
    _Data d (box_list ss) (box_list ms)
  | Cons (c, ss, ms, ns) ->
    let ss = List.map lift_sort ss in
    let ms = List.map lift_tm ms in
    let ns = List.map lift_tm ns in
    _Cons c (box_list ss) (box_list ms) (box_list ns)
  | Match (rel, m, bnd, cls) ->
    let cls =
      List.map
        (function
          | PIt (s, m) -> _PIt (lift_sort s) (lift_tm m)
          | PTrue m -> _PTrue (lift_tm m)
          | PFalse m -> _PFalse (lift_tm m)
          | PZero m -> _PZero (lift_tm m)
          | PSucc bnd -> _PSucc (box_binder lift_tm bnd)
          | PPair (rel1, rel2, s, bnd) ->
            _PPair rel1 rel2 (lift_sort s) (box_mbinder lift_tm bnd)
          | PCons (c, bnd) -> _PCons c (box_mbinder lift_tm bnd))
        cls
    in
    _Match rel (lift_tm m) (box_binder lift_tm bnd) (box_list cls)
  (* absurd *)
  | Bot -> _Bot
  | Absurd (a, m) -> _Absurd (lift_tm a) (lift_tm m)
  (* equality *)
  | Eq (a, m, n) -> _Eq (lift_tm a) (lift_tm m) (lift_tm n)
  | Refl m -> _Refl (lift_tm m)
  | Rew (bnd, pf, m) -> _Rew (box_mbinder lift_tm bnd) (lift_tm pf) (lift_tm m)
  (* monadic *)
  | IO a -> _IO (lift_tm a)
  | Return m -> _Return (lift_tm m)
  | MLet (m, bnd) -> _MLet (lift_tm m) (box_binder lift_tm bnd)
  (* session *)
  | Proto -> _Proto
  | End -> _End
  | Act (rel, rol, a, bnd) -> _Act rel rol (lift_tm a) (box_binder lift_tm bnd)
  | Ch (rol, m) -> _Ch rol (lift_tm m)
  | Open prim -> _Open prim
  | Fork (a, bnd) -> _Fork (lift_tm a) (box_binder lift_tm bnd)
  | Recv m -> _Recv (lift_tm m)
  | Send m -> _Send (lift_tm m)
  | Close m -> _Close (lift_tm m)
  (* effects *)
  | Sleep m -> _Sleep (lift_tm m)
  | Rand (m, n) -> _Rand (lift_tm m) (lift_tm n)

let rec lift_param lift = function
  | PBase a -> _PBase (lift a)
  | PBind (a, bnd) -> _PBind (lift_tm a) (box_binder (lift_param lift) bnd)

let rec lift_tele = function
  | TBase a -> _TBase (lift_tm a)
  | TBind (rel, a, bnd) -> _TBind rel (lift_tm a) (box_binder lift_tele bnd)

let lift_dcons (DCons (c, sch)) =
  _DCons c (box_mbinder (lift_param lift_tele) sch)

let lift_dconss dconss = box_list (List.map lift_dcons dconss)

let lift_dcl = function
  | DTm (rel, x, guard, sch) ->
    _DTm rel x guard
      (box_mbinder (fun (a, m) -> box_pair (lift_tm a) (lift_tm m)) sch)
  | DData (rel, d, sch, dconss) ->
    _DData rel d (box_mbinder (lift_param lift_tm) sch) (lift_dconss dconss)

let lift_dcls dcls = box_list (List.map lift_dcl dcls)

(* utility *)
let _mLam rel s xs m =
  List.fold_right (fun (x, a) m -> _Lam rel s a (bind_var x m)) xs m

let _mkApps hd ms = List.fold_left _App hd ms
let mkApps hd ms = List.fold_left (fun hd m -> App (hd, m)) hd ms

let unApps m =
  let rec aux m ns =
    match m with
    | App (m, n) -> aux m (n :: ns)
    | _ -> (m, ns)
  in
  aux m []
