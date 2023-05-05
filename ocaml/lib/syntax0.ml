open Util
open Names

(* syntax definitions *)
type id = string
type ids = id list

type sort =
  | U
  | L
  | SId of id

type sorts = sort list

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

type p =
  | PIt
  | PTrue
  | PFalse
  | PZero
  | PSucc of id
  | PPair of rel * sort * id * id
  | PCons of id * ids

type ('a, 'b) binder = Binder of 'a * 'b

type tm =
  (* inference *)
  | Ann of tm * tm
  | Inst of id * sorts
  (* core *)
  | Type of sort
  | Id of id
  | Pi of rel * sort * tm * (id, tm) binder
  | Lam of rel * sort * tm * (id, tm) binder
  | App of tms
  | Let of rel * tm * ((id, p) either, tm) binder
  (* native *)
  | Unit
  | UIt
  | Bool
  | BTrue
  | BFalse
  | Nat
  | NZero
  | NSucc of int * tm
  (* data *)
  | Sigma of rel * sort * tm * (id, tm) binder
  | Pair of rel * sort * tm * tm
  | Match of tm * (id, tm) binder * cls
  (* equality *)
  | Eq of tm * tm
  | Refl
  | Rew of (id * id, tm) binder * tm * tm
  (* monadic *)
  | IO of tm
  | Return of tm
  | MLet of tm * ((id, p) either, tm) binder
  (* session *)
  | Proto
  | End
  | Act of rel * role * tm * (id, tm) binder
  | Ch of role * tm
  | Open of prim
  | Fork of tm * (id, tm) binder
  | Recv of tm
  | Send of tm
  | Close of tm
  | Sleep of tm

and tms = tm list
and cl = (p, tm) binder
and cls = cl list

type dcl =
  | DTm of rel * id * args scheme
  | DData of id * tm param scheme * dconss

and dcls = dcl list
and dcons = DCons of id * tele param scheme
and dconss = dcons list
and 'a scheme = (ids, 'a) binder

and 'a param =
  | PBase of 'a
  | PBind of tm * (id, 'a param) binder

and tele =
  | TBase of tm
  | TBind of rel * tm * (id, tele) binder

and args =
  | ABase of tm * tm
  | ABind of rel * tm * (id, args) binder
