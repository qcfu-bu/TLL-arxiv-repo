open Util
open Fmt
open Bindlib
open Names
open Syntax3
open Prelude1

let rec nat_of = function
  | Int i -> Int i
  | Add (0, m) -> nat_of m
  | Add (i, m) -> (
    match nat_of m with
    | Int j -> Int (i + j)
    | Add (j, m) when i + j = 0 -> m
    | Add (j, m) -> Add (i + j, m)
    | m -> Add (i, m))
  | m -> m

let char_of m =
  match m with
  | Cons (c, [ m ]) when C.equal c char_c -> (
    match nat_of m with
    | Int i -> Some (Char.chr (i mod 256))
    | _ -> None)
  | _ -> None

let rec string_of = function
  | Cons (c, []) when C.equal c emptyString_c -> Some ""
  | Cons (c, [ m; n ]) when C.equal c string_c -> (
    match (char_of m, string_of n) with
    | Some c, Some s -> Some (str "%c%s" c s)
    | _ -> None)
  | _ -> None

let pipe fmt _ = pf fmt " | "
let break fmt _ = pf fmt "@.@."

let rec pp_sort fmt = function
  | U -> pf fmt "U"
  | L -> pf fmt "L"

let pp_prim fmt = function
  | Stdin -> pf fmt "stdin"
  | Stdout -> pf fmt "stdout"
  | Stderr -> pf fmt "stderr"

let rec gather_lam s m =
  match m with
  | Lam (t, bnd) ->
    if s = t then
      let x, m = unbind bnd in
      let xs, m = gather_lam s m in
      (x :: xs, m)
    else
      ([], m)
  | _ -> ([], m)

and pp_tm fmt = function
  (* core *)
  | Var x -> V.pp fmt x
  | Const x -> pf fmt "%a" I.pp x
  | Lam (s, bnd) -> (
    let x, m = unbind bnd in
    let xs, m = gather_lam s m in
    let xs = x :: xs in
    match s with
    | U -> pf fmt "@[fn @[%a@] ⇒@;<1 2>@[%a@]@]" (list ~sep:sp V.pp) xs pp_tm m
    | L -> pf fmt "@[ln @[%a@] ⇒@;<1 2>@[%a@]@]" (list ~sep:sp V.pp) xs pp_tm m)
  | Call (x, ms) -> pf fmt "@[%a(@[%a@])@]" I.pp x (list ~sep:comma pp_tm) ms
  | App (_, m, n) -> pf fmt "@[(%a)@;<1 2>@[%a@]@]" pp_tm m pp_tm n
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    pf fmt "@[@[let %a =@;<1 2>%a@;<1 0>in@]@;<1 0>%a@]" V.pp x pp_tm m pp_tm n
  (* native *)
  | Int i -> pf fmt "%d" i
  | Add _ as m -> (
    match nat_of m with
    | Int n -> pf fmt "%d" n
    | Add (i, m) when 0 <= i -> pf fmt "%a.+%d" pp_tm m (abs i)
    | Add (i, m) when i < 0 -> pf fmt "%a.-%d" pp_tm m (abs i)
    | m -> pf fmt "%a" pp_tm m)
  | Ifte (m, n1, n2) ->
    pf fmt "@[<v 0>@[if @[%a@] then@]@;<1 2>@[%a@]@;<1 0>else@;<1 2>@[%a@]@]"
      pp_tm m pp_tm n1 pp_tm n2
  (* data *)
  | Pair (m, n) -> pf fmt "(%a, %a)" pp_tm m pp_tm n
  | Cons (c, []) -> pf fmt "%a" C.pp c
  | Cons (c, ms) as m ->
    if C.equal c char_c then
      match char_of m with
      | Some c -> pf fmt "%C" c
      | None -> pf fmt "@[(%a@;<1 2>@[%a@])@]" C.pp c (list ~sep:sp pp_tm) ms
    else if C.equal c string_c then
      match string_of m with
      | Some s -> pf fmt "%S" s
      | None -> pf fmt "@[(%a@;<1 2>@[%a@])@]" C.pp c (list ~sep:sp pp_tm) ms
    else
      pf fmt "@[(%a@;<1 2>@[%a@])@]" C.pp c (list ~sep:sp pp_tm) ms
  | Match (_, m, cls) ->
    pf fmt "@[<v 0>@[match %a with@]@;<1 0>@[%a@]@;<1 0>end@]" pp_tm m pp_cls
      cls
  (* effect *)
  | Open prim -> pf fmt "open %a" pp_prim prim
  | Fork bnd ->
    let x, m = unbind bnd in
    pf fmt "@[@[fork %a in@]@;<1 2>%a@]" V.pp x pp_tm m
  | Recv m -> pf fmt "recv(%a)" pp_tm m
  | Send (m, n) -> pf fmt "send(%a, %a)" pp_tm m pp_tm n
  | Close m -> pf fmt "close(%a)" pp_tm m
  | Sleep m -> pf fmt "sleep(%a)" pp_tm m
  | NULL -> pf fmt "NULL"

and pp_cl fmt = function
  | PPair bnd ->
    let xs, m = unmbind bnd in
    pf fmt "| @[(%a, %a) ⇒@;<1 0>%a@]" V.pp xs.(0) V.pp xs.(1) pp_tm m
  | PCons (c, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "| @[%a %a ⇒@;<1 0>%a@]" C.pp c (array ~sep:sp V.pp) xs pp_tm m

and pp_cls fmt = function
  | [] -> ()
  | [ cl ] -> pp_cl fmt cl
  | cl :: cls -> pf fmt "%a@;<1 0>%a" pp_cl cl pp_cls cls

let rec pp_dcl fmt = function
  | DFun (x, bnd) ->
    let xs, m = unmbind bnd in
    pf fmt "@[fun %a(%a) =@;<1 2>%a@]" I.pp x (array ~sep:comma V.pp) xs pp_tm m
  | DVal (x, m) -> pf fmt "@[val %a =@;<1 2>%a@]" I.pp x pp_tm m
  | DMain m -> pf fmt "@[main =@;<1 2>%a@]" pp_tm m

let pp_dcls fmt dcls = pf fmt "%a" (list ~sep:break pp_dcl) dcls
