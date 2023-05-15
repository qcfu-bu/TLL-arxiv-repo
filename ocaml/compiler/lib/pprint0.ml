open Fmt
open Syntax0

let pipe fmt _ = pf fmt " | "
let break fmt _ = pf fmt "@.@."

let pp_sort fmt = function
  | U -> pf fmt "U"
  | L -> pf fmt "L"
  | SId id -> pf fmt "%s" id

let pp_role fmt = function
  | Pos -> pf fmt "!"
  | Neg -> pf fmt "?"

let pp_prim fmt = function
  | Stdin -> pf fmt "stdin"
  | Stdout -> pf fmt "stdout"
  | Stderr -> pf fmt "stderr"

let rec pp_tm fmt = function
  (* inference *)
  | Ann (m, a) -> pf fmt "(%a : %a)" pp_tm m pp_tm a
  | Inst (id, ss) -> pf fmt "%s‹%a›" id (list ~sep:comma pp_sort) ss
  (* core *)
  | Type U -> pf fmt "U"
  | Type L -> pf fmt "L"
  | Type (SId id) -> pf fmt "Type‹%s›" id
  | Id id -> pf fmt "%s" id
  | Pi (R, U, a, Binder (id, b)) ->
    pf fmt "(∀ (%s : %a) → %a)" id pp_tm a pp_tm b
  | Pi (N, U, a, Binder (id, b)) ->
    pf fmt "(∀ {%s : %a} → %a)" id pp_tm a pp_tm b
  | Pi (R, L, a, Binder (id, b)) ->
    pf fmt "(∀ (%s : %a) ⊸ %a)" id pp_tm a pp_tm b
  | Pi (N, L, a, Binder (id, b)) ->
    pf fmt "(∀ {%s : %a} ⊸ %a)" id pp_tm a pp_tm b
  | Pi (R, SId sid, a, Binder (id, b)) ->
    pf fmt "(forall‹%s›(%s : %a), %a)" sid id pp_tm a pp_tm b
  | Pi (N, SId sid, a, Binder (id, b)) ->
    pf fmt "(forall‹%s›{%s : %a}, %a)" sid id pp_tm a pp_tm b
  | Lam (R, U, a, Binder (id, m)) ->
    pf fmt "(fn (%s : %a) ⇒ %a)" id pp_tm a pp_tm m
  | Lam (N, U, a, Binder (id, m)) ->
    pf fmt "(fn {%s : %a} ⇒ %a)" id pp_tm a pp_tm m
  | Lam (R, L, a, Binder (id, m)) ->
    pf fmt "(ln (%s : %a) ⇒ %a)" id pp_tm a pp_tm m
  | Lam (N, L, a, Binder (id, m)) ->
    pf fmt "(ln {%s : %a} ⇒ %a)" id pp_tm a pp_tm m
  | Lam (R, SId sid, a, Binder (id, m)) ->
    pf fmt "(function‹%s›(%s), %a)" sid id pp_tm m
  | Lam (N, SId sid, a, Binder (id, m)) ->
    pf fmt "(function‹%s›{%s}, %a)" sid id pp_tm m
  | App ms -> pf fmt "(%a)" (list ~sep:sp (parens pp_tm)) ms
  | Let (R, m, Binder (Left id, n)) ->
    pf fmt "let %s = %a in %a" id pp_tm m pp_tm n
  | Let (N, m, Binder (Left id, n)) ->
    pf fmt "let {%s} = %a in %a" id pp_tm m pp_tm n
  | Let (_, m, Binder (Right p, n)) ->
    pf fmt "let %a = %a in %a" pp_p p pp_tm m pp_tm n
  (* native *)
  | Unit -> pf fmt "unit"
  | UIt -> pf fmt "()"
  | Bool -> pf fmt "bool"
  | BTrue -> pf fmt "true"
  | BFalse -> pf fmt "false"
  | Nat -> pf fmt "nat"
  | NZero -> pf fmt "O"
  | NSucc (i, m) -> pf fmt "%a.+%d" pp_tm m i
  (* data *)
  | Sigma (R, U, a, Binder (id, b)) ->
    pf fmt "(∃ (%s : %a) × %a)" id pp_tm a pp_tm b
  | Sigma (N, U, a, Binder (id, b)) ->
    pf fmt "(∃ {%s : %a} × %a)" id pp_tm a pp_tm b
  | Sigma (R, L, a, Binder (id, b)) ->
    pf fmt "(∃ (%s : %a) ⊗ %a)" id pp_tm a pp_tm b
  | Sigma (N, L, a, Binder (id, b)) ->
    pf fmt "(∃ {%s : %a} ⊗ %a)" id pp_tm a pp_tm b
  | Sigma (R, SId sid, a, Binder (id, b)) ->
    pf fmt "(exists‹%s›(%s : %a), %a)" sid id pp_tm a pp_tm b
  | Sigma (N, SId sid, a, Binder (id, b)) ->
    pf fmt "(exists‹%s›{%s : %a}, %a)" sid id pp_tm a pp_tm b
  | Pair (R, U, m, n) -> pf fmt "(%a, %a)" pp_tm m pp_tm n
  | Pair (N, U, m, n) -> pf fmt "({%a}, %a)" pp_tm m pp_tm n
  | Pair (R, L, m, n) -> pf fmt "⟨%a, %a⟩" pp_tm m pp_tm n
  | Pair (N, L, m, n) -> pf fmt "⟨{%a}, %a⟩" pp_tm m pp_tm n
  | Pair (R, SId sid, m, n) -> pf fmt "tup‹%s›(%a, %a)" sid pp_tm m pp_tm n
  | Pair (N, SId sid, m, n) -> pf fmt "tup‹%s›({%a}, %a)" sid pp_tm m pp_tm n
  | Match (m, Binder (id, a), cls) ->
    pf fmt "match %a as %s in %a with %a" pp_tm m id pp_tm a pp_cls cls
  (* equality *)
  | Eq (m, n) -> pf fmt "%a ≡ %a" pp_tm m pp_tm n
  | Refl -> pf fmt "refl"
  | Rew (Binder ((id1, id2), a), p, m) ->
    pf fmt "rew [%s, %s ⇒ %a] %a in %a" id1 id2 pp_tm a pp_tm p pp_tm m
  (* monadic *)
  | IO a -> pf fmt "IO %a" pp_tm a
  | Return m -> pf fmt "return %a" pp_tm m
  | MLet (m, Binder (Left id, n)) ->
    pf fmt "let %s ⇐ %a in %a" id pp_tm m pp_tm n
  | MLet (m, Binder (Right p, n)) ->
    pf fmt "let %a ⇐ %a in %a" pp_p p pp_tm m pp_tm n
  (* session *)
  | Proto -> pf fmt "proto"
  | End -> pf fmt "end"
  | Act (R, rol, a, Binder (id, b)) ->
    pf fmt "%a(%s : %a) → %a" pp_role rol id pp_tm a pp_tm b
  | Act (N, rol, a, Binder (id, b)) ->
    pf fmt "%a{%s : %a} → %a" pp_role rol id pp_tm a pp_tm b
  | Ch (Pos, a) -> pf fmt "ch‹%a›" pp_tm a
  | Ch (Neg, a) -> pf fmt "hc‹%a›" pp_tm a
  | Open prim -> pf fmt "open %a" pp_prim prim
  | Fork (a, Binder (id, m)) -> pf fmt "fork (%s : %a) in %a" id pp_tm a pp_tm m
  | Recv m -> pf fmt "recv %a" pp_tm m
  | Send m -> pf fmt "send %a" pp_tm m
  | Close m -> pf fmt "close %a" pp_tm m
  | Sleep m -> pf fmt "sleep %a" pp_tm m
  | Rand (m, n) -> pf fmt "rand %a %a" pp_tm m pp_tm n

and pp_p fmt = function
  | PIt -> pf fmt "()"
  | PTrue -> pf fmt "true"
  | PFalse -> pf fmt "false"
  | PZero -> pf fmt "O"
  | PSucc id -> pf fmt "S %s" id
  | PPair (R, U, id1, id2) -> pf fmt "(%s, %s)" id1 id2
  | PPair (N, U, id1, id2) -> pf fmt "({%s}, %s)" id1 id2
  | PPair (R, L, id1, id2) -> pf fmt "⟨%s, %s⟩" id1 id2
  | PPair (N, L, id1, id2) -> pf fmt "⟨{%s}, %s⟩" id1 id2
  | PPair (R, SId sid, id1, id2) -> pf fmt "tup‹%s›(%s, %s)" sid id1 id2
  | PPair (N, SId sid, id1, id2) -> pf fmt "tup‹%s›({%s}, %s)" sid id1 id2
  | PCons (id, ids) -> pf fmt "%s %a" id (list ~sep:sp string) ids

and pp_cl fmt (Binder (p, m)) = pf fmt "%a ⇒ %a" pp_p p pp_tm m
and pp_cls fmt cls = list ~sep:pipe pp_cl fmt cls

let pp_scheme pp fmt (Binder (sids, m)) =
  pf fmt "‹%a› %a" (list ~sep:comma string) sids pp m

let rec pp_ptm fmt = function
  | PBase b -> pf fmt ": %a" pp_tm b
  | PBind (a, Binder (id, ptm)) -> pf fmt "(%s : %a) %a" id pp_tm a pp_ptm ptm

let rec pp_tele fmt = function
  | TBase b -> pf fmt "→ %a" pp_tm b
  | TBind (R, a, Binder (id, tl)) -> pf fmt "(%s : %a) %a" id pp_tm a pp_tele tl
  | TBind (N, a, Binder (id, tl)) -> pf fmt "{%s : %a} %a" id pp_tm a pp_tele tl

let rec pp_ptl fmt = function
  | PBase b -> pp_tele fmt b
  | PBind (a, Binder (id, ptl)) -> pf fmt "{%s : %a} %a" id pp_tm a pp_ptl ptl

let rec pp_args fmt = function
  | ABase (b, m) -> pf fmt ": %a = %a" pp_tm b pp_tm m
  | ABind (R, a, Binder (id, args)) ->
    pf fmt "(%s : %a) %a" id pp_tm a pp_args args
  | ABind (N, a, Binder (id, args)) ->
    pf fmt "{%s : %a} %a" id pp_tm a pp_args args

let pp_dcons fmt (DCons (id, sch)) = pf fmt "%s of %a" id (pp_scheme pp_ptl) sch

let pp_dcl fmt = function
  | DTm (R, id, sch) -> pf fmt "program %s%a" id (pp_scheme pp_args) sch
  | DTm (N, id, sch) -> pf fmt "logical %s%a" id (pp_scheme pp_args) sch
  | DData (id, sch, dconss) ->
    pf fmt "inductive %s%a = %a" id (pp_scheme pp_ptm) sch
      (list ~sep:pipe pp_dcons) dconss

let pp_dcls fmt dcls = pf fmt "%a" (list ~sep:break pp_dcl) dcls
