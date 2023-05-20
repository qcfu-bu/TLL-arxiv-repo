open Fmt
open Util
open Bindlib
open Names
open Syntax0

type nspc_entry =
  | EVar of Syntax1.V.t
  | EConst of I.t * int
  | ESVar of Syntax1.SV.t
  | EData of D.t * int
  | ECons of C.t * int * int

type nspc = (string * nspc_entry) list

let find_var s nspc =
  let opt =
    List.find_opt
      (fun (k, entry) ->
        if s = k then
          match entry with
          | EVar _ -> true
          | _ -> false
        else
          false)
      nspc
  in
  match opt with
  | Some (_, EVar x) -> Some x
  | _ -> None

let find_const s nspc =
  let opt =
    List.find_opt
      (fun (k, entry) ->
        if s = k then
          match entry with
          | EConst _ -> true
          | _ -> false
        else
          false)
      nspc
  in
  match opt with
  | Some (_, EConst (x, _)) -> Some x
  | _ -> None

let find_svar s nspc =
  let opt =
    List.find_opt
      (fun (k, entry) ->
        if s = k then
          match entry with
          | ESVar _ -> true
          | _ -> false
        else
          false)
      nspc
  in
  match opt with
  | Some (_, ESVar x) -> Some x
  | _ -> None

let find_cons s nspc =
  let opt =
    List.find_opt
      (fun (k, entry) ->
        if s = k then
          match entry with
          | ECons _ -> true
          | _ -> false
        else
          false)
      nspc
  in
  match opt with
  | Some (_, ECons (c, i, j)) -> Some (c, i, j)
  | _ -> None

let find_data s nspc =
  let opt =
    List.find_opt
      (fun (k, entry) ->
        if s = k then
          match entry with
          | EData _ -> true
          | _ -> false
        else
          false)
      nspc
  in
  match opt with
  | Some (_, EData (d, i)) -> Some (d, i)
  | _ -> None

let trans_rel = function
  | R -> Syntax1.R
  | N -> Syntax1.N

let trans_role = function
  | Pos -> Syntax1.Pos
  | Neg -> Syntax1.Neg

let trans_prim = function
  | Stdin -> Syntax1.Stdin
  | Stdout -> Syntax1.Stdout
  | Stderr -> Syntax1.Stderr

let sspine_of_nspc nspc =
  List.fold_right
    (fun (_, entry) acc ->
      match entry with
      | ESVar x -> Syntax1._SVar x :: acc
      | _ -> acc)
    nspc []

let vspine_of_nspc nspc =
  List.fold_right
    (fun (_, entry) acc ->
      match entry with
      | EVar x -> Syntax1._Var x :: acc
      | _ -> acc)
    nspc []

let trans_sort nspc = function
  | U -> Syntax1._U
  | L -> Syntax1._L
  | SId "_" -> Syntax1.(_SMeta (M.mk ()) (box_list (sspine_of_nspc nspc)))
  | SId id -> (
    match find_svar id nspc with
    | Some sv -> Syntax1.(_SVar sv)
    | None -> failwith "trans01.trans_sort")

let mk_meta nspc =
  Syntax1.(
    _Meta (M.mk ())
      (box_list (sspine_of_nspc nspc))
      (box_list (vspine_of_nspc nspc)))

let mk_inst nspc i =
  let rec loop i =
    if i <= 0 then
      []
    else
      Syntax1.(_SMeta (M.mk ()) (box_list (sspine_of_nspc nspc))) :: loop (i - 1)
  in
  box_list (loop i)

let mk_param nspc i =
  let rec loop i =
    if i <= 0 then
      []
    else
      mk_meta nspc :: loop (i - 1)
  in
  box_list (loop i)

let rec trans_xs nspc = function
  | [] -> (nspc, [])
  | id :: ids ->
    let x = Syntax1.(V.mk id) in
    let nspc, xs = trans_xs ((id, EVar x) :: nspc) ids in
    (nspc, x :: xs)

let rec trans_tm nspc = function
  (* inference *)
  | Ann (m, a) ->
    let m, iset1 = trans_tm nspc m in
    let a, iset2 = trans_tm nspc a in
    Syntax1.(_Ann m a, ISet.union iset1 iset2)
  (* core *)
  | Type s -> Syntax1.(_Type (trans_sort nspc s), ISet.empty)
  | Id "_" -> (mk_meta nspc, ISet.empty)
  | Id id -> (
    match List.assoc_opt id nspc with
    | Some (EVar x) -> Syntax1.(_Var x, ISet.empty)
    | Some (EConst (x, i)) ->
      Syntax1.(_Const x (mk_inst nspc i), ISet.singleton x)
    | Some (EData (d, i)) ->
      Syntax1.(_Data d (mk_inst nspc i) (box []), ISet.empty)
    | Some (ECons (c, i, j)) ->
      Syntax1.(_Cons c (mk_inst nspc i) (mk_param nspc j) (box []), ISet.empty)
    | _ -> failwith "trans01.trans_tm.Id(%s)" id)
  | Inst (id, ss) -> (
    let ss = List.map (trans_sort nspc) ss in
    let ss = box_list ss in
    match List.assoc_opt id nspc with
    | Some (EConst (x, _)) -> Syntax1.(_Const x ss, ISet.singleton x)
    | Some (EData (d, _)) -> Syntax1.(_Data d ss (box []), ISet.empty)
    | Some (ECons (c, _, j)) ->
      Syntax1.(_Cons c ss (mk_param nspc j) (box []), ISet.empty)
    | _ -> failwith "trans01.trans_tm.Inst")
  | Pi (rel, s, a, Binder (id, b)) ->
    let a, iset1 = trans_tm nspc a in
    let x = Syntax1.(V.mk id) in
    let b, iset2 = trans_tm ((id, EVar x) :: nspc) b in
    Syntax1.
      ( _Pi (trans_rel rel) (trans_sort nspc s) a (bind_var x b)
      , ISet.union iset1 iset2 )
  | Lam (rel, s, a, Binder (id, m)) ->
    let a, iset1 = trans_tm nspc a in
    let x = Syntax1.(V.mk id) in
    let m, iset2 = trans_tm ((id, EVar x) :: nspc) m in
    Syntax1.
      ( _Lam (trans_rel rel) (trans_sort nspc s) a (bind_var x m)
      , ISet.union iset1 iset2 )
  | App ms -> (
    match ms with
    | Id id :: ms -> (
      let ms, iset =
        List.fold_right
          (fun m (ms, acc) ->
            let m, iset = trans_tm nspc m in
            (m :: ms, ISet.union iset acc))
          ms ([], ISet.empty)
      in
      match List.assoc_opt id nspc with
      | Some (EVar x) -> Syntax1.(_mkApps (_Var x) ms, iset)
      | Some (EConst (x, i)) ->
        Syntax1.(_mkApps (_Const x (mk_inst nspc i)) ms, ISet.add x iset)
      | Some (EData (d, i)) ->
        Syntax1.(_Data d (mk_inst nspc i) (box_list ms), iset)
      | Some (ECons (c, i, j)) ->
        Syntax1.(_Cons c (mk_inst nspc i) (mk_param nspc j) (box_list ms), iset)
      | _ -> failwith "trans01.trans_tm.App(%s)" id)
    | Inst (id, ss) :: ms -> (
      let ss = List.map (trans_sort nspc) ss in
      let ms, iset =
        List.fold_right
          (fun m (ms, acc) ->
            let m, iset = trans_tm nspc m in
            (m :: ms, ISet.union iset acc))
          ms ([], ISet.empty)
      in
      match List.assoc_opt id nspc with
      | Some (EConst (x, _)) ->
        Syntax1.(_mkApps (_Const x (box_list ss)) ms, ISet.add x iset)
      | Some (EData (d, _)) ->
        Syntax1.(_Data d (box_list ss) (box_list ms), iset)
      | Some (ECons (c, _, j)) ->
        Syntax1.(_Cons c (box_list ss) (mk_param nspc j) (box_list ms), iset)
      | _ -> failwith "trans01.trans_tm.Inst")
    | m :: ms ->
      let m, iset = trans_tm nspc m in
      let ms, iset =
        List.fold_right
          (fun m (ms, acc) ->
            let m, iset = trans_tm nspc m in
            (m :: ms, ISet.union iset acc))
          ms ([], iset)
      in
      Syntax1.(_mkApps m ms, iset)
    | _ -> failwith "trans01.trans_tm.App")
  | Let (rel, m, Binder (opt, n)) -> (
    match opt with
    | Left id ->
      let m, iset1 = trans_tm nspc m in
      let x = Syntax1.(V.mk id) in
      let n, iset2 = trans_tm ((id, EVar x) :: nspc) n in
      Syntax1.(_Let (trans_rel rel) m (bind_var x n), ISet.union iset1 iset2)
    | Right p ->
      let m, iset1 = trans_tm nspc m in
      let x = Syntax1.(V.mk "_") in
      let cl, iset2 = trans_cl nspc (Binder (p, n)) in
      let mot = bind_var x (mk_meta nspc) in
      let n = Syntax1.(_Match R (_Var x) mot (box_list [ cl ])) in
      (Syntax1.(_Let (trans_rel rel) m (bind_var x n)), ISet.union iset1 iset2))
  (* native *)
  | Unit s -> Syntax1.(_Unit (trans_sort nspc s), ISet.empty)
  | UIt s -> Syntax1.(_UIt (trans_sort nspc s), ISet.empty)
  | Bool -> Syntax1.(_Bool, ISet.empty)
  | BTrue -> Syntax1.(_BTrue, ISet.empty)
  | BFalse -> Syntax1.(_BFalse, ISet.empty)
  | Nat -> Syntax1.(_Nat, ISet.empty)
  | NZero -> Syntax1.(_NZero, ISet.empty)
  | NSucc (i, m) ->
    let m, iset = trans_tm nspc m in
    Syntax1.(_NSucc i m, iset)
  (* data *)
  | Sigma (rel1, rel2, s, a, Binder (id, b)) ->
    let a, iset1 = trans_tm nspc a in
    let x = Syntax1.(V.mk id) in
    let b, iset2 = trans_tm ((id, EVar x) :: nspc) b in
    Syntax1.
      ( _Sigma (trans_rel rel1) (trans_rel rel2) (trans_sort nspc s) a
          (bind_var x b)
      , ISet.union iset1 iset2 )
  | Pair (rel1, rel2, s, m, n) ->
    let m, iset1 = trans_tm nspc m in
    let n, iset2 = trans_tm nspc n in
    Syntax1.
      ( _Pair (trans_rel rel1) (trans_rel rel2) (trans_sort nspc s) m n
      , ISet.union iset1 iset2 )
  | Match (rel, m, Binder (id, a), cls) ->
    let m, iset1 = trans_tm nspc m in
    let x = Syntax1.(V.mk id) in
    let a, iset2 = trans_tm ((id, EVar x) :: nspc) a in
    let cls, iset3 =
      List.fold_right
        (fun cl (cls, acc) ->
          let cl, iset = trans_cl nspc cl in
          (cl :: cls, ISet.union iset acc))
        cls ([], ISet.empty)
    in
    Syntax1.
      ( _Match (trans_rel rel) m (bind_var x a) (box_list cls)
      , ISet.union (ISet.union iset1 iset2) iset3 )
  (* absurd *)
  | Bot -> Syntax1.(_Bot, ISet.empty)
  | Absurd m ->
    let m, iset = trans_tm nspc m in
    Syntax1.(_Absurd (mk_meta nspc) m, iset)
  (* equality *)
  | Eq (m, n) ->
    let m, iset1 = trans_tm nspc m in
    let n, iset2 = trans_tm nspc n in
    Syntax1.(_Eq (mk_meta nspc) m n, ISet.union iset1 iset2)
  | Refl -> Syntax1.(_Refl (mk_meta nspc), ISet.empty)
  | Rew (Binder ((id1, id2), a), pf, m) ->
    let pf, iset1 = trans_tm nspc pf in
    let m, iset2 = trans_tm nspc m in
    let nspc, xs = trans_xs nspc [ id1; id2 ] in
    let a, iset3 = trans_tm nspc a in
    let bnd = bind_mvar (Array.of_list xs) a in
    Syntax1.(_Rew bnd pf m, ISet.union (ISet.union iset1 iset2) iset3)
  (* monadic *)
  | IO a ->
    let a, iset = trans_tm nspc a in
    Syntax1.(_IO a, iset)
  | Return m ->
    let m, iset = trans_tm nspc m in
    Syntax1.(_Return m, iset)
  | MLet (m, Binder (opt, n)) -> (
    match opt with
    | Left id ->
      let m, iset1 = trans_tm nspc m in
      let x = Syntax1.(V.mk id) in
      let n, iset2 = trans_tm ((id, EVar x) :: nspc) n in
      Syntax1.(_MLet m (bind_var x n), ISet.union iset1 iset2)
    | Right p ->
      let m, iset1 = trans_tm nspc m in
      let x = Syntax1.(V.mk "_") in
      let cl, iset2 = trans_cl nspc (Binder (p, n)) in
      let mot = bind_var x (mk_meta nspc) in
      let n = Syntax1.(_Match R (_Var x) mot (box_list [ cl ])) in
      (Syntax1.(_MLet m (bind_var x n)), ISet.union iset1 iset2))
  (* session *)
  | Proto -> Syntax1.(_Proto, ISet.empty)
  | End -> Syntax1.(_End, ISet.empty)
  | Act (rel, rol, a, Binder (id, b)) ->
    let a, iset1 = trans_tm nspc a in
    let x = Syntax1.(V.mk id) in
    let b, iset2 = trans_tm ((id, EVar x) :: nspc) b in
    Syntax1.
      ( _Act (trans_rel rel) (trans_role rol) a (bind_var x b)
      , ISet.union iset1 iset2 )
  | Ch (rol, m) ->
    let m, iset = trans_tm nspc m in
    Syntax1.(_Ch (trans_role rol) m, iset)
  | Open prim -> Syntax1.(_Open (trans_prim prim), ISet.empty)
  | Fork (a, Binder (id, m)) ->
    let a, iset1 = trans_tm nspc a in
    let x = Syntax1.(V.mk id) in
    let m, iset2 = trans_tm ((id, EVar x) :: nspc) m in
    Syntax1.(_Fork a (bind_var x m), ISet.union iset1 iset2)
  | Recv m ->
    let m, iset = trans_tm nspc m in
    Syntax1.(_Recv m, iset)
  | Send m ->
    let m, iset = trans_tm nspc m in
    Syntax1.(_Send m, iset)
  | Close m ->
    let m, iset = trans_tm nspc m in
    Syntax1.(_Close m, iset)
  | Sleep m ->
    let m, iset = trans_tm nspc m in
    Syntax1.(_Sleep m, iset)
  | Rand (m, n) ->
    let m, iset1 = trans_tm nspc m in
    let n, iset2 = trans_tm nspc n in
    Syntax1.(_Rand m n, ISet.union iset1 iset2)

and trans_cl nspc = function
  | Binder (PIt s, m) ->
    let m, iset = trans_tm nspc m in
    Syntax1.(_PIt (trans_sort nspc s) m, iset)
  | Binder (PTrue, m) ->
    let m, iset = trans_tm nspc m in
    Syntax1.(_PTrue m, iset)
  | Binder (PFalse, m) ->
    let m, iset = trans_tm nspc m in
    Syntax1.(_PFalse m, iset)
  | Binder (PZero, m) ->
    let m, iset = trans_tm nspc m in
    Syntax1.(_PZero m, iset)
  | Binder (PSucc id, m) ->
    let x = Syntax1.(V.mk id) in
    let m, iset = trans_tm ((id, EVar x) :: nspc) m in
    let bnd = bind_var x m in
    Syntax1.(_PSucc bnd, iset)
  | Binder (PPair (rel1, rel2, s, id1, id2), m) ->
    let nspc, xs = trans_xs nspc [ id1; id2 ] in
    let m, iset = trans_tm nspc m in
    let bnd = bind_mvar (Array.of_list xs) m in
    Syntax1.
      (_PPair (trans_rel rel1) (trans_rel rel2) (trans_sort nspc s) bnd, iset)
  | Binder (PCons (id, ids), m) -> (
    match find_cons id nspc with
    | Some (c, _, _) ->
      let nspc, xs = trans_xs nspc ids in
      let m, iset = trans_tm nspc m in
      let bnd = bind_mvar (Array.of_list xs) m in
      Syntax1.(_PCons c bnd, iset)
    | _ -> failwith "trans01.trans_tm.Match")

let rec trans_param trans nspc = function
  | PBase a -> Syntax1.(_PBase (trans nspc a), 0)
  | PBind (a, Binder (id, b)) ->
    let a, _ = trans_tm nspc a in
    let x = Syntax1.(V.mk id) in
    let b, i = trans_param trans ((id, EVar x) :: nspc) b in
    Syntax1.(_PBind a (bind_var x b), i + 1)

let rec trans_tele nspc = function
  | TBase a -> Syntax1.(_TBase (fst (trans_tm nspc a)))
  | TBind (rel, a, Binder (id, b)) ->
    let a, _ = trans_tm nspc a in
    let x = Syntax1.(V.mk id) in
    let b = trans_tele ((id, EVar x) :: nspc) b in
    Syntax1.(_TBind (trans_rel rel) a (bind_var x b))

let rec trans_args nspc = function
  | ABase (b, m) ->
    let b, _ = trans_tm nspc b in
    let m, iset = trans_tm nspc m in
    (b, m, iset)
  | ABind (rel, a, Binder (id, args)) ->
    let x = Syntax1.(V.mk id) in
    let a, _ = trans_tm nspc a in
    let b, m, iset = trans_args ((id, EVar x) :: nspc) args in
    Syntax1.
      ( _Pi (trans_rel rel) _U a (bind_var x b)
      , _Lam (trans_rel rel) _U a (bind_var x m)
      , iset )

let trans_scheme nspc trans (Binder (ids, m)) =
  let nspc, xs, i =
    List.fold_left
      (fun (nspc, xs, i) id ->
        let x = Syntax1.(SV.mk id) in
        let nspc = (id, ESVar x) :: nspc in
        (nspc, x :: xs, i + 1))
      (nspc, [], 0) ids
  in
  let m, res = trans nspc i m in
  (bind_mvar (Array.of_list (List.rev xs)) m, res)

let trans_dcons nspc (DCons (id, sch)) =
  let c = C.mk id in
  let sch, (i, j) =
    trans_scheme nspc
      (fun nspc i ptl ->
        let ptl, j = trans_param trans_tele nspc ptl in
        (ptl, (i, j)))
      sch
  in
  ((id, ECons (c, i, j)) :: nspc, Syntax1.(_DCons c sch))

let rec trans_dconss nspc = function
  | [] -> (nspc, [])
  | dcons :: dconss ->
    let nspc, dcons = trans_dcons nspc dcons in
    let nspc, dconss = trans_dconss nspc dconss in
    (nspc, dcons :: dconss)

let rec trans_dcl nspc = function
  | DTm (rel, id, sch) ->
    let x = I.mk id in
    let sch, (i, iset) =
      trans_scheme nspc
        (fun nspc i args ->
          let nspc = (id, EConst (x, i)) :: nspc in
          let m, a, iset = trans_args nspc args in
          (box_pair m a, (i, iset)))
        sch
    in
    let nspc = (id, EConst (x, i)) :: nspc in
    let guard = ISet.mem x iset in
    (nspc, Syntax1.(_DTm (trans_rel rel) x guard sch))
  | DData (rel, id, sch, dconss) ->
    let d = D.mk id in
    let sch, i =
      trans_scheme nspc
        (fun nspc i ptm ->
          let ptm, _ =
            trans_param (fun nspc m -> fst (trans_tm nspc m)) nspc ptm
          in
          (ptm, i))
        sch
    in
    let nspc = (id, EData (d, i)) :: nspc in
    let nspc, dconss = trans_dconss nspc dconss in
    (nspc, Syntax1._DData (trans_rel rel) d sch (box_list dconss))

let trans_dcls nspc dcls =
  let rec aux nspc dcls =
    match dcls with
    | [] -> (nspc, [])
    | dcl :: dcls ->
      let nspc, dcl = trans_dcl nspc dcl in
      let nspc, dcls = aux nspc dcls in
      (nspc, dcl :: dcls)
  in
  let nspc, dcls = aux nspc dcls in
  (nspc, unbox (box_list dcls))
