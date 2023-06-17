open Fmt
open Names
open Syntax4

let resolve_c c res = Trans12.Resolver.find_cons c [] res

let pp_prelude fmt res =
  let pp_define fmt c0 =
    let c1 = resolve_c c0 res in
    pf fmt "#define %s_c %d" (C.get_name c1) (C.get_id c1)
  in
  pf fmt "#ifndef prelude_h@.#define prelude_h@.@.@[<v 0>%a@]@.@.#endif"
    (list ~sep:sp pp_define)
    Prelude1.[ char_c; emptyString_c; string_c; between_c ]

let rec pp_value fmt = function
  | Int i -> pf fmt "(tll_ptr)%d" i
  | Reg x -> pf fmt "%s" x
  | Env i -> pf fmt "env[%d]" i
  | Idx (v, i) -> pf fmt "((tll_node)%a)->data[%d]" pp_value v i
  | NULL -> pf fmt "0"

let rec pp_values fmt vs = pf fmt "@[%a@]" (list ~sep:comma pp_value) vs

let rec gather_var ctx instrs =
  match instrs with
  | [] -> ctx
  | Init _ :: instrs -> gather_var ctx instrs
  | Mov instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Add instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | LteN instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | GteN instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | LtN instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | GtN instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | EqN instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | AddN instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | SubN instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | MulN instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | DivN instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | ModN instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Clo instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Call instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | App instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Struct instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Ifte instr :: instrs ->
    let ctx = gather_var ctx instr.tcase in
    let ctx = gather_var ctx instr.fcase in
    gather_var ctx instrs
  | Switch instr :: instrs ->
    let ctx =
      List.fold_left
        (fun ctx (_, intrs) -> gather_var ctx intrs)
        ctx instr.cases
    in
    gather_var ctx instrs
  | Break :: instrs -> gather_var ctx instrs
  | Open instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Fork instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Recv instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Send instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Close instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Sleep instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Rand instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | FreeClo _ :: instrs -> gather_var ctx instrs
  | FreeStruct _ :: instrs -> gather_var ctx instrs
  | FreeThread :: instrs -> gather_var ctx instrs

let rec gather_init ctx instrs =
  match instrs with
  | [] -> ctx
  | Init instr :: instrs -> gather_init (SSet.add instr.lhs ctx) instrs
  | _ :: instrs -> gather_init ctx instrs

let pp_xs fmt ctx =
  let xs = SSet.elements ctx in
  let rec aux fmt = function
    | [] -> ()
    | [ x ] -> pf fmt "tll_ptr %s;" x
    | x :: xs -> pf fmt "tll_ptr %s;@;<1 0>%a" x aux xs
  in
  aux fmt xs

let rec pp_proc fmt = function
  | GFun { fname; param; body; return } ->
    let xs = gather_var SSet.empty body in
    let rec pp_param fmt = function
      | [] -> ()
      | [ x ] -> pf fmt "tll_ptr %s" x
      | x :: xs -> pf fmt "tll_ptr %s, %a" x pp_param xs
    in
    pf fmt
      "@[<v 0>tll_ptr %s(%a) {@;\
       <1 2>@[<v 0>@[%a@]@;\
       <1 0>%a@;\
       <1 0>return %a@];@;\
       <1 0>}@]" fname pp_param param pp_xs xs pp_instrs body pp_value return
  | LFun { fname; param; body; return } ->
    let xs = gather_var SSet.empty body in
    let pp_param fmt opt =
      match opt with
      | None -> ()
      | Some x -> pf fmt "tll_ptr %s, " x
    in
    pf fmt
      "@[<v 0>tll_ptr %s(%atll_env env) {@;\
       <1 2>@[<v 0>@[%a@]@;\
       <1 0>%a@;\
       <1 0>return %a@];@;\
       <1 0>}@]" fname pp_param param pp_xs xs pp_instrs body pp_value return

and pp_procs fmt = function
  | [] -> ()
  | [ proc ] -> pp_proc fmt proc
  | proc :: procs -> pf fmt "@[<v 0>%a@]@.@.%a" pp_proc proc pp_procs procs

and pp_instr fmt = function
  | Init { lhs; rhs } -> pf fmt "%s = %a;" lhs pp_value rhs
  | Mov { lhs; rhs } -> pf fmt "%s = %a;" lhs pp_value rhs
  | Add { lhs; i; rhs } ->
    if 0 <= i then
      pf fmt "%s = (tll_ptr)((long)%a + %d);" lhs pp_value rhs (abs i)
    else
      pf fmt "%s = (tll_ptr)((long)%a - %d);" lhs pp_value rhs (abs i)
  | LteN { lhs; x; y } ->
    pf fmt "instr_lten(&%s, %a, %a);" lhs pp_value x pp_value y
  | GteN { lhs; x; y } ->
    pf fmt "instr_gten(&%s, %a, %a);" lhs pp_value x pp_value y
  | LtN { lhs; x; y } ->
    pf fmt "instr_ltn(&%s, %a, %a);" lhs pp_value x pp_value y
  | GtN { lhs; x; y } ->
    pf fmt "instr_gtn(&%s, %a, %a);" lhs pp_value x pp_value y
  | EqN { lhs; x; y } ->
    pf fmt "instr_eqn(&%s, %a, %a);" lhs pp_value x pp_value y
  | AddN { lhs; x; y } ->
    pf fmt "instr_addn(&%s, %a, %a);" lhs pp_value x pp_value y
  | SubN { lhs; x; y } ->
    pf fmt "instr_subn(&%s, %a, %a);" lhs pp_value x pp_value y
  | MulN { lhs; x; y } ->
    pf fmt "instr_muln(&%s, %a, %a);" lhs pp_value x pp_value y
  | DivN { lhs; x; y } ->
    pf fmt "instr_divn(&%s, %a, %a);" lhs pp_value x pp_value y
  | ModN { lhs; x; y } ->
    pf fmt "instr_modn(&%s, %a, %a);" lhs pp_value x pp_value y
  | Clo { lhs; fname; env = [] } ->
    pf fmt "instr_clo(&%s, &%s, %d);" lhs fname 0
  | Clo { lhs; fname; env } ->
    pf fmt "instr_clo(@[&%s, &%s, %d,@;<1 0>@[%a@]@]);" lhs fname
      (List.length env) pp_values env
  | Call { lhs; fname; aptrs } ->
    pf fmt "%s = %s(%a);" lhs fname pp_values aptrs
  | App { lhs; fptr; aptr } ->
    pf fmt "instr_app(&%s, %a, %a);" lhs pp_value fptr pp_value aptr
  | Struct { lhs; ctag; size; data = [] } ->
    pf fmt "instr_struct(&%s, %d, %d);" lhs ctag 0
  | Struct { lhs; ctag; size; data } ->
    pf fmt "instr_struct(@[&%s, %d, %d,@;<1 0>@[%a@]@]);" lhs ctag
      (List.length data) pp_values data
  | Ifte { cond; tcase; fcase } ->
    pf fmt
      "@[<v 0>if (%a) {@;\
       <1 2>@[%a@]@;\
       <1 0>}@;\
       <1 0>else {@;\
       <1 2>@[%a@]@;\
       <1 0>}@]" pp_value cond pp_instrs tcase pp_instrs fcase
  | Switch { cond; cases } ->
    pf fmt "@[<v 0>switch(((tll_node)%a)->tag) {@;<1 2>@[%a@]@;<1 0>}@]"
      pp_value cond pp_cases cases
  | Break -> pf fmt "break;"
  | Open { lhs; mode } -> (
    match mode with
    | Stdout -> pf fmt "instr_open(&%s, &proc_stdout);" lhs
    | Stdin -> pf fmt "instr_open(&%s, &proc_stdin);" lhs
    | Stderr -> pf fmt "instr_open(&%s, &proc_stderr);" lhs)
  | Fork { lhs; fname; env = [] } ->
    pf fmt "instr_fork(&%s, &%s, %d);" lhs fname 0
  | Fork { lhs; fname; env } ->
    pf fmt "instr_fork(&%s, &%s, %d, %a);" lhs fname (List.length env) pp_values
      env
  | Send { lhs; ch; msg } ->
    pf fmt "instr_send(&%s, %a, %a);" lhs pp_value ch pp_value msg
  | Recv { lhs; ch } -> pf fmt "instr_recv(&%s, %a);" lhs pp_value ch
  | Close { lhs; ch } -> pf fmt "instr_close(&%s, %a);" lhs pp_value ch
  | Sleep { lhs; rhs } -> pf fmt "instr_sleep(&%s, %a);" lhs pp_value rhs
  | Rand { lhs; v1; v2 } ->
    pf fmt "instr_rand(&%s, %a, %a);" lhs pp_value v1 pp_value v2
  | FreeClo v -> pf fmt "instr_free_clo(%a);" pp_value v
  | FreeStruct v -> pf fmt "instr_free_struct(%a);" pp_value v
  | FreeThread -> pf fmt "instr_free_thread(env);"

and pp_instrs fmt instrs =
  let rec aux fmt instrs =
    match instrs with
    | [] -> ()
    | [ instr ] -> pp_instr fmt instr
    | instr :: instrs -> pf fmt "%a@;<1 0>%a" pp_instr instr pp_instrs instrs
  in
  pf fmt "@[<v 0>%a@]" aux instrs

and pp_case fmt (i, instr) =
  pf fmt "@[<v 0>case %d:@;<1 2>%a@]" i pp_instrs instr

and pp_cases fmt cases =
  match cases with
  | [] -> ()
  | [ case ] -> pp_case fmt case
  | case :: cases -> pf fmt "%a@;<1 0>%a" pp_case case pp_cases cases

let rec pp_dcls fmt dcls =
  let rec pp_param fmt = function
    | [] -> ()
    | [ x ] -> pf fmt "tll_ptr %s" x
    | x :: xs -> pf fmt "tll_ptr %s, %a" x pp_param xs
  in
  match dcls with
  | [] -> ()
  | [ GFun { fname; param; body; return } ] ->
    pf fmt "tll_ptr %s(%a);" fname pp_param param
  | GFun { fname; param; body; return } :: dcls ->
    pf fmt "tll_ptr %s(%a);@;<1 0>%a" fname pp_param param pp_dcls dcls
  | _ :: dcls -> pp_dcls fmt dcls

let pp_prog fmt (procs, instr, _) =
  let xs = gather_init SSet.empty instr in
  let ys = gather_var SSet.empty instr in
  pf fmt
    "#include \"runtime.h\"@.@.@[<v 0>%a@;\
     <1 0>%a@]@.@.%a@.@.@[<v 0>int main() {@;\
     <1 2>@[<v 0>instr_init();@;\
     <1 0>@[%a@]@;\
     <1 0>%a@;\
     <1 0>instr_exit();@]@;\
     <1 0>}@]" pp_dcls procs pp_xs xs pp_procs procs pp_xs ys pp_instrs instr
