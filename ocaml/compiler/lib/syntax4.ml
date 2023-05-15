type prim =
  | Stdin
  | Stdout
  | Stderr
[@@deriving show { with_path = false }]

type value =
  | Int of int
  | Reg of string
  | Env of int
  | Idx of value * int
  | NULL
[@@deriving show { with_path = false }]

and values = value list

and proc =
  | GFun of
      { fname : string
      ; param : string list
      ; body : instrs
      ; return : value
      }
  | LFun of
      { fname : string
      ; param : string option
      ; body : instrs
      ; return : value
      }

and procs = proc list

and instr =
  | Init of
      { lhs : string
      ; rhs : value
      }
  | Mov of
      { lhs : string
      ; rhs : value
      }
  | Add of
      { lhs : string
      ; i : int
      ; rhs : value
      }
  | LteN of
      { lhs : string
      ; x : value
      ; y : value
      }
  | GteN of
      { lhs : string
      ; x : value
      ; y : value
      }
  | LtN of
      { lhs : string
      ; x : value
      ; y : value
      }
  | GtN of
      { lhs : string
      ; x : value
      ; y : value
      }
  | EqN of
      { lhs : string
      ; x : value
      ; y : value
      }
  | AddN of
      { lhs : string
      ; x : value
      ; y : value
      }
  | SubN of
      { lhs : string
      ; x : value
      ; y : value
      }
  | MulN of
      { lhs : string
      ; x : value
      ; y : value
      }
  | DivN of
      { lhs : string
      ; x : value
      ; y : value
      }
  | ModN of
      { lhs : string
      ; x : value
      ; y : value
      }
  | Clo of
      { lhs : string
      ; fname : string
      ; env : values
      }
  | Call of
      { lhs : string
      ; fname : string
      ; aptrs : values
      }
  | App of
      { lhs : string
      ; fptr : value
      ; aptr : value
      }
  | Struct of
      { lhs : string
      ; ctag : int
      ; size : int
      ; data : values
      }
  | Ifte of
      { cond : value
      ; tcase : instrs
      ; fcase : instrs
      }
  | Switch of
      { cond : value
      ; cases : cls
      }
  | Break
  | Open of
      { lhs : string
      ; mode : prim
      }
  | Fork of
      { lhs : string
      ; fname : string
      ; env : values
      }
  | Recv of
      { lhs : string
      ; ch : value
      }
  | Send of
      { lhs : string
      ; ch : value
      ; msg : value
      }
  | Close of
      { lhs : string
      ; ch : value
      }
  | Sleep of
      { lhs : string
      ; rhs : value
      }
  | Rand of
      { lhs : string
      ; v1 : value
      ; v2 : value
      }
  | FreeClo of value
  | FreeStruct of value
  | FreeThread

and instrs = instr list
and cl = int * instrs
and cls = cl list
