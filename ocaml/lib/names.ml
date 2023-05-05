open Fmt

(* meta variables *)
module M : sig
  type t

  val mk : unit -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
  val to_string : t -> string
end = struct
  type t = int

  let stamp = ref 0

  let mk () =
    incr stamp;
    !stamp

  let equal x y = x = y
  let compare x y = Int.compare x y
  let pp fmt id = pf fmt "??%d" id
  let to_string x = to_to_string pp x
end

(* constant identifiers *)
module I : sig
  type t

  val mk : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val extend : t -> string -> t
  val pp : Format.formatter -> t -> unit
  val to_string : t -> string
  val is_main : t -> bool
end = struct
  type t = string * int

  let stamp = ref 0

  let mk s =
    incr stamp;
    (s, !stamp)

  let equal x y = snd x = snd y
  let compare x y = Int.compare (snd x) (snd y)

  let extend (s0, _) s1 =
    incr stamp;
    (s0 ^ s1, !stamp)

  let pp fmt (s, id) = pf fmt "%s_i%d" s id
  let to_string x = to_to_string pp x
  let is_main (s, _) = s = "main"
end

(* data identifiers *)
module D : sig
  type t

  val mk : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val extend : t -> string -> t
  val pp : Format.formatter -> t -> unit
  val to_string : t -> string
end = struct
  type t = string * int

  let stamp = ref 0

  let mk s =
    incr stamp;
    (s, !stamp)

  let equal x y = snd x = snd y
  let compare x y = Int.compare (snd x) (snd y)

  let extend (s0, _) s1 =
    incr stamp;
    (s0 ^ s1, !stamp)

  let pp fmt (s, id) = pf fmt "%s_d%d" s id
  let to_string x = to_to_string pp x
end

(* constructor identifiers *)
module C : sig
  type t

  val mk : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val get_id : t -> int
  val get_name : t -> string
  val extend : t -> string -> t
  val pp : Format.formatter -> t -> unit
  val to_string : t -> string
end = struct
  type t = string * int

  let stamp = ref 0

  let mk s =
    incr stamp;
    (s, !stamp)

  let equal x y = snd x = snd y
  let compare x y = Int.compare (snd x) (snd y)
  let get_id (_, id) = id
  let get_name (s, _) = s

  let extend (s0, _) s1 =
    incr stamp;
    (s0 ^ s1, !stamp)

  let pp fmt (s, id) = pf fmt "%s_c%d" s id
  let to_string x = to_to_string pp x
end

(* sets *)
module SSet = Set.Make (String)
module MSet = Set.Make (M)
module ISet = Set.Make (I)
module CSet = Set.Make (C)
module DSet = Set.Make (D)

(* maps *)
module SMap = Map.Make (String)
module MMap = Map.Make (M)
module IMap = Map.Make (I)
module CMap = Map.Make (C)
module DMap = Map.Make (D)
