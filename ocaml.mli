
(* 
 * OCaml hacks to support reflection (work with ocamltarzan).
 *
 * See also sexp.ml and json.ml for other "reflective" techniques.
 *)

(* OCaml type definitions (the core part of OCaml, no objects, no modules) *)
type t =
  | Unit | Bool | Float | Char | String
  | Int

  | Tuple of t list
  | Dict of (string * [`RW|`RO] * t) list (* aka record *)
  | Sum of (string * t list) list         (* aka variants *)

  | Var of string
  | Poly of string
  | Arrow of t * t

  | Apply of string * t

  (* special cases of Apply *) 
  | Option of t
  | List of t 

  | TTODO of string

val add_new_type: string -> t -> unit
val get_type: string -> t

(* OCaml values (a restricted form of expressions) *)
type v = 
  | VUnit | VBool of bool | VFloat of float | VChar of char | VString of string
  | VInt of int64

  | VTuple of v list
  | VDict of (string * v) list
  | VSum of string * v list

  | VVar of (string * int64)
  | VArrow of string

  (* special cases *) 
  | VNone | VSome of v
  | VList of v list

  | VTODO of string

(* building blocks, used by code generated using ocamltarzan *)
val vof_unit   : unit -> v
val vof_int    : int -> v
val vof_string : string -> v
val vof_list   : ('a -> v) -> 'a list -> v
val vof_option : ('a -> v) -> 'a option -> v
val vof_ref    : ('a -> v) -> 'a ref -> v

(* sexp converters *)
val string_of_t: t -> string
val t_of_string: string -> t

val string_of_v: v -> string
val v_of_string: string -> v

(* TODO visitors *)

(* TODO regular pretty printer (not via sexp) *)
