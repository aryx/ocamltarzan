(*
  Conversion between OCaml types and JSON types as provided by the json-wheel
  library. 
  
  Author: Martin Jambon <martin_jambon@emailuser.net>

Copyright (c) 2007 Burnham Institute for Medical Research
Copyright (c) 2008 Martin Jambon
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions
are met:
1. Redistributions of source code must retain the above copyright
   notice, this list of conditions and the following disclaimer.
2. Redistributions in binary form must reproduce the above copyright
   notice, this list of conditions and the following disclaimer in the
   documentation and/or other materials provided with the distribution.
3. The name of the author may not be used to endorse or promote products
   derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(* This version was tested successfully with camlp4 3.10.0+beta.

   The upgrade from 3.09 to 3.10+beta was performed with the help 
   of Nicolas Pouillard.

   Command that compiles this program:

     ocamlc -c -pp camlp4orf -I +camlp4 \
        pa_json_static_3100beta.ml

   Before 3.10, it used to be: 
     ocamlc -c -pp 'camlp4o q_MLast.cmo pa_extend.cmo' -I +camlp4 \
        pa_json_static.ml


   Command that works for using this syntax extension when it is present
   in the current directory (not installed, no ocamlfind). It preprocesses
   a file that uses the json-static syntax and pretty-prints it to
   standard OCaml syntax:

     camlp4o -parser ./pa_json_static_3100beta.cmo -printer o example.ml

   Before 3.10, it used to be:
     camlp4o ./pa_json_static.cmo pr_o.cmo example.ml


   It passes the "make test" stage of the json-static package!
*)

open Camlp4.PreCast
open Printf

let check_unique f l =
  let tbl = Hashtbl.create 50 in
  List.iter
    (fun x -> 
       let (_loc, id) = f x in
       if Hashtbl.mem tbl id then
	 Loc.raise _loc
	   (Failure "this tag or label is not unique")
       else Hashtbl.add tbl id ())
    l

let unopt default = function
    None -> default
  | Some x -> x

let rec optmap f = function
    [] -> []
  | hd :: tl ->
      match f hd with
	  None -> optmap f tl
	| Some x -> x :: optmap f tl
    

type field = { field_caml_name : string;
	       field_json_name : string;
	       field_type : t;
	       field_caml_loc : Loc.t;
	       field_json_loc : Loc.t;
	       optional : bool;
	       default : Ast.expr option;
	       is_mutable : bool }

and constructor = { cons_caml_name : string;
		    cons_json_name : string;
		    cons_args : t list;
		    cons_caml_loc : Loc.t;
		    cons_json_loc : Loc.t }

and type_expr =
    List of t
  | Array of t
  | Option of t
  | Object of field list
  | Record of field list
  | Hashtbl of t
  | Assoc of t
  | Tuple of t list
  | Variant of constructor list
  | Poly of constructor list
  | Name of string
  | String
  | Bool
  | Int
  | Float
  | Number
  | Raw
  | Custom of string

and t = Loc.t * type_expr

and type_def = { def : t;
		 is_predefined : bool;
		 is_private : bool (* unused at the moment *) }

module StringMap = Map.Make (String)

let make_typedef _loc names l =
  let rec convert (_loc, def) =
    match def with
	List x -> <:ctyp< list $convert x$ >>
      | Array x -> <:ctyp< array $convert x$ >>
      | Option x -> <:ctyp< option $convert x$ >>
      | Object l -> 
	  (* (* Development version post-3.10.0+beta *)
          let ml = 
	    List.fold_right 
	      (fun x acc ->
		 <:ctyp< $lid:x.field_caml_name$ : $convert x.field_type$ ; 
                         $acc$ >>)
	      l <:ctyp<>> in
          <:ctyp< < $ml$ > >> in
	  *)

	  let ml = 
	    List.fold_right
	      (fun x acc ->
		 let field = 
		   <:ctyp< $lid:x.field_caml_name$ : 
		              $convert x.field_type$ >> in
		 <:ctyp< $field$ ; $acc$ >>)
            l <:ctyp<>> in
	  <:ctyp< < $ml$ > >>
      | Record r -> 
	  let l = 
	    List.fold_right begin fun x acc ->
              let _loc = x.field_caml_loc in
              let t = convert x.field_type in
              let t = if x.is_mutable then <:ctyp< mutable $t$ >> else t in
	      (* (* Development version post-3.10.0+beta: *)
		 <:ctyp< $lid:x.field_caml_name$ : $t$; $acc$ >> *)
	      let field = <:ctyp< $lid:x.field_caml_name$ : $t$ >> in
              <:ctyp< $field$; $acc$ >>
            end r <:ctyp<>> in
	  <:ctyp< { $l$ } >>
      | Hashtbl x -> <:ctyp< Hashtbl.t string $convert x$ >>
      | Assoc x -> <:ctyp< list (string * $convert x$) >>
      | Tuple l -> 
	  (* (* Development version post-3.10.0+beta: *)
	     let tl = List.map convert l in
	     <:ctyp< ( $tup:Ast.tySta_of_list tl$ ) >> *)
	  let t =
	    List.fold_right 
	      (fun x tup -> <:ctyp< $convert x$ * $tup$ >>)
	      l <:ctyp< >> in
	  <:ctyp< ( $tup:t$ ) >>
      | Poly l -> 
	  let rfl = 
	    List.fold_right (fun c acc ->
			let name = c.cons_caml_name in
			match c.cons_args with
			    [] -> <:ctyp< `$name$ | $acc$ >>
			  | [x] -> 
			      (* (* Development version post-3.10.0+beta: *)
				 <:ctyp< `$name$ of $convert x$ | $acc$ >> *)
			      let case = <:ctyp< `$name$ of $convert x$ >> in
			      <:ctyp< $case$ | $acc$ >>
			  | _ -> assert false)
	      l <:ctyp<>> in
	  <:ctyp< [ = $rfl$ ] >>
      | Variant v -> 
	  let l = 
	    List.fold_right
	      (fun x acc ->
		 let cal = List.map convert x.cons_args in
                 let _loc = x.cons_caml_loc in
		 (* (* Development version post-3.10.0+beta: *)
		    <:ctyp< $uid:x.cons_caml_name$ of $list:cal$ | $acc$ >> *)
		 let case = <:ctyp< $uid:x.cons_caml_name$ of $list:cal$ >> in
		 <:ctyp< $case$ | $acc$ >>)
	      v <:ctyp<>> in
	  <:ctyp< [ $l$ ] >>
      | Name x -> 
	  if StringMap.mem x names then <:ctyp< $lid:x$ >>
	  else
	    Loc.raise _loc 
	      (Failure ("type name " ^ x ^ 
			" is undefined or not defined in the same \
                         'type ... and ...' block"))
      | String -> <:ctyp< string >>
      | Bool -> <:ctyp< bool >>
      | Int -> <:ctyp< int >>
      | Float -> <:ctyp< float >>
      | Number -> <:ctyp< float >>
      | Raw -> <:ctyp< Json_type.t >>
      | Custom s -> <:ctyp< $uid:s$ . t >> in

  let l = List.filter (fun (_, x) -> not x.is_predefined) l in
  match l with
      [] -> <:str_item< >>
    | ((_loc, name), x) :: l ->

	let tdl =
	  let dcl = Ast.TyDcl (_loc, name, [], convert x.def, []) in
	  List.fold_right (
	    fun ((_loc, name), x) acc ->
	      let dcl = Ast.TyDcl (_loc, name, [], convert x.def, []) in
	      <:ctyp< $dcl$ and $acc$ >>
          ) l dcl in
	<:str_item< type $tdl$ >>


let numbered_list l =
  Array.to_list
    (Array.mapi 
       (fun i x -> (x, "x" ^ string_of_int i))
       (Array.of_list l))

let eta_expand = function
    <:expr< fun [ $_$ ] >> as f -> f
  | e -> let _loc = Ast.loc_of_expr e in <:expr< fun x -> $e$ x >>

let make_ofjson _loc l =
  let browse _loc f = <:expr< Json_type.Browse.$lid:f$ >> in

  let rec convert (_loc, def) =
    match def with
	List x -> <:expr< $browse _loc "list"$ $convert x$ >>
      | Array x -> 
	  <:expr< fun x -> 
	    Array.of_list (($browse _loc "list"$ $convert x$) x) >>
      | Option x -> 
	  <:expr< $browse _loc "optional"$ $convert x$ >>
      | Object l -> convert_object _loc l
      | Record r -> convert_record _loc r
      | Hashtbl x -> 
	  <:expr< 
	     fun x -> 
	       let l = $browse _loc "objekt"$ x in
	       let tbl = Hashtbl.create (List.length l) in
               do { List.iter (fun (s, x) -> 
				 Hashtbl.add tbl s ($convert x$ x)) l;
		    tbl } >>
      | Assoc x -> 
	  <:expr< fun x ->
	            List.map (fun (key, data) -> (key, $convert x$ data))
	              ($browse _loc "objekt"$ x) >>
      | Tuple l ->
	  let nl = numbered_list l in
	  let pl = 
	    List.fold_right 
	      (fun ((_loc, _), name) tl -> <:patt< [ $lid:name$ :: $tl$ ] >>) 
	      nl <:patt< [] >> in
	  let el = 
	    List.fold_right (fun ((_loc, _) as x, name) acc ->
			<:expr< $convert x$ $lid:name$, $acc$ >>)
	      nl <:expr<>> in
	  <:expr< fun [ Json_type.Array $pl$ -> ( $tup:el$ )
		      | Json_type.Array _ as x ->
			  __json_static_error x
			    "wrong number of elements in JSON array"
		      | x ->
			  __json_static_error x
			    "not a JSON array" ] >>
      | Poly l ->
	  convert_variants (fun _loc name -> <:expr< ` $name$ >>) _loc l
      | Variant l ->
	  convert_variants (fun _loc name -> <:expr< $uid:name$ >>) _loc l
      | Name x -> <:expr< $lid: x ^ "_of_json"$ >>
      | String -> browse _loc "string"
      | Bool -> browse _loc "bool"
      | Int -> browse _loc "int"
      | Float -> browse _loc "float"
      | Number -> browse _loc "number"
      | Raw -> <:expr< fun x -> x >>
      | Custom modul -> <:expr< $uid:modul$ . of_json >>

   and convert_object _loc l =
     let pel = convert_object_field_list _loc l in
     let methods = 
       List.fold_right
	 (fun x acc ->
	    let name = x.field_caml_name in
            <:class_str_item< method $name$ = $lid:name$ ; $acc$ >>)
	 l <:class_str_item<>> in
     eval_with_tbl _loc <:expr< let $list:pel$ in object $methods$ end >>

  and convert_record _loc r =
     let pel = convert_record_field_list _loc r in
     eval_with_tbl _loc <:expr< { $list:pel$ } >>

  and convert_field_list _loc l =
     List.map 
       (fun { field_caml_name = name;
	      field_json_name = json_name;
	      field_type = x;
	      optional = optional;
	      default = default } ->
	  let e1 = 
	    let f = if optional then "fieldx" else "field" in
	    <:expr< Json_type.Browse.$lid:f$ tbl $str:json_name$ >> in
	  let e2 =
	    match default with
		Some e -> 
		  (<:expr< 
		   match $e1$ with 
		       [ Json_type.Null -> $e$
		       | x -> $convert x$ x ] >>)
	      | None -> <:expr< $convert x$ $e1$ >> in

	  (name, e2))
       l

  and convert_record_field_list _loc l = 
    List.map (fun (name, e) -> <:rec_binding< $lid:name$ = $e$ >>)
      (convert_field_list _loc l)

  and convert_object_field_list _loc l =
    List.map (fun (name, e) -> <:binding< $lid:name$ = $e$ >>)
      (convert_field_list _loc l)

  and convert_variants make_cons _loc l =
    let l0, l1 =
      List.partition (fun x -> x.cons_args = []) l in
    let pwel0 =
      List.fold_right
	(fun { cons_caml_name = name;
	       cons_json_name = json_name } acc ->
	   <:match_case< $str:json_name$ -> $make_cons _loc name$ | $acc$ >>)
	l0 <:match_case<>> in
    let pwel1 =
      List.fold_right
	(fun { cons_caml_name = name;
	       cons_json_name = json_name;
	       cons_args = args } acc ->
	   let argnames = numbered_list args in
	   let list_patt =
	     List.fold_right 
	       (fun (_, s) l -> 
		  <:patt< [ $lid:s$ :: $l$ ] >>)
	       argnames <:patt< [] >> in
	   let e =
	     List.fold_left
	       (fun cons (arg, s) -> 
		  <:expr< $cons$ ($convert arg$ $lid:s$) >>)
	     (make_cons _loc name) argnames in
	   <:match_case< ($str:json_name$, $list_patt$) -> $e$ | $acc$ >>)
	l1 <:match_case<>> in
    let default_case =
      <:match_case< _ -> __json_static_error x
                           "invalid variant name or \
                            wrong number of arguments" >>
    in
    
    (<:expr< 
     fun
	 [ Json_type.String s as x -> 
	     match s with [ $pwel0$ | $default_case$ ]
	       | Json_type.Array 
		   [ Json_type.String s :: ([ _ :: _ ] as args) ] as x -> 
		   match (s, args) with [ $pwel1$ | $default_case$ ]
	       | x -> __json_static_error x
		   "not able to read this as \
                    a variant" ]
     >>)


  and eval_with_tbl _loc e =
    (<:expr< 
     fun x ->
       let tbl = 
	 Json_type.Browse.make_table (Json_type.Browse.objekt x) in
       $e$ >>)
  in

  let error =
    <:str_item< 
    value __json_static_error obj msg =
      let m = 400 in
      let s = Json_io.string_of_json obj in
      let obj_string =
	if String.length s > m then String.sub s 0 (m - 4) ^ " ..."
	else s in
      Json_type.json_error (msg ^ ":\n" ^ obj_string) >> in

  let defs = 
    List.fold_right
      (fun ((_loc, name), x) acc -> 
	 (*if x.is_private then acc
	 else*)
	   let fname = name ^ "_of_json" in
           <:binding< ( $lid:fname$ : Json_type.t -> $lid:name$ ) = 
                      $eta_expand (convert x.def)$ and $acc$ >>)
      l <:binding<>>
  in
    <:str_item< $error$; value rec $defs$ >>

let make_tojson _loc l =
  let build _loc s = <:expr< Json_type.Build. $lid:s$ >> in

  let rec convert (_loc, def) =
    match def with
	List x -> <:expr< Json_type.Build.list $convert x$ >>
      | Array x -> 
	  <:expr< fun x -> 
                    Json_type.Build.list $convert x$ (Array.to_list x) >>
      | Option x -> <:expr< Json_type.Build.optional $convert x$ >>
      | Object l ->
	  convert_field_list (fun name -> <:expr< x#$lid:name$ >>) 
	    _loc l
      | Record r -> 
	  convert_field_list (fun name -> <:expr< x.$lid:name$ >>)
	    _loc r
      | Hashtbl x ->
	  <:expr< fun tbl -> 
	    Json_type.Object 
	      (Hashtbl.fold (fun key data tl -> 
			       [ (key, $convert x$ data) :: tl ])
		 tbl []) >>
      | Assoc x ->
	  <:expr< 
	    fun x ->
	      Json_type.Object
	        ((List.map (fun (key, data) -> (key, $convert x$ data))) x) >>
      | Tuple l ->
	  let nl = numbered_list l in
	  let pl = List.fold_right 
                    (fun (_, name) acc -> <:patt< $lid:name$, $acc$ >>)
                    nl <:patt<>> in
	  let a = List.fold_right 
		    (fun (x, name) tl -> 
		       <:expr< [ $convert x$ $lid:name$ :: $tl$ ] >>)
		    nl <:expr< [] >> in
	  <:expr< fun [ ( $tup:pl$ ) -> Json_type.Array $a$ ] >>
      | Poly l -> 
	  let match_cases =
	    List.map
	      (fun { cons_caml_name = name;
		     cons_json_name = json_name;
		     cons_args = args } ->
		 match args with
		     [] -> 
		       <:match_case< 
		          `$name$ -> Json_type.String $str:json_name$ >>
		   | [x] ->
		       <:match_case< 
		          `$name$ arg ->
		              Json_type.Array 
		                [ Json_type.String $str:json_name$;
			          $convert x$ arg ] >>
		   | _ -> assert false)
	      l in
	  <:expr< fun [ $list:match_cases$ ] >>
      | Variant v -> 
	  let match_cases =
	    List.map
	      (fun { cons_caml_name = name;
		     cons_json_name = json_name;
		     cons_args = args } ->
		 match args with
		     [] -> 
		       <:match_case< 
		          $uid:name$ -> Json_type.String $str:json_name$ >>
		   | l ->
		       let args = numbered_list l in
		       let p =
			 List.fold_left
			   (fun cons (_, s) -> <:patt< $cons$ $lid:s$ >>)
			   <:patt< $uid:name$ >> args in
		       let e =
			 List.fold_right
			   (fun (x, s) l -> 
			      <:expr< [ $convert x$ $lid:s$ :: $l$ ] >>)
			   args <:expr< [] >> in
		       <:match_case< $p$ ->
			Json_type.Array 
			  [ Json_type.String $str:json_name$ :: $e$ ] >>)
	      v in
	  <:expr< fun [ $list:match_cases$ ] >>
      | Name x -> <:expr< $lid: "json_of_" ^ x$ >>
      | String -> build _loc "string"
      | Bool -> build _loc "bool"
      | Int -> build _loc "int"
      | Float -> build _loc "float"
      | Number -> build _loc "float"
      | Raw -> <:expr< fun x -> x >>
      | Custom modul -> <:expr< $uid:modul$ . to_json >>

  and convert_field_list access _loc l =
    let pairs = 
      List.fold_right
	(fun { field_caml_name = name;
	       field_json_name = json_name;
	       field_type = x } tl ->
	   <:expr< [ ( $str:json_name$, $convert x$ $access name$ )
		     :: $tl$ ] >>)
	l <:expr< [] >> in
    <:expr< fun x -> Json_type.Object $pairs$ >>
  in

  let defs = 
    List.fold_right
      (fun ((_loc, name), x) acc -> 
	 let fname = "json_of_" ^ name in
	 <:binding< ( $lid:fname$ : $lid:name$ -> Json_type.t ) =
	            $eta_expand (convert x.def)$ and $acc$ >>)
      l <:binding<>> in
  <:str_item< value rec $defs$ >>


let expand_typedefs _loc l =
  check_unique (fun (name, _) -> name) l;
  let names = 
    List.fold_left 
      (fun m (((_loc, name), _) as data) -> StringMap.add name data m)
      StringMap.empty l in
  let typedef = make_typedef _loc names l in
  let ofjson = make_ofjson _loc l in
  let tojson = make_tojson _loc l in
  <:str_item< $typedef$; $ofjson$; $tojson$ >>

let o2b = function None -> false | _ -> true

let is_reserved =
  let l = [ "json"; "json_type";
	    "string"; "bool"; "int"; "float"; 
	    "number"; "assoc" ] in
  let tbl = Hashtbl.create 20 in
  List.iter (fun s -> Hashtbl.add tbl s ()) l;
  Hashtbl.mem tbl

let list_of_opt = function None -> [] | Some x -> [x]
let list_of_optlist = function None -> [] | Some x -> x

let check_methods l =
  List.iter (fun x ->
	       if x.is_mutable then
		 Loc.raise x.field_caml_loc 
		   (Failure "object fields cannot be made mutable")) l

let string_assoc _loc = function
    (_loc, Tuple [ (_, String); (_, x) ]) -> (_loc, x)
  | (_, _) -> 
      Loc.raise _loc
	(Failure "must be of the form (string * ...) assoc")

open Syntax
let eval_string s = Camlp4.Struct.Token.Eval.string ~strict:() s

EXTEND Gram
  GLOBAL: str_item;
  str_item: LEVEL "top" [
    [ "type"; LIDENT "json"; 
      l = LIST1 type_binding SEP "and" -> expand_typedefs _loc l ]
  ];

  type_binding: [
    [ name = [ s = LIDENT -> 
		 if is_reserved s then
		   Loc.raise _loc 
		     (Failure ("you can't use '" ^ s ^ "' as a type name"))
		 else (_loc, s) ]; 
      "=";
      p = OPT [ LIDENT "predefined" (* ; 
		priv = OPT "private"*) -> (* priv <> None *) false ];
      t = [ t = type_expr -> (t : t)
	  | r = record -> (_loc, Record r)
	  | v = variants -> (_loc, Variant v) ] ->
	let type_def =
	  match p with
	      None -> { is_predefined = false;
			is_private = false;
			def = t }
	    | Some is_private -> 
		{ is_predefined = true;
		  is_private = is_private;
		  def = t } in
	(name, type_def) ]
  ];

  record: [
    [ "{"; l = methods; "}" -> l ]
  ];

  variants: [
    [ l = 
	LIST1 [ id = [ id = UIDENT -> (_loc, id) ]; 
		label = OPT [ s = STRING -> 
				(_loc, eval_string s) ];
		typ = OPT [ "of";
			    x = LIST1 type_expr LEVEL "simple" 
				SEP "*" -> x ] -> 
		  let id' = unopt id label in
		  { cons_caml_loc = fst id;
		    cons_caml_name = snd id;
		    cons_json_loc = fst id';
		    cons_json_name = snd id';
		    cons_args = list_of_optlist typ } ] 
	  SEP "|" -> 
	    check_unique (fun x -> (x.cons_caml_loc, x.cons_caml_name)) l;
            check_unique (fun x -> (x.cons_json_loc, x.cons_json_name)) l;
	    l ]
  ];

  type_expr: [
    "top" [
      x = type_expr; "*"; l = LIST1 type_expr LEVEL "simple" SEP "*" ->
	(_loc, Tuple (x :: l)) 
    ]
		
  | "simple" [
      x = type_expr; LIDENT "list" -> (_loc, List x)
    | x = type_expr; LIDENT "array" -> (_loc, Array x)
    | x = type_expr; LIDENT "option" -> (_loc, Option x)
    | x = type_expr; LIDENT "assoc" -> (_loc, Assoc (string_assoc _loc x))
    | "<"; l = methods; ">" -> check_methods l; (_loc, Object l)
    | "["; l = polymorphic_variants; "]" -> (_loc, Poly l)
    | "("; x = type_expr; ")" -> x
    | "("; LIDENT "string"; ","; x = type_expr; ")"; 
      UIDENT "Hashtbl"; "."; LIDENT "t" -> 
	(_loc, Hashtbl x)
    | LIDENT "string" -> (_loc, String)
    | LIDENT "bool" -> (_loc, Bool)
    | LIDENT "int" -> (_loc, Int)
    | LIDENT "float" -> (_loc, Float)
    | LIDENT "number" -> (_loc, Number)
    | [ UIDENT "Json_type"; "."; LIDENT "json_type"
      | LIDENT "json_type" ] -> (_loc, Raw)
    | name = LIDENT -> (_loc, Name name)
    | module_name = UIDENT; "."; LIDENT "t" -> 
	if module_name = "Json_type" then (_loc, Raw)
	else (_loc, Custom module_name) ]
  ];

  polymorphic_variants: [
    [ l = 
        LIST1 [ "`"; id = [ `(LIDENT id | UIDENT id) -> (_loc, id) ]; 
		label = OPT [ s = STRING -> 
				(_loc, eval_string s) ];
		typ = OPT [ "of"; x = type_expr -> x ] -> 
		  let id' = unopt id label in
		  { cons_caml_loc = fst id;
		    cons_caml_name = snd id;
		    cons_json_loc = fst id';
		    cons_json_name = snd id';
		    cons_args = list_of_opt typ } ] 
	  SEP "|" -> 
	    check_unique (fun x -> (x.cons_caml_loc, x.cons_caml_name)) l;
            check_unique (fun x -> (x.cons_json_loc, x.cons_json_name)) l;
	    l ]
  ];

  methods: [
    [ l = LIST0 
	    [ mut = OPT "mutable";
	      lab = method_label; x = type_expr; 
	      default = OPT [ "="; e = expr LEVEL "apply" -> e ] -> 
		let ((id, optional), label) = lab in
		let id' = unopt id label in
		{ field_caml_loc = fst id;
		  field_caml_name = snd id;
		  field_json_loc = fst id';
		  field_json_name = snd id';
		  field_type = x;
		  optional = optional;
		  default = default;
		  is_mutable = (mut <> None) } ]
	    SEP ";" ->
	check_unique (fun x -> (x.field_caml_loc, x.field_caml_name)) l;
        check_unique (fun x -> (x.field_json_loc, x.field_json_name)) l;
	l ]
  ];

  method_label: [
    [ id_opt = [ id = LIDENT -> ((_loc, id), false)
               | "?"; id = LIDENT -> ((_loc, id), true) ]; 
      label = OPT [ s = STRING -> 
		      (_loc, eval_string s) ];
      ":" -> (id_opt, label)
    | id = OPTLABEL -> (((_loc, id), true), None) ]
  ];

END
