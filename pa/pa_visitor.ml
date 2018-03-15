(*pp camlp4orf *)

(* File: pa_visitor.ml,  by Yoann Padioleau.
 Heavily based on pa_sexp_conv.ml.
 Removed the Generate of_sexp (need only 1 direction when
 generate visitor)




    Copyright (C) 2005-

      Jane Street Holding, LLC
      Author: Markus Mottl
      email: mmottl\@janestcapital.com
      WWW: http://www.janestcapital.com/ocaml

   This file is derived from file "pa_tywith.ml" of version 0.45 of the
   library "Tywith".

   Tywith is Copyright (C) 2004, 2005 by

      Martin Sandin  <msandin@hotmail.com>

   This library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2 of the License, or (at your option) any later version.

   This library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with this library; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*)

(* Pa_sexp_conv: Preprocessing Module for Automated S-expression Conversions *)

open Printf
open Lexing

open Camlp4
open PreCast
open Ast
open Pa_type_conv

(* Utility functions *)

let ( *** ) f g x = f (g x)

let mk_rev_bindings _loc fps =
  let coll (i, bindings, patts, vars) fp =
    let name = "v" ^ string_of_int i in
    let var_expr = Gen.ide _loc name in
    let expr =
      match fp with
      | `Fun fun_expr -> <:expr< $fun_expr$ $var_expr$ >>
      | `Match matchings -> <:expr< match $var_expr$ with [ $matchings$ ] >>
    in
    let patt = Gen.idp _loc name in
    let bindings = <:binding< $patt$ = $expr$ and $bindings$ >> in
    i - 1, bindings, patt :: patts, var_expr :: vars
  in
  let n = List.length fps in
  let _, bindings, patts, expr =
    List.fold_left coll (n, BiNil _loc, [], []) fps
  in
  bindings, patts, expr

let mk_bindings _loc fps = mk_rev_bindings _loc (List.rev fps)

let unroll_cnv_fp _loc var = function
  | `Fun fun_expr -> <:expr< $fun_expr$ $var$ >>
  | `Match matchings -> <:expr< match $var$ with [ $matchings$ ] >>

let unroll_fun_matches _loc fp1 fp2 =
  match fp1, fp2 with
  | `Fun fun_expr1, `Fun fun_expr2 -> <:expr< $fun_expr1$ $fun_expr2$ >>
  | `Fun fun_expr, `Match matching -> <:expr< $fun_expr$ (fun [ $matching$ ]) >>
  | _ -> assert false  (* impossible *)

(* Generators for S-expressions *)

(* ugly: because of the monormphic restriction I have to do some trick
 * to generate the right visitor for polymorphic type (e.g.
 * v_wrap2, v_wrap3, etc. See visitor_php.ml for instance.
 *)
let h = Hashtbl.create 101

(* Generator for converters of OCaml-values to S-expressions *)
module Generate_sexp_of = struct
  let mk_abst_call _loc tn rev_path =
    match tn with
    | "wrap" | "paren" | "brace" | "bracket" 
    | "comma_list" | "and_list" | "pipe_list" | "semicolon_list" 
    | "star_list"
        ->

        let aref = 
          try Hashtbl.find h tn
          with Not_found ->
            let aref = ref 10 in
            Hashtbl.add h tn aref;
            aref
        in
        incr aref;
        let s = string_of_int !aref in
        <:expr< $id:Gen.ident_of_rev_path _loc (("v_" ^ tn ^ s) :: rev_path)$ >>
        
    | _ ->
        <:expr< $id:Gen.ident_of_rev_path _loc (("v_" ^ tn) :: rev_path)$ >>

  (* Conversion of type paths *)
  let sexp_of_path_fun _loc id =
    match Gen.get_rev_id_path id [] with
    | ["unit"] -> <:expr< v_unit >>
    | ["bool"] -> <:expr< v_bool >>
    | ["string"] -> <:expr< v_string >>
    | ["char"] -> <:expr< v_char >>
    | ["int"] -> <:expr< v_int >>
    | ["float"] -> <:expr< v_float >>
    | ["int32"] -> <:expr< v_int32 >>
    | ["int64"] -> <:expr< v_int64 >>
    | ["nativeint"] -> <:expr< v_nativeint >>
    | ["big_int"; "Big_int"] -> <:expr< v_big_int >>
    | ["nat"; "Nat"] -> <:expr< v_nat >>
    | ["num"; "Num"] -> <:expr< v_num >>
    | ["ratio"; "Ratio"] -> <:expr< v_ratio >>
    | ["ref"] -> <:expr< v_ref >>
    | ["t"; "Lazy"] | ["lazy_t"] -> <:expr< v_lazy >>
    | ["option"] -> <:expr< v_option >>
    | ["list"] -> <:expr< v_list >>
    | ["array"] -> <:expr< v_array >>
    | ["t"; "Hashtbl"] -> <:expr< v_hashtbl >>
    | tn :: rev_path -> mk_abst_call _loc tn rev_path
    | [] -> assert false  (* impossible *)

  (* Conversion of types *)
  let rec sexp_of_type _loc = function
    | <:ctyp< $tp1$ $tp2$ >> -> `Fun (sexp_of_appl_fun _loc tp1 tp2)
    | <:ctyp< ( $tup:tp$ ) >> -> sexp_of_tuple _loc tp
    | <:ctyp< '$parm$ >> -> `Fun (Gen.ide _loc ("_of_" ^ parm))
    | <:ctyp< $id:id$ >> -> `Fun (sexp_of_path_fun _loc id)
    | <:ctyp< $_$ -> $_$ >> -> `Fun <:expr< Conv.sexp_of_fun >>
    | <:ctyp< [< $row_fields$ ] >> | <:ctyp< [> $row_fields$ ] >>
    | <:ctyp< [= $row_fields$ ] >> -> sexp_of_variant _loc row_fields
    | <:ctyp< ! $parms$ . $poly_tp$ >> -> sexp_of_poly _loc parms poly_tp
    | _ ->
        prerr_endline (get_loc_err _loc "sexp_of_type: unknown type construct");
        exit 1

  (* Conversion of polymorphic types *)
  and sexp_of_appl_fun _loc tp1 tp2 =
    match sexp_of_type _loc tp1, sexp_of_type _loc tp2 with
    | `Fun fun_expr1, `Fun fun_expr2 -> <:expr< $fun_expr1$ $fun_expr2$ >>
    | `Fun fun_expr, `Match matching -> <:expr< $fun_expr$ (fun [ $matching$ ]) >>
    | _ -> assert false  (* impossible *)


  (* Conversion of tuples *)
  and sexp_of_tuple _loc tp =
    let fps = List.map (sexp_of_type _loc) (list_of_ctyp tp []) in
    let bindings, patts, vars = mk_bindings _loc fps in
    let in_expr = <:expr< () (*pad*) >> in
    let expr = <:expr< let $bindings$ in $in_expr$ >> in
    `Match <:match_case< ( $tup:paCom_of_list patts$ ) -> $expr$ >>


  (* Conversion of variant types *)

  and sexp_of_variant _loc row_fields =
    let rec loop = function
      | <:ctyp< $tp1$ | $tp2$ >> -> <:match_case< $loop tp1$ | $loop tp2$ >>
      | <:ctyp< `$cnstr$ >> ->
          <:match_case< `$cnstr$ -> ()(*pad Sexp.Atom $str:cnstr$*) >>
      | <:ctyp< `$cnstr$ of $tps$ >> ->
          let fps = List.map (sexp_of_type _loc) (list_of_ctyp tps []) in
          let bindings, patts, vars = mk_bindings _loc fps in
          let cnstr_expr = <:expr< () (*pad Sexp.Atom $str:cnstr$*) >> in
          let expr =
            <:expr<
              let $bindings$ in
              () (*pad*)
            >>
          in
          <:match_case< `$cnstr$ $paSem_of_list patts$ -> $expr$ >>
      | <:ctyp< [= $row_fields$ ] >> | <:ctyp< [> $row_fields$ ] >>
      | <:ctyp< [< $row_fields$ ] >> -> loop row_fields
      | <:ctyp< $tp1$ $tp2$ >> ->
          let id_path = Gen.get_appl_path _loc tp1 in
          let call = sexp_of_appl_fun _loc tp1 tp2 in
          <:match_case< #$id_path$ as v -> $call$ v >>
      | <:ctyp< $id:id$ >> ->
          let call =
            match Gen.get_rev_id_path id [] with
            | tn :: rev_path -> mk_abst_call _loc tn rev_path
            | [] -> assert false  (* impossible *)
          in
          <:match_case< #$id$ as v -> $call$ v >>
      | _ -> failwith "sexp_of_variant: unknown type"
    in
    `Match (loop row_fields)


  (* Polymorphic record fields *)

  and sexp_of_poly _loc parms tp =
    let bindings =
      let mk_binding parm =
        <:binding<
          $Gen.idp _loc ("_of_" ^ parm)$ = Conv.sexp_of_abstr
        >>
      in
      List.map mk_binding (Gen.ty_var_list_of_ctyp parms [])
    in
    match sexp_of_type _loc tp with
    | `Fun fun_expr -> `Fun <:expr< let $list:bindings$ in $fun_expr$ >>
    | `Match matchings ->
        `Match
          <:match_case<
            arg ->
              let $list:bindings$ in
              match arg with
              [ $matchings$ ]
          >>


  (* Conversion of sum types *)

  let rec branch_sum _loc = function
    | <:ctyp< $tp1$ | $tp2$ >> ->
        <:match_case< $branch_sum _loc tp1$ | $branch_sum _loc tp2$ >>
    | <:ctyp< $uid:cnstr$ >> ->
        <:match_case< $uid:cnstr$ -> () (*pad Sexp.Atom $str:cnstr$*) >>
    | <:ctyp< $uid:cnstr$ of $tps$ >> ->
        let fps = List.map (sexp_of_type _loc) (list_of_ctyp tps []) in
        let cnstr_expr = <:expr< () (*pad for simple cases: Sexp.Atom $str:cnstr$*) >> in
        let bindings, patts, vars = mk_bindings _loc fps in
        let patt =
          match patts with
          | [patt] -> patt
          | _ -> <:patt< ( $tup:paCom_of_list patts$ ) >>
        in
        <:match_case<
          $uid:cnstr$ $patt$ ->
            let $bindings$ in
            ()(*pad*)
        >>
    | _ -> failwith "branch_sum: unknown type"

  let sexp_of_sum _loc alts = `Match (branch_sum _loc alts)


  (* Conversion of record types *)

  let mk_rec_patt _loc patt name =
    let p = <:patt< $lid:name$ = $lid:"v_" ^ name$ >> in
    (* pad: reverse it, cf also List.rev below. hacky but it works *)
    <:patt< $p$; $patt$  >>

  let mk_cnv_expr _loc tp var =
    match sexp_of_type _loc tp with
    | `Fun fun_expr -> <:expr< $fun_expr$ $var$ >>
    | `Match matchings -> <:expr< match $var$ with [ $matchings$ ] >>

  let sexp_of_record _loc flds_ctyp =
    let flds = list_of_ctyp flds_ctyp [] in

    let rec coll (patt, expr) = function
      | <:ctyp< $lid:name$ : mutable $tp$ >>
      | <:ctyp< $lid:name$ : $tp$ >> ->
          let patt = mk_rec_patt _loc patt name in
          let vname = <:expr< $lid:"v_" ^ name$ >> in
          let cnv_expr = unroll_cnv_fp _loc vname  (sexp_of_type _loc tp) in
          let expr =
            <:expr<
              let arg = $cnv_expr$ in
              (* pad *)
              $expr$
            >>
          in
          patt, expr
      | _ -> assert false  (* impossible *)
    in
    let init_expr = <:expr< ()(*pad*) >> in
    let patt, expr = List.fold_left coll (<:patt<>>, init_expr) (List.rev flds) in
    `Match
      <:match_case<
        { $patt$ } ->
          (*pad*)
          $expr$
      >>


  (* Empty type *)
  let sexp_of_nil _loc = `Fun <:expr< fun _v -> assert False >>


  (* Generate code from type definitions *)

  let sexp_of_td _loc type_name tps rhs =
    let is_alias_ref = ref false in
    let handle_alias _loc tp = is_alias_ref := true; sexp_of_type _loc tp in
    let body =
      let rec loop _loc =
        Gen.switch_tp_def _loc
          ~alias:handle_alias
          ~sum:sexp_of_sum
          ~record:sexp_of_record
          ~variants:sexp_of_variant
          ~mani:(fun _loc _tp1 -> loop _loc)
          ~nil:sexp_of_nil
      in
      match loop _loc rhs with
      | `Fun fun_expr ->
          (* Prevent violation of value restriction through eta-expansion *)
          if !is_alias_ref && tps = [] then <:expr< fun [ v -> $fun_expr$ v ] >>
          else <:expr< $fun_expr$ >>
      | `Match matchings -> <:expr< fun [ $matchings$ ] >>
    in
    let patts =
      List.map (Gen.idp _loc *** (^) "_of_" *** Gen.get_tparam_id) tps
    in
    let bnd = Gen.idp _loc ("v_" ^ type_name) in
    <:binding< $bnd$ = $Gen.abstract _loc patts body$ >>

  let rec sexp_of_tds = function
    | TyDcl (_loc, type_name, tps, rhs, _cl) ->
        sexp_of_td _loc type_name tps rhs
    | TyAnd (_loc, tp1, tp2) ->
        <:binding< $sexp_of_tds tp1$ and $sexp_of_tds tp2$ >>
    | _ -> assert false  (* impossible *)

  let sexp_of tds =
    let binding, recursive, _loc =
      match tds with
      | TyDcl (_loc, type_name, tps, rhs, _cl) ->
          sexp_of_td _loc type_name tps rhs,
          Gen.type_is_recursive _loc type_name rhs, _loc
      | TyAnd (_loc, _, _) as tds -> sexp_of_tds tds, true, _loc
      | _ -> assert false  (* impossible *)
    in
    if recursive then <:str_item< value rec $binding$ >>
    else <:str_item< value $binding$ >>

  (* Add code generator to the set of known generators *)
  let () = add_generator "sexp_of" sexp_of
end



(* Add "of_sexp" and "sexp_of" as "sexp" to the set of generators *)
let () =
  add_generator
    "vi"
    (fun tds ->
      let _loc = Loc.ghost in
      <:str_item<
        $Generate_sexp_of.sexp_of tds$
      >>
    )
