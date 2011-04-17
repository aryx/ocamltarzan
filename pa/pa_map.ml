(*pp camlp4orf *)

(* Yoann Padioleau.
 *
 * Heavily based on pa_sexp_conv.ml.
 *
 * Copyright (C) 2005-
 * 
 * Jane Street Holding, LLC
 * Author: Markus Mottl
 * email: mmottl\@janestcapital.com
 * WWW: http://www.janestcapital.com/ocaml
 * 
 * This file is derived from file "pa_tywith.ml" of version 0.45 of the
 * library "Tywith".
 * 
 * Tywith is Copyright (C) 2004, 2005 by
 * 
 * Martin Sandin  <msandin@hotmail.com>
 * 
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2 of the License, or (at your option) any later version.
 * 
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

(* Pa_sexp_conv: Preprocessing Module for Automated S-expression Conversions *)

open Printf
open Lexing

open Camlp4
open PreCast
open Ast
open Pa_type_conv

let prefix = "map_"
let name_generator = "map"

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


(* Generators for S-expressions *)

(* Generator for converters of OCaml-values to S-expressions *)
module Generate_sexp_of = struct
  let mk_abst_call _loc tn rev_path =
    <:expr< $id:Gen.ident_of_rev_path _loc ((prefix ^ tn) :: rev_path)$ >>

  (* Conversion of type paths *)
  let sexp_of_path_fun _loc id =
    match Gen.get_rev_id_path id [] with
    | ["unit"] ->                   <:expr< map_of_unit      >>
    | ["bool"] ->                   <:expr< map_of_bool      >>
    | ["string"] ->                 <:expr< map_of_string    >>
    | ["char"] ->                   <:expr< map_of_char      >>
    | ["int"] ->                    <:expr< map_of_int       >>
    | ["float"] ->                  <:expr< map_of_float     >>

    | ["int32"] ->                  <:expr< map_of_int32     >>
    | ["int64"] ->                  <:expr< map_of_int64     >>
    | ["nativeint"] ->              <:expr< map_of_nativeint >>
    | ["big_int"; "Big_int"] ->     <:expr< map_of_big_int   >>
    | ["nat"; "Nat"] ->             <:expr< map_of_nat       >>
    | ["num"; "Num"] ->             <:expr< map_of_num       >>
    | ["ratio"; "Ratio"] ->         <:expr< map_of_ratio     >>

    | ["ref"] ->                    <:expr< map_of_ref       >>
    | ["option"] ->                 <:expr< map_of_option    >>
    | ["list"] ->                   <:expr< map_of_list      >>
    | ["array"] ->                  <:expr< map_of_array     >>
    | ["t"; "Hashtbl"] ->           <:expr< map_of_hashtbl   >>

    | ["t"; "Lazy"] | ["lazy_t"] -> <:expr< map_of_lazy      >>

    | tn :: rev_path -> mk_abst_call _loc tn rev_path
    | [] -> assert false  (* impossible *)

  (* Conversion of types *)
  let rec sexp_of_type _loc = function
    | <:ctyp< $tp1$ $tp2$ >> -> `Fun (sexp_of_appl_fun _loc tp1 tp2)
    | <:ctyp< ( $tup:tp$ ) >> -> sexp_of_tuple _loc tp
    | <:ctyp< '$parm$ >> -> `Fun (Gen.ide _loc ("_of_" ^ parm))
    | <:ctyp< $id:id$ >> -> `Fun (sexp_of_path_fun _loc id)
    | <:ctyp< $_$ -> $_$ >> -> `Fun <:expr< vof_fun >>
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
    let in_expr = <:expr< $tup:exCom_of_list vars$ >> in
    let expr = <:expr< let $bindings$ in $in_expr$ >> in
    `Match <:match_case< ( $tup:paCom_of_list patts$ ) -> $expr$ >>


  (* Conversion of variant types *)

  and sexp_of_variant _loc row_fields =
    failwith "DONT USE VARIANT, they are BAD"


  (* Polymorphic record fields *)

  and sexp_of_poly _loc parms tp =
    let bindings =
      let mk_binding parm =
        <:binding<
          $Gen.idp _loc ("_of_" ^ parm)$ = vof_abstr
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
        <:match_case< $uid:cnstr$ -> $uid:cnstr$ >>

    | <:ctyp< $uid:cnstr$ of $tps$ >> ->
        let fps = List.map (sexp_of_type _loc) (list_of_ctyp tps []) in
        let bindings, patts, vars = mk_bindings _loc fps in
        let patt =
          match patts with
          | [patt] -> patt
          | _ -> <:patt< ( $tup:paCom_of_list patts$ ) >>
        in
        <:match_case<
          $uid:cnstr$ $patt$ ->
            let $bindings$ in
            $uid:cnstr$ $tup:exCom_of_list vars$
        >>
    | _ -> failwith "branch_sum: unknown type"

  let sexp_of_sum _loc alts = `Match (branch_sum _loc alts)


  (* Conversion of record types *)

  let mk_rec_patt _loc patt name =
    let p = <:patt< $lid:name$ = $lid:"v_" ^ name$ >> in
    <:patt< $patt$; $p$ >>

  

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
              let $lid:"v_" ^ name$ = $cnv_expr$ in
              $expr$
            >>
          in
          patt, expr
      | _ -> assert false  (* impossible *)
    in
    let init_expr = <:expr< { xXXX = 1; } >> in
    let patt, expr = List.fold_left coll (<:patt<>>, init_expr) flds in
    `Match
      <:match_case<
        { $patt$ } ->
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
    let bnd = Gen.idp _loc (prefix ^ type_name) in
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
  let () = add_generator name_generator sexp_of
end


(* Add "of_sexp" and "sexp_of" as "sexp" to the set of generators *)
let () =
  add_generator
    (name_generator ^ "1")
    (fun tds ->
      let _loc = Loc.ghost in
      <:str_item<
        $Generate_sexp_of.sexp_of tds$
      >>
    )
