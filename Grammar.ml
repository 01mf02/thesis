open List;;
open Norm;;

(************************************************
 **************** Type definitions **************
 ************************************************)

type variable = string;;
type terminal = char;;
type variables = variable list;;

type norm_unit = int;;

type t_rule  = terminal * variables;;
type t_rules = t_rule list;;
type v_rule  = variable * t_rules;;
type v_rules = v_rule list;;

type t_rule_norm   = norm_unit * t_rule;;
type v_rule_norm   = variable * t_rule_norm;;
type v_rules_norms = v_rule_norm list;;

type grammar = v_rules * v_rules_norms;;


(************************************************
 *************** Auxiliary functions ************
 ************************************************)

let rules_of_variable (rules : v_rules) (var : variable) =
  assoc var rules;;

let variable_of_terminal (rules : v_rules) (term : terminal) =
  fst (find (function (_, r) -> r = [(term, [])]) rules);;

(* return smallest element of an int list, or raise Not_found if list empty *)
let min_list l =
  let rec ml curr_min = function
    | [] -> curr_min
    | hd::tl -> if hd < curr_min then ml hd tl else ml curr_min tl in
  match l with
  | [] -> raise Not_found
  | hd::tl -> ml hd tl;;


(************************************************
 *************** Printing functions *************
 ************************************************)

(* variables -> string *)
let string_of_variables (vars : variables) =
  String.concat " " vars;;

(* variable_rule -> string *)
let string_of_variable_rule (term, vars) =
  String.concat " " ((String.make 1 term)::vars);;

(* variable_rules -> string *)
let string_of_variable_rules (rules : t_rules) =
  String.concat " + " (map string_of_variable_rule rules);;

(* production_rule -> string *)
let string_of_production_rule (v, rules) =
  v ^ " -> " ^ (string_of_variable_rules rules);;

(* production_rules -> string *)
let string_of_production_rules (rules : v_rules) =
  String.concat "\n" (map string_of_production_rule rules);;


(************************************************
 ***************** Norm functions ***************
 ************************************************)

exception Norm_not_found;;

(* norm_list -> variable -> int *)
let norm_of_variable (norms : v_rules_norms) (var : variable) =
  try fst (assoc var norms) with Not_found -> raise Norm_not_found;;

let       eq_poly = {Norm.equal          = (=)};;
let      ord_poly = {Norm.less_eq        = (<=); Norm.less = (<)};;
let preorder_poly = {Norm.ord_preorder   = ord_poly};;
let    order_poly = {Norm.preorder_order = preorder_poly};;
let linorder_poly = {Norm.order_linorder = order_poly};;

let norms_of_production_rules (rules : v_rules) =
  let el = (eq_poly, linorder_poly) in
  if Norm.gram_nsd el el rules then
    let norms = Norm.norms_of_grammar el linorder_poly rules in
    map (fun (v, (Norm.Nat n, (t, vs))) ->
      (v, (Big_int.int_of_big_int n, (t, vs)))) norms
  else
    failwith "Grammar is not normed simple-deterministic!";;

let grammar_of_production_rules (prods : v_rules) =
  (prods, norms_of_production_rules prods);;


(************************************************
 ***************** Decomposition ****************
 ************************************************)

exception Negative_decompose
exception Not_decomposable

(* grammar -> int -> variables -> variables *)
let rec decompose (gram : grammar) (final_norm : int) = function
  | [] -> if final_norm = 0 then [] else raise Negative_decompose
  | head::tail ->
    let (prods, norms) = gram in
    let head_norm = norm_of_variable norms head in
    if final_norm < 0 then raise Negative_decompose
    else if final_norm = 0 then []
    else if final_norm >= head_norm then
      head::decompose gram (final_norm - head_norm) tail
    else begin
      let rules = rules_of_variable prods head in
      if length rules = 1 then
        let (term, vars) = hd rules in
        variable_of_terminal prods term :: decompose gram (final_norm - 1) vars
      else
        raise Not_decomposable
    end;;

exception Negative_norm_reduce

(* int -> variables -> grammar -> variables *)
let rec norm_reduce (p : int) (vars : variables) (gram : grammar) =
  if p < 0 then
    raise Negative_norm_reduce
  else if p = 0 then
    vars
  else
    match vars with
    | [] -> raise Negative_norm_reduce
    | head::tail ->
      let (prods, norms) = gram in
      let head_norm = norm_of_variable norms head in
      if p >= head_norm then
        norm_reduce (p - head_norm) tail gram
      else
        let first_production = snd (hd (rules_of_variable prods head)) in
        (norm_reduce (p - 1) first_production gram) @ tail;;

