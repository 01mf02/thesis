open List;;
open Norm;;
open Big_int;;

(************************************************
 **************** Type definitions **************
 ************************************************)

type variable = string;;
type terminal = char;;
type variables = variable list;;

type norm_unit = big_int;;

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

let string_of_variables (vars : variables) =
  String.concat " " vars;;

let string_of_t_rule (term, vars) =
  String.concat " " ((String.make 1 term)::vars);;

let string_of_t_rules (rules : t_rules) =
  String.concat " + " (map string_of_t_rule rules);;

let string_of_v_rule (v, rules) =
  v ^ " -> " ^ (string_of_t_rules rules);;

let string_of_v_rules (rules : v_rules) =
  String.concat "\n" (map string_of_v_rule rules);;


(************************************************
 ***************** Norm functions ***************
 ************************************************)

exception Norm_not_found;;

let norm_of_variable (norms : v_rules_norms) (var : variable) =
  try fst (assoc var norms) with Not_found -> raise Norm_not_found;;

let       eq_poly = {Norm.equal          = (=)};;
let      ord_poly = {Norm.less_eq        = (<=); Norm.less = (<)};;
let preorder_poly = {Norm.ord_preorder   = ord_poly};;
let    order_poly = {Norm.preorder_order = preorder_poly};;
let linorder_poly = {Norm.order_linorder = order_poly};;

let norms_of_v_rules (rules : v_rules) =
  let el = (eq_poly, linorder_poly) in
  if Norm.gram_nsd el el rules then
    let norms = Norm.norms_of_grammar el linorder_poly rules in
    map (fun (v, (Norm.Nat n, tr)) -> (v, (n, tr))) norms
  else
    failwith "Grammar is not simple-deterministic and normed!";;

let grammar_of_v_rules (rules : v_rules) =
  (rules, norms_of_v_rules rules);;


(************************************************
 ***************** Decomposition ****************
 ************************************************)

exception Negative_decompose
exception Not_decomposable

let rec decompose (gram : grammar) (final_norm : norm_unit) = function
  | [] -> if final_norm = zero_big_int then [] else raise Negative_decompose
  | head::tail ->
    let (prods, norms) = gram in
    let head_norm = norm_of_variable norms head in
    if lt_big_int final_norm zero_big_int then raise Negative_decompose
    else if eq_big_int final_norm zero_big_int then []
    else if ge_big_int final_norm head_norm then
      head::decompose gram (sub_big_int final_norm head_norm) tail
    else begin
      let rules = assoc head prods in
      if length rules = 1 then
        let (term, vars) = hd rules in
        variable_of_terminal prods term ::
          decompose gram (pred_big_int final_norm) vars
      else
        raise Not_decomposable
    end;;

exception Negative_norm_reduce

let rec norm_reduce (p : norm_unit) (vars : variables) (gram : grammar) =
  if lt_big_int p zero_big_int then
    raise Negative_norm_reduce
  else if eq_big_int p zero_big_int then
    vars
  else
    match vars with
    | [] -> raise Negative_norm_reduce
    | head::tail ->
      let (prods, norms) = gram in
      let head_norm = norm_of_variable norms head in
      if ge_big_int p head_norm then
        norm_reduce (sub_big_int p head_norm) tail gram
      else
        let (n, (t, vs)) = assoc head norms in
        (norm_reduce (pred_big_int p) vs gram) @ tail;;

