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
type grammar = v_rule list;;

type t_rule_norm   = norm_unit * t_rule;;
type v_rule_norm   = variable * t_rule_norm;;
type grammar_norms = v_rule_norm list;;


(************************************************
 *************** Auxiliary functions ************
 ************************************************)

let variable_of_terminal (gr : grammar) (term : terminal) =
  fst (find (function (_, r) -> r = [(term, [])]) gr);;

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

let string_of_grammar (gr : grammar) =
  String.concat "\n" (map string_of_v_rule gr);;


(************************************************
 ***************** Norm functions ***************
 ************************************************)

exception Norm_not_found;;

let norm_of_variable (norms : grammar_norms) (var : variable) =
  try fst (assoc var norms) with Not_found -> raise Norm_not_found;;

let       eq_poly = {HOL.equal = (=)};;
let      ord_poly = {Orderings.less_eq = (<=); Orderings.less = (<)};;
let preorder_poly = {Orderings.ord_preorder = ord_poly};;
let    order_poly = {Orderings.preorder_order = preorder_poly};;
let linorder_poly = {Orderings.order_linorder = order_poly};;

let norms_of_grammar (gr : grammar) =
  let el = (eq_poly, linorder_poly) in
  if Grammar_defs.gram_nsd el el gr then
    let norms = Grammar_defs.norms_of_grammar el linorder_poly gr in
    map (fun (v, (Arith.Nat n, tr)) -> (v, (n, tr))) norms
  else
    failwith "Grammar is not simple-deterministic and normed!";;


(************************************************
 ***************** Decomposition ****************
 ************************************************)

exception Negative_decompose
exception Not_decomposable

let rec decompose
  (gr : grammar) (norms: grammar_norms) (final_norm : norm_unit) = function
  | [] -> if final_norm = zero_big_int then [] else raise Negative_decompose
  | head::tail ->
    let head_norm = norm_of_variable norms head in
    if lt_big_int final_norm zero_big_int then raise Negative_decompose
    else if eq_big_int final_norm zero_big_int then []
    else if ge_big_int final_norm head_norm then
      head::decompose gr norms (sub_big_int final_norm head_norm) tail
    else begin
      let rules = assoc head gr in
      if length rules = 1 then
        let (term, vars) = hd rules in
        variable_of_terminal gr term ::
          decompose gr norms (pred_big_int final_norm) vars
      else
        raise Not_decomposable
    end;;

exception Negative_norm_reduce

let rec norm_reduce 
  (gr : grammar) (norms : grammar_norms) (p : norm_unit) (vars : variables) =
  if lt_big_int p zero_big_int then
    raise Negative_norm_reduce
  else if eq_big_int p zero_big_int then
    vars
  else
    match vars with
    | [] -> raise Negative_norm_reduce
    | head::tail ->
      let head_norm = norm_of_variable norms head in
      if ge_big_int p head_norm then
        norm_reduce gr norms (sub_big_int p head_norm) tail
      else
        let (n, (t, vs)) = assoc head norms in
        (norm_reduce gr norms (pred_big_int p) vs) @ tail;;

