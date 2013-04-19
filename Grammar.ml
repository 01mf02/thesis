open List;;

(************************************************
 **************** Type definitions **************
 ************************************************)

type variable = string;;
type terminal = char;;
type variables = variable list;;
type variable_rule = terminal * variables;;
type variable_rules = variable_rule list;;
type production_rule = variable * variable_rules;;
type production_rules = production_rule list;;

type norm_list = (variable * int) list;;
type grammar = production_rules * norm_list;;


(************************************************
 *************** Auxiliary functions ************
 ************************************************)

let rules_of_variable (rules : production_rules) (var : variable) =
  assoc var rules;;

let variable_of_terminal (rules : production_rules) (term : terminal) =
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
let string_of_variable_rules (r : variable_rules) =
  String.concat " + " (map string_of_variable_rule r);;

(* production_rule -> string *)
let string_of_production_rule (v, rules) =
  v ^ " -> " ^ (string_of_variable_rules rules);;

(* production_rules -> string *)
let string_of_production_rules (r : production_rules) =
  String.concat "\n" (map string_of_production_rule r);;


(************************************************
 ***************** Norm functions ***************
 ************************************************)

exception Norm_not_found;;

(* norm_list -> variable -> int *)
let norm_of_variable (norms : norm_list) (var : variable) =
  try assoc var norms with Not_found -> raise Norm_not_found;;

(* norm_list -> variables -> int *)
let rec norm_of_variables (norms : norm_list) =
  fold_left (fun sum var -> sum + (norm_of_variable norms var)) 0;;

(* calculate norms of all variables in the production rules and
 * verify that production rules adhere to required restrictions:
   * for all variables X_i in the production rules, norm(X_i) <= norm(X_(i+1))
   * the first rule for each variable generates a norm-reducing transition,
     i.e. norm(X_i) > norm(alpha_i1)
   * norm(alpha_i1) <= norm(alpha_ij) *)
(* production_rules -> norm_list *)
let norms_of_production_rules (prods : production_rules) =
  let rec norm_list norms = function
    | [] -> []
    | (_, hdv)::tl ->
      try (norm_of_variables norms hdv)::norm_list norms tl
      with Norm_not_found -> norm_list norms tl in

  let rec nopr norms prev_min_norm = function
    | [] -> norms
    | (hdv, hdr)::tl ->
      let first_norm = norm_of_variables norms (snd (hd hdr)) in
      let min_norm = min_list (norm_list norms hdr) in
      if first_norm > min_norm then
        failwith "Norm of first production rule is not the smallest norm!"
      else if prev_min_norm > min_norm then
        failwith "Norm of current variable is smaller than previous variable!"
      else
        nopr ((hdv, 1 + min_norm)::norms) min_norm tl in

  nopr [] 0 prods;;

let grammar_of_production_rules (prods : production_rules) =
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

