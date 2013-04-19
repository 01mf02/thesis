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

(* calculate the norm of a variable of a grammar *)
(* TODO: delete this! *)
(* production_rules -> variable -> int *)
let rec norm_of_variable (prods : production_rules) (var : variable) =
  let vars = snd (hd (rules_of_variable prods var)) in
  fold_left (fun n v -> n + (norm_of_variable prods v)) 1 vars;;

exception Norm_not_found;;

(* norm_list -> variables -> int *)
let rec norm_of_variables (norms : norm_list) = function
  | [] -> 0
  | hd::tl ->
    try (assoc hd norms) + (norm_of_variables norms tl)
    with Not_found -> raise Norm_not_found;;

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


(* production_rules -> bool *)
(* TODO: delete this! *)
let productions_valid (prods : production_rules) =
  let norms = norms_of_production_rules prods in

  let rec is_sorted prev_norm = function
    | [] -> true
    | (hdv, hdr)::tl ->
      let curr_norm = assoc hdv norms (*norm_of_variable prods hdv*) in
      if curr_norm >= prev_norm then is_sorted curr_norm tl
      else false in

  is_sorted 0 prods;;


(************************************************
 ***************** Decomposition ****************
 ************************************************)

exception Negative_decompose
exception Not_decomposable

(* production_rules -> int -> variables -> variables *)
let rec decompose (prods : production_rules) (final_norm : int) = function
  | [] -> if final_norm = 0 then [] else raise Negative_decompose
  | head::tail -> let head_norm = norm_of_variable prods head in
    if final_norm < 0 then raise Negative_decompose
    else if final_norm = 0 then []
    else if final_norm >= head_norm then
      head::decompose prods (final_norm - head_norm) tail
    else begin
      let rules = rules_of_variable prods head in
      if length rules = 1 then
        let (term, vars) = hd rules in
        variable_of_terminal prods term :: decompose prods (final_norm - 1) vars
      else
        raise Not_decomposable
    end;;

exception Negative_norm_reduce

(* int -> variables -> production_rules -> variables *)
let rec norm_reduce (p : int) (vars : variables) (prods : production_rules) =
  if p < 0 then
    raise Negative_norm_reduce
  else if p = 0 then
    vars
  else
    match vars with
    | [] -> raise Negative_norm_reduce
    | head::tail ->
      let head_norm = norm_of_variable prods head in
      if p >= head_norm then
        norm_reduce (p - head_norm) tail prods
      else
        let first_production = snd (hd (rules_of_variable prods head)) in
        (norm_reduce (p - 1) first_production prods) @ tail;;

