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


(************************************************
 *************** Auxiliary functions ************
 ************************************************)

let rules_of_variable (var : variable) (rules : production_rules) =
  snd (find (function (v, _) -> v = var) rules);;

let variable_of_terminal (term : terminal) (rules : production_rules) =
  fst (find (function (_, r) -> r = [(term, [])]) rules);;


(************************************************
 *************** Printing functions *************
 ************************************************)

(* variables -> string *)
let string_of_variables (vars : variables) =
  String.concat " " vars;;

(* variable_rule -> string *)
let string_of_variable_rule (c, vars) =
  String.concat " " ((String.make 1 c)::vars);;

(* variable_rules -> string *)
let string_of_variable_rules (r : variable_rules) =
  String.concat " | " (map string_of_variable_rule r);;

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
(* TODO: inverse order of v and prods to be consistent with nov! *)
(* variable -> production_rules -> int *)
let rec norm (v : variable) (prods : production_rules) =
  let vars = snd (hd (rules_of_variable v prods)) in
  fold_left (fun prev_sum curr_var -> prev_sum + (norm curr_var prods)) 1 vars;;

let norm_of_variables prods = fold_left (fun n v -> n + norm v prods) 0;;

(* verify that production rules adhere to required restrictions:
   * for all variables X_i in the production rules, norm(X_i) <= norm(X_(i+1))
   * the first rule for each variable generates a norm-reducing transition,
     i.e. norm(X_i) > norm(alpha_i1) *)
(* production_rules -> bool *)
let productions_valid (prods : production_rules) =
  let rec is_sorted prev_norm = function
    | [] -> true
    | (hdv, hdr)::tl ->
      let curr_norm = norm hdv prods in
      if curr_norm >= prev_norm then is_sorted curr_norm tl
      else false in

  is_sorted 0 prods;;


(************************************************
 ***************** Decomposition ****************
 ************************************************)

exception Not_decomposable;;

let rec decompose prods final_norm = function
  | [] -> if final_norm = 0 then [] else raise Not_decomposable
  | hdv::tlv -> let hd_norm = norm hdv prods in
    if final_norm < 0 then raise Not_decomposable
    else if final_norm = 0 then []
    else if final_norm >= hd_norm then
      hdv::decompose prods (final_norm - hd_norm) tlv
    else begin
      let rules = rules_of_variable hdv prods in
      if length rules = 1 then
        let (term, vars) = hd rules in
        variable_of_terminal term prods :: decompose prods (final_norm - 1) vars
      else
        raise Not_decomposable
    end;;

exception Negative_norm_reduce

(* int -> variables -> production_rules -> int list *)
let rec norm_reduce (p : int) (vars : variables) (prods : production_rules) =
  if p < 0 then
    raise Negative_norm_reduce
  else if p = 0 then
    vars
  else
    match vars with
    | [] -> raise Negative_norm_reduce
    | head::tail ->
        if p >= norm head prods then
          norm_reduce (p - norm head prods) tail prods
        else
          let first_production = snd (hd (rules_of_variable head prods)) in
          (norm_reduce (p - 1) first_production prods) @ tail;;

