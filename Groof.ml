open Format;;
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

let rules_of_variable (var : variable) (rules : production_rules) =
  match find (function (v, r) -> v = var) rules with (_, r) -> r;;


(************************************************
 *************** Printing functions *************
 ************************************************)

(* variables -> string *)
let string_of_variables (vars : variables) =
  String.concat " " vars;;

(* variable_rule -> string *)
let string_of_variable_rule (c, vars) =
  (String.make 1 c) ^ " " ^ string_of_variables vars;;

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
(* variable -> production_rules -> int *)
let rec norm (v : variable) (prods : production_rules) =
  let vars = snd (hd (rules_of_variable v prods)) in
  fold_left (fun prev_sum curr_var -> prev_sum + (norm curr_var prods)) 1 vars;;


(************************************************
 **************** Example grammars **************
 ************************************************)

let zero_variables = map (fun (v, c) -> (v, [(c, [])]));;
let one_variable = map (fun (v, c, v1) -> (v, [(c, [v1])]));;
let two_variables = map (fun (v, c, v1, v2) -> (v, [(c, [v1; v2])]));;
let soi = string_of_int;;

let rec ab_grammar n =
  let unequal_var vu ve t vt = function
    | 0 -> one_variable [(vu ^ "0", t, vt)]
    | n -> one_variable [(vu ^ soi n, t, ve ^ soi n)] in

  let equal_var ve vu t = function
    | 0 -> []
    | n -> two_variables [(ve ^ soi n, t, vu ^ soi (n-1), vu ^ soi (n-1))] in

  let ab = unequal_var "AB" "BB" 'a' "B" in
  let ba = unequal_var "BA" "AA" 'b' "A" in
  let aa = equal_var "AA" "BA" 'a' in
  let bb = equal_var "BB" "AB" 'b' in

  let fg n = two_variables [("F" ^ soi n, 'a', "B", "AB" ^ soi n);
                            ("G" ^ soi n, 'a', "BA" ^ soi n, "B")] in

  match n with
    | 0 -> zero_variables [("A", 'a'); ("B", 'b')] @ ab 0 @ ba 0 @ fg 0
    | n -> ab_grammar (n-1) @ aa n @ bb n @ ab n @ ba n @ fg n;;

let rec power_two_grammar n =
  let nonprime_var v vf1 vf2 = function
    | 0 -> zero_variables [(v ^ "0", 'a')]
    | 1 -> one_variable [(v ^ "1", 'a', v ^ "0")]
    | n -> let p = soi (n-1) in
           two_variables [(v ^ soi n, 'a', vf1 p, vf2 p)] in

  let prime_var v = function
    | 0 -> []
    | 1 -> zero_variables [(v ^ "1'", 'a')]
    | n -> let pp = v ^ soi (n-1) ^ "'" in
           two_variables [(v ^ soi n ^ "'", 'a', pp, pp)] in

  let s = nonprime_var "S" (fun p -> "S" ^ p) (fun p -> "S" ^ p ^ "'") in
  let t = nonprime_var "T" (fun p -> "T" ^ p ^ "'") (fun p -> "T" ^ p) in
  let s' = prime_var "S" in
  let t' = prime_var "T" in

  match n with
    | 0 -> s 0 @ t 0
    | n -> power_two_grammar (n-1) @ s' n @ t' n @ s n @ t n;;


(************************************************
 ****************** Main function ***************
 ************************************************)

let _ =
  let prods = ab_grammar 10 in

  print_endline "Production rules:";
  print_endline (string_of_production_rules prods);

  print_endline ("Norm: " ^ (string_of_int (norm "F10" prods)));
;;
