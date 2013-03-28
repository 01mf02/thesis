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
    if final_norm = 0 then []
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


let rec fibonacci_grammar n =
  let nonprime_var v vf1 vf2 = function
    | 0 -> zero_variables [(v ^ "0", 'a')]
    | 1 -> zero_variables [(v ^ "1", 'a')]
    | 2 -> one_variable [(v ^ "2", 'a', v ^ "0")]
    | n -> two_variables [(v ^ soi n, 'a', vf1 n, vf2 n)] in

  let prime_var v vf1 vf2 = function
    | 0 -> []
    | 1 -> []
    | 2 -> zero_variables [(v ^ "2'", 'a')]
    | 3 -> one_variable [(v ^ "3'", 'a', v ^ "2'")]
    | n -> two_variables [(v ^ soi n ^ "'", 'a', vf1 n, vf2 n)] in

  let f = nonprime_var "F"
    (fun n -> "F" ^ soi (n-2)) (fun n -> "F" ^ soi (n-1) ^ "'") in
  let g = nonprime_var "G"
    (fun n -> "G" ^ soi (n-1) ^ "'") (fun n -> "G" ^ soi (n-2)) in

  let f' = prime_var "F"
    (fun n -> "F" ^ soi (n-2) ^ "'") (fun n -> "F" ^ soi (n-1) ^ "'") in
  let g' = prime_var "G"
    (fun n -> "G" ^ soi (n-1) ^ "'") (fun n -> "G" ^ soi (n-2) ^ "'") in

  match n with
    | 0 -> f 0 @ g 0
    | n -> fibonacci_grammar (n-1) @ f' n @ g' n @ f n @ g n;;


(************************************************
 ****************** Main function ***************
 ************************************************)

let _ =
  let prods = fibonacci_grammar 10 in

  if productions_valid prods then
    print_endline "Productions valid. :)"
  else begin
    print_endline "Productions invalid! :@";
    exit 1
  end;

  print_endline "Production rules:";
  print_endline (string_of_production_rules prods);

  print_endline ("Norm: " ^ (string_of_int (norm "G10" prods)));

  print_endline ("Decomposition: " ^
    string_of_variables (decompose prods 88 ["G10"]));

  exit 0;
;;
