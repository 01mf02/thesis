open Format;;
open List;;

(************************************************
 ************ Grammar type definitions **********
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
    (* case for negative final_norm? *)
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
 ************* Proof type definitions ***********
 ************************************************)

type expression =
    Product of variable * variables
  | Sum of variable_rule * variable_rules;;

type equivalence = expression * expression;;

type sequent = equivalence * rule and rule =
  | Refl
  | Gr
  | Unsupported
  | Sym   of equivalence
  | Plus  of equivalence * equivalence
  | Times of equivalence * equivalence
  | Trans of equivalence * equivalence;;

let equivalences_of_rule = function
  | Refl -> []
  | Gr -> []
  | Unsupported -> []
  | Sym e -> [e]
  | Plus  (e1, e2) -> [e1; e2]
  | Times (e1, e2) -> [e1; e2]
  | Trans (e1, e2) -> [e1; e2];;

let string_of_expression = function
  | Product (ph, pt) -> string_of_variables (ph::pt)
  | Sum (sh, st) -> string_of_variable_rules (sh::st);;

let string_of_equivalence (a, b) =
  (string_of_expression a) ^ " = " ^ (string_of_expression b);;

let string_of_equivalences eqs =
  String.concat ", " (map string_of_equivalence eqs);;

let string_of_rule = function
  | Refl -> "Refl"
  | Gr -> "Gr"
  | Unsupported -> "Unsupported"
  | Sym e -> "Sym(" ^ (string_of_equivalence e) ^ ")"
  | Plus  (e1, e2) -> "Plus("  ^ (string_of_equivalences [e1; e2]) ^ ")"
  | Times (e1, e2) -> "Times(" ^ (string_of_equivalences [e1; e2]) ^ ")"
  | Trans (e1, e2) -> "Trans(" ^ (string_of_equivalences [e1; e2]) ^ ")";;

let rec string_of_sequent (e, r) =
  (string_of_equivalence e) ^ " -> " ^ (string_of_rule r);;

let rec print_sequents =
  iter (fun s -> print_endline (string_of_sequent s));;


exception Empty_variables;;
exception Empty_variable_rules;;
exception Proof_impossible;;

let product_of_variable v = Product(v, []);;

let product_of_variables = function
  | [] -> raise Empty_variables
  | (vh::vt) -> Product(vh, vt);;

let sum_of_variable_rules = function
  | [] -> raise Empty_variable_rules
  | (rh::rt) -> Sum(rh, rt);;


exception No_prefix;;

let prove_equivalence (eq : equivalence) (prods : production_rules) =
  let pov = product_of_variables in

  let partition f l =
    let rec aux prefix postfix =
      if f prefix then prefix, postfix
      else match postfix with
        | [] -> raise No_prefix
        | h::t -> aux (prefix@[h]) t in
    aux [] l in

  let prove_eq (e : equivalence) = match e with (a, b) ->
    if a = b then
      e, Refl
    else match a with
      | Product (pah, []) ->
          let gr = sum_of_variable_rules (rules_of_variable pah prods) in
          if b = gr then e, Gr
          else e, Trans((a, gr), (gr, b))
      | Product (pah, pat) ->
        begin match b with
        | Product (pbh, []) -> e, Sym(b, a)
        | Product (pbh, pbt) ->
          let (npah, npbh) = (norm pah prods, norm pbh prods) in
          if npah > npbh then
            try
              let nov = norm_of_variables in
              let (pb1, pb2) =
                partition (fun l -> nov prods l = npah) (pbh::pbt) in
              e, Times((pov [pah], pov pb1), (pov pat, pov pb2))
            with No_prefix ->
              let a' = pov (pbh::norm_reduce npbh [pah] prods @ pat) in
              e, Trans((a, a'), (a', b))
          else if npah = npbh then
            e, Times((pov [pah], pov [pbh]), (pov pat, pov pbt))
          else
            e, Sym(b, a)
        | _ -> e, Unsupported
        end
      | Sum ((sahc, sahv), []) ->
          begin match b with
          | Product (pbh, []) -> e, Sym((b, a))
          | Sum ((sbhc, sbhv), []) ->
            if sahc = sbhc then
              let sum_of_terminal t = Sum((t, []), []) in
              e, Times((sum_of_terminal sahc, sum_of_terminal sbhc),
                       (pov sahv, pov sbhv))
            else
              raise Proof_impossible
          | _ -> e, Unsupported
          end
      | _ -> e, Unsupported in

  let rec construct_proof seqs = function
    | [] -> seqs
    | (eqh::eqt) ->
      let seq = prove_eq eqh in
      let eqs = equivalences_of_rule (snd seq) in
      let unproven_eqs =
        filter (fun e -> not (exists (fun (se, _) -> e = se) seqs)) eqs in
      construct_proof (seq::seqs) (unproven_eqs@eqt) in

  construct_proof [] [eq];;


let prove_var_eq a b =
  prove_equivalence (product_of_variable a, product_of_variable b);;


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

  print_endline "Proof:";
  print_sequents (prove_var_eq "F5" "G5" prods);

  exit 0;
;;
