open Format;;
open List;;

open Grammar;;


(************************************************
 **************** Type definitions **************
 ************************************************)

type expression =
  | Product of variable * variables
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


(************************************************
 *************** Auxiliary functions ************
 ************************************************)

exception Empty_variables
exception Empty_variable_rules

let product_of_variable v = Product(v, []);;
let sum_of_terminal t = Sum((t, []), []);;

let product_of_variables = function
  | [] -> raise Empty_variables
  | (vh::vt) -> Product(vh, vt);;

let sum_of_variable_rules = function
  | [] -> raise Empty_variable_rules
  | (rh::rt) -> Sum(rh, rt);;

let equivalences_of_rule = function
  | Refl -> []
  | Gr -> []
  | Unsupported -> []
  | Sym e -> [e]
  | Plus  (e1, e2) -> [e1; e2]
  | Times (e1, e2) -> [e1; e2]
  | Trans (e1, e2) -> [e1; e2];;

let expression_equals x y =
  (* TODO *)
  x = y;;


(************************************************
 *************** Printing functions *************
 ************************************************)

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


(************************************************
 *************** Proof construction *************
 ************************************************)

exception Proof_impossible
exception Circular_sequent

let prove_equivalence (eq : equivalence) (prods : production_rules) =
  let pov = product_of_variables in

  (* determine whether the first list is a prefix of the second list,
   * and if so, also return the remaining part of the second list *)
  let rec is_prefix = function
    | ([], postfix) -> (true, postfix)
    | (_::_, []) -> (false, [])
    | (h1::t1, h2::t2) -> if h1 = h2 then is_prefix (t1, t2) else (false, []) in

  let rule_of_equivalence (a, b) =
    let trans x = Trans((a, x), (x, b)) in

    let rule_of_products (pah, pat) (pbh, pbt) =
      let pair_map f (x, y) = (f x, f y) in
      let (npah, npbh) = pair_map (norm_of_variable prods) (pah, pbh) in

      if npah < npbh then
        Sym(b, a)
      else
        try
          let dec = decompose prods npah (pbh::pbt) in
          let (dec_is_prefix, postfix) = is_prefix (dec, (pbh::pbt)) in
          if dec_is_prefix then
            Times((pov [pah], pov dec), (pov pat, pov postfix))
          else
            trans (pov (dec@pat))
        with Not_decomposable ->
          trans (pov (pbh::norm_reduce npbh [pah] prods @ pat)) in


    if expression_equals a b then
      Refl
    else
      match a with
      | Product (pah, []) ->
        let gr = sum_of_variable_rules (rules_of_variable prods pah) in
        if expression_equals b gr then Gr
        else begin match b with
          | Product (pbh, []) ->
            trans gr
          | Product (pbh, pbt) ->
            let npbh = norm_of_variable prods pbh in
            let reduct = pbh::norm_reduce npbh [pah] prods in
            if reduct = pbh::pbt then trans gr
            else trans (pov reduct)
          | Sum ((sbhc, sbhv), []) ->
            trans (Product(variable_of_terminal prods sbhc, sbhv))
          | _ -> Unsupported
        end
      | Product (pah, pat) ->
        begin match b with
        | Product (pbh, []) -> Sym(b, a)
        | Product (pbh, pbt) ->
          rule_of_products (pah, pat) (pbh, pbt)
        | Sum ((sbhc, sbhv), []) ->
          if norm_of_variable prods pah = 1 then
            Times((pov [pah], sum_of_terminal sbhc), (pov pat, pov sbhv))
          else
            trans (Product(variable_of_terminal prods sbhc, sbhv))
        | _ -> Unsupported
        end
      | Sum ((sahc, sahv), []) ->
        begin match b with
        | Product (_, _) -> Sym((b, a))
        | Sum ((sbhc, sbhv), []) ->
          if sahc = sbhc then
            let sum_of_terminal t = Sum((t, []), []) in
            Times((sum_of_terminal sahc, sum_of_terminal sbhc),
                  (pov sahv, pov sbhv))
          else
            raise Proof_impossible
        | _ -> Unsupported
        end
      | _ -> Unsupported in

  let rec construct_proof seqs = function
    | [] -> seqs
    | (eqh::eqt) ->
      let rule = rule_of_equivalence eqh in
      let eqs = equivalences_of_rule rule in

      if exists (fun e -> e = eqh) eqs then raise Circular_sequent
      else
        let unproven_eqs =
          filter (fun e -> not (exists (fun (se, _) -> e = se) seqs)) eqs in
        construct_proof ((eqh, rule)::seqs) (unproven_eqs@eqt) in

  construct_proof [] [eq];;


let prove_var_eq a b =
  prove_equivalence (product_of_variable a, product_of_variable b);;


(************************************************
 ****************** Main function ***************
 ************************************************)

let _ =
  let prods = Examples.fibonacci_grammar 10 in

  if productions_valid prods then
    print_endline "Productions valid. :)"
  else begin
    print_endline "Productions invalid! :@";
    exit 1
  end;

  print_endline "Production rules:";
  print_endline (string_of_production_rules prods);

  print_endline ("Norm: " ^ (string_of_int (norm_of_variable prods "G10")));

  print_endline ("Decomposition: " ^
    string_of_variables (decompose prods 88 ["G10"]));

  print_endline "Proof:";
  print_sequents (prove_var_eq "F4" "G4" prods);

  exit 0;
;;
