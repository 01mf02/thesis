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
  | Sym e -> [e]
  | Plus  (e1, e2) -> [e1; e2]
  | Times (e1, e2) -> [e1; e2]
  | Trans (e1, e2) -> [e1; e2];;

let pair_map f (x, y) = (f x, f y);;

let rec expression_equals = function
  | (Product(pah, pat), Product(pbh, pbt)) -> pah = pbh && pat = pbt
  | (Product(_, _), Sum(_, _)) -> false
  | (Sum(_, _), Product(_, _)) -> false
  | (Sum(sah, sat), Sum(sbh, sbt)) ->
    for_all (fun (sac, sav) -> exists (fun (sbc, sbv) ->
      sac = sbc &&
      if length sav = 0 then length sbv = 0
      else
        length sbv > 0 &&
        expression_equals (pair_map product_of_variables (sav, sbv)))
    (sbh::sbt)) (sah::sat);;

let is_sequent_of_equivalence eq (seq, _) = seq = eq;;


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
  | Sym e -> "Sym(" ^ (string_of_equivalence e) ^ ")"
  | Plus  (e1, e2) -> "Plus("  ^ (string_of_equivalences [e1; e2]) ^ ")"
  | Times (e1, e2) -> "Times(" ^ (string_of_equivalences [e1; e2]) ^ ")"
  | Trans (e1, e2) -> "Trans(" ^ (string_of_equivalences [e1; e2]) ^ ")";;

let rec string_of_sequent (e, r) =
  (string_of_equivalence e) ^ " -> " ^ (string_of_rule r);;

let rec print_sequents =
  iter (fun s -> print_endline (string_of_sequent s));;


let latex_of_expression e = "{" ^ string_of_expression e ^ "}";;
let latex_of_equivalence (a, b) =
  latex_of_expression a ^ latex_of_expression b;;

let latex_of_sequents seqs eq_root =

  let rec lose proven eq =
    let loeq = latex_of_equivalence in

    let aux str eq eqs =
      let fold_f (s, p) e =
        let (s', p') = lose p e in
        (s ^ s', p') in

      let (s, p) = fold_left fold_f ("\\" ^ str ^ loeq eq, eq::proven) eqs in
      ("{" ^ s ^ "}", p) in

    if mem eq proven then
      aux "sj" eq []
    else
      let (_, r) = find (is_sequent_of_equivalence eq) seqs in
      match r with
      | Refl           -> aux "refl"     eq []
      | Gr             -> aux "gr"       eq []
      | Sym e          -> aux "syminf"   eq [e]
      | Plus  (e1, e2) -> aux "plusinf"  eq [e1; e2]
      | Times (e1, e2) -> aux "timesinf" eq [e1; e2]
      | Trans (e1, e2) -> aux "transinf" eq [e1; e2] in

  "\\bussproof" ^ (fst (lose [] eq_root));;


(************************************************
 *************** Proof construction *************
 ************************************************)

exception Proof_impossible
exception Circular_sequent

let prove_equivalence (eq : equivalence) (prods : production_rules) =
  let pov = product_of_variables in
  let sov = sum_of_variable_rules in

  (* determine whether the first list is a prefix of the second list,
   * and if so, also return the remaining part of the second list *)
  let rec is_prefix = function
    | ([], postfix) -> (true, postfix)
    | (_::_, []) -> (false, [])
    | (h1::t1, h2::t2) -> if h1 = h2 then is_prefix (t1, t2) else (false, []) in

  let rewrite_with_grammar vh vt =
    let gr = rules_of_variable prods vh in
    sum_of_variable_rules (map (fun (t, v) -> (t, v@vt)) gr) in

  let rule_of_equivalence (a, b) =
    let trans x = Trans((a, x), (x, b)) in

    let rule_of_products (pah, pat) (pbh, pbt) =
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


    if expression_equals (a, b) then
      Refl
    else
      match a with
      | Product (pah, []) ->
        let gr = rewrite_with_grammar pah [] in
        if expression_equals (b, gr) then Gr
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
          | Sum(_, _) ->
            trans gr
        end
      | Product (pah, pat) ->
        begin match b with
        | Product (pbh, []) -> Sym(b, a)
        | Product (pbh, pbt) ->
          rule_of_products (pah, pat) (pbh, pbt)
        | Sum ((sbhc, []), []) ->
          raise Proof_impossible
        | Sum ((sbhc, sbhv), []) ->
          if norm_of_variable prods pah = 1 then
            Times((pov [pah], sum_of_terminal sbhc), (pov pat, pov sbhv))
          else
            trans (Product(variable_of_terminal prods sbhc, sbhv))
        | Sum(sbh, sbt) ->
          let gr = rewrite_with_grammar pah pat in
          if expression_equals (Sum(sbh, sbt), gr) then
            Times((pov [pah], rewrite_with_grammar pah []), (pov pat, pov pat))
          else
            trans gr
        end
      | Sum ((sahc, sahv), []) ->
        begin match b with
        | Product (_, _) -> Sym((b, a))
        | Sum ((sbhc, sbhv), []) ->
          if sahc = sbhc then
            Times(pair_map sum_of_terminal (sahc, sbhc), (pov sahv, pov sbhv))
          else
            raise Proof_impossible
        | Sum(_, _) ->
          raise Proof_impossible
        end
      | Sum ((sahc, sahv) as sah, sat) ->
        begin match b with
        | Product (_, _) -> Sym((b, a))
        | Sum (sbh, sbt) ->
          let (eq, noneq) = partition (fun (c, v) -> c = sahc) (sbh::sbt) in
          match eq with
          | eh::[] -> Plus((sov [sah], sov [eh]), (sov sat, sov noneq))
          | _ -> raise Proof_impossible
        end in

  let rec construct_proof seqs = function
    | [] -> seqs
    | (eqh::eqt) ->
      let rule = rule_of_equivalence eqh in
      let eqs = equivalences_of_rule rule in

      if mem eqh eqs then raise Circular_sequent
      else
        let unproven_eqs = filter
          (fun e -> not (exists (is_sequent_of_equivalence e) seqs)) eqs in
        construct_proof ((eqh, rule)::seqs) (unproven_eqs@eqt) in

  construct_proof [] [eq];;


(************************************************
 ****************** Main function ***************
 ************************************************)

let _ =
  (*let prods = Examples.branching_fibonacci_grammar 10 in*)
  let prods = Examples.recursive_grammar in

  if productions_valid prods then
    print_endline "Productions valid. :)"
  else begin
    print_endline "Productions invalid! :@";
    exit 1
  end;

  print_endline "Production rules:";
  print_endline (string_of_production_rules prods);

  (*print_endline ("Norm: " ^ (string_of_int (norm_of_variable prods "X10")));*)

  (*print_endline ("Decomposition: " ^
    string_of_variables (decompose prods 88 ["G10"]));*)

  let eq = pair_map product_of_variable ("X", "Y") in
  let sequents = prove_equivalence eq prods in

  print_endline "Proof:";
  print_sequents sequents;

  print_endline
    ("Proof size: " ^ string_of_int (length sequents) ^ " sequents");

  print_endline "LaTeX proof: ";
  print_endline (latex_of_sequents sequents eq);

  exit 0;
;;
