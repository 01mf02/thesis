open Big_int;;
open Format;;
open List;;

open Grammar;;


(************************************************
 **************** Type definitions **************
 ************************************************)

type expression =
  | Product of variable * variables
  | Sum of t_rule * t_rules;;

type equivalence = expression * expression;;

type sequent = equivalence * rule and rule =
  | Refl
  | Gr
  | Sym   of equivalence
  | Plus  of equivalence * equivalence
  | Times of equivalence * equivalence
  | Trans of equivalence * equivalence;;

type strategy =
  | Base
  | Decomposition;;


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
  | Refl
  | Gr -> []
  | Sym e -> [e]
  | Plus  (e1, e2)
  | Times (e1, e2)
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

let sequent_of_equivalence seqs eq =
  find (fun (eq', _) -> eq = eq') seqs;;

let exists_sequent_of_equivalence seqs eq =
  exists (fun (eq', _) -> eq = eq') seqs;;

let sequents_of_rule seqs rl =
  map (sequent_of_equivalence seqs) (equivalences_of_rule rl);;

let size_of_variable_rule (term, vars) = 1 + length vars;;

let sum = fold_left (+) 0;;

let size_of_expression = function
  | Product (_, vt) -> 1 + length vt
  | Sum (rh, rt) ->
    (size_of_variable_rule rh) + (sum (map size_of_variable_rule rt));;

let size_of_equivalence (ex1, ex2) =
  size_of_expression ex1 + size_of_expression ex2;;

let size_of_sequent (eq, _) = size_of_equivalence eq;;


(************************************************
 *************** Printing functions *************
 ************************************************)

let string_of_expression = function
  | Product (ph, pt) -> string_of_variables (ph::pt)
  | Sum (sh, st) -> string_of_t_rules (sh::st);;

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
      let (_, r) = sequent_of_equivalence seqs eq in
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

let prove_equivalence (eq : equivalence) (gram : grammar) (strat : strategy) =
  let pov = product_of_variables in
  let sov = sum_of_variable_rules in
  let (prods, norms) = gram in

  (* determine whether the first list is a prefix of the second list,
   * and if so, also return the remaining part of the second list *)
  let rec is_prefix = function
    | ([], postfix) -> (true, postfix)
    | (_::_, []) -> (false, [])
    | (h1::t1, h2::t2) -> if h1 = h2 then is_prefix (t1, t2) else (false, []) in

  let rewrite_with_grammar vh vt =
    let gr = assoc vh prods in
    sum_of_variable_rules (map (fun (t, v) -> (t, v@vt)) gr) in

  let rule_of_equivalence (a, b) =
    let trans x = Trans((a, x), (x, b)) in

    let rule_of_products (pah, pat) (pbh, pbt) =
      let (npah, npbh) = pair_map (norm_of_variable norms) (pah, pbh) in

      if lt_big_int npah npbh then
        Sym(b, a)
      else
        let base_repl = pbh::norm_reduce npbh [pah] gram in
        let pah_repl = match strat with
          | Base -> base_repl
          | Decomposition ->
            try decompose gram npah (pbh::pbt)
            with Not_decomposable -> base_repl in

          let (repl_is_prefix, postfix) = is_prefix (pah_repl, (pbh::pbt)) in
          if repl_is_prefix then
            Times((pov [pah], pov pah_repl), (pov pat, pov postfix))
          else
          trans (pov (pah_repl@pat)) in


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
            let (npah, npbh) = pair_map (norm_of_variable norms) (pah, pbh) in
            if le_big_int npah npbh then
              raise Proof_impossible
            else begin
              let reduct = pbh::norm_reduce npbh [pah] gram in
              if reduct = pbh::pbt then trans gr
              else trans (pov reduct)
            end
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
          if eq_big_int (norm_of_variable norms pah) unit_big_int then
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
      | Sum ((sahc, []), []) ->
        begin match b with
        | Product (_, []) -> Sym((b, a))
        | _ -> raise Proof_impossible
        end
      | Sum ((sahc, sahv), []) ->
        begin match b with
        | Product (_, _) -> Sym((b, a))
        | Sum ((sbhc, []), []) -> Sym((b, a))
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
        | Sum (sbh,  []) -> Sym((b, a))
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
          (fun e -> not (exists_sequent_of_equivalence seqs e)) eqs in
        construct_proof ((eqh, rule)::seqs) (unproven_eqs@eqt) in

  construct_proof [] [eq];;


(************************************************
 *************** Proof verification *************
 ************************************************)

let verify_proof seqs =

  let unique_conclusions =
    for_all (fun (e1, r1) -> for_all (fun (e2, r2) ->
      if e1 = e2 then r1 = r2 else true) seqs) seqs in

  let rec premstartimes acc = function
    | (_, Times (_)) -> acc
    | (eq, rl) as seq ->
      if mem seq acc then
        acc
      else
        fold_left premstartimes (seq::acc) (sequents_of_rule seqs rl) in

  let conclusions_proved =
    for_all (fun seq ->
      let premises = equivalences_of_rule (snd seq) in
      for_all (fun eq ->
        let sp = sequent_of_equivalence seqs eq in
        not (mem seq (premstartimes [] sp))) premises) seqs in

  unique_conclusions && conclusions_proved;;
