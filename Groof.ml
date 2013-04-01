open Format;;
open List;;

open Grammar;;


(************************************************
 **************** Type definitions **************
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


(************************************************
 *************** Auxiliary functions ************
 ************************************************)

exception Empty_variables;;
exception Empty_variable_rules;;

let product_of_variable v = Product(v, []);;

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

exception Proof_impossible;;
exception No_partition;;

let prove_equivalence (eq : equivalence) (prods : production_rules) =
  let pov = product_of_variables in

  let partition f l =
    let rec aux prefix postfix =
      if f prefix then prefix, postfix
      else match postfix with
        | [] -> raise No_partition
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
            with No_partition ->
              try
                let a' = pov ((decompose prods npah (pbh::pbt))@pat) in
                e, Trans((a, a'), (a', b))
              with Not_decomposable ->
                let a' = pov (pbh::norm_reduce npbh [pah] prods @ pat) in
                e, Trans((a, a'), (a', b))
          else if npah = npbh then
            e, Times((pov [pah], pov [pbh]), (pov pat, pov pbt))
          else
            e, Sym(b, a)
        | Sum ((sbhc, sbhv), []) ->
          let rules = rules_of_variable pah prods in
          if length rules = 1 then
            let first_rule = hd rules in
            let a' = Sum((fst first_rule, (snd first_rule)@pat), []) in
            e, Trans((a, a'), (a', b))
          else
            raise Proof_impossible
        | _ -> e, Unsupported
        end
      | Sum ((sahc, sahv), []) ->
          begin match b with
          | Product (_, _) -> e, Sym((b, a))
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
  let prods = Examples.fibonacci_grammar 23 in

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
  print_sequents (prove_var_eq "F23" "G23" prods);

  exit 0;
;;
