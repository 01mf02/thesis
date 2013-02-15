open Format;;
open Gnf;;
open List;;

type expression =
    Product of variable * variables
  | Sum of variable_rule * variable_rules;;

type equivalence = expression * expression;;

type sequent = equivalence * rule and rule =
    Refl
  | Gr
  | Unsupported
  | Sym   of sequent
  | Plus  of sequent * sequent
  | Times of sequent * sequent
  | Trans of sequent * sequent;;

let string_of_expression = function
  | Product (ph, pt) -> string_of_variables (ph::pt)
  | Sum (sh, st) -> string_of_variable_rules (sh::st);;

let string_of_equivalence (a, b) =
  (string_of_expression a) ^ " = " ^ (string_of_expression b);;

let rec string_of_sequent (e, r) =
  (string_of_equivalence e) ^ " -> " ^ (string_of_rule r) and
string_of_sequents seqs = String.concat ", " (map string_of_sequent seqs) and
string_of_rule = function
  | Refl -> "Refl"
  | Gr -> "Gr"
  | Unsupported -> "Unsupported"
  | Sym s -> "Sym(" ^ (string_of_sequent s) ^ ")"
  | Plus  (s1, s2) -> "Plus("  ^ (string_of_sequents [s1; s2]) ^ ")"
  | Times (s1, s2) -> "Times(" ^ (string_of_sequents [s1; s2]) ^ ")"
  | Trans (s1, s2) -> "Trans(" ^ (string_of_sequents [s1; s2]) ^ ")";;


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



let prove_equivalence eq prods base =
  let pov = product_of_variables in

  let partition a b =
    let norm_vars = fold_left (fun s v -> s + (norm v prods)) 0 in

    let rec partition' a1 a2 b1 b2 =
      (* TODO: check if first variables of a2 and b2 did not appear yet in
         proof before *)
      let initial = a1 = [] && b1 = [] in
      if not initial && base_equals base a1 b1 then
        (a1, a2, b1, b2)
      else if norm_vars a1 < norm_vars b1 || initial then
        match a2 with
          | [] -> raise Empty_variables
          | hd::tl -> partition' (a1@[hd]) tl b1 b2
      else if norm_vars a1 > norm_vars b1 then
        match b2 with
          | [] -> raise Empty_variables
          | hd::tl -> partition' a1 a2 (b1@[hd]) tl
      else raise Proof_impossible in
    partition' [] a [] b in

  let rec prove_eq e = match e with (a, b) ->
    if a = b then
      (a, b), Refl
    else match a with
      | Product (pah, []) -> let gr = sum_of_variable_rules (nth prods pah) in
          e, Trans(((a, gr), Gr), prove_eq (gr, b))
      | Product (pah, pat) ->
          begin match b with
            | Product (pbh, []) -> e, Sym(prove_eq (b, a))
            | Product (pbh, pbt) ->
                let (pa1, pa2, pb1, pb2) = partition (pah::pat) (pbh::pbt) in
                if (pa2 = [] && pb2 = []) then
                  e, Unsupported
                else
                  e, Times(prove_eq (pov pa1, pov pb1),
                           prove_eq (pov pa1, pov pb1))
            | _ -> e, Unsupported
          end
      | Sum ((sahc, sahv), []) ->
          begin match b with
            | Product (pbh, []) -> e, Sym(prove_eq (b, a))
            | Product (pbh, pat) -> raise Proof_impossible
            | Sum ((sbhc, sbhv), []) ->
                if sahc = sbhc then
                  let sum_of_terminal t = Sum((t, []), []) in
                  e, Times(((sum_of_terminal sahc, sum_of_terminal sbhc), Refl),
                           prove_eq (pov sahv, pov sbhv))
                else
                  raise Proof_impossible
            | Sum (sbh, sbt) -> raise Proof_impossible
          end
      | Sum (sah, sat) -> e, Unsupported in

  prove_eq eq;;

let prove_var_eq a b =
  prove_equivalence (product_of_variable a, product_of_variable b);;

let _ =
  let p0 = [[('a', [])]; [('a', [])]] in
  let p1 = [[('a', [])]; [('b', [])]; [('c', [])];
            [('a', [1])]; [('b', [2])];
            [('a', [3; 2])]; [('a', [0; 4])]] in
  let ps = [p0; p1] in
  let prods = nth ps 1 in

  let base = refine_base (initial_base prods) prods in
  let proof = prove_var_eq 5 6 prods base in
  print_string "Proof: ";
  print_endline (string_of_sequent proof);
;;
