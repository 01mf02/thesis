open Format;;
open Gnf;;
open List;;

type expression = Product of variables | Sum of variable_rules;;
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
  | Product p -> string_of_variables p
  | Sum s -> string_of_variable_rules s;;

let string_of_equivalence = function (a, b) ->
  (string_of_expression a) ^ " = " ^ (string_of_expression b);;

let rec string_of_sequent = function (e, r) ->
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


exception Empty_product;;
exception Empty_sum;;
exception Proof_impossible;;

let prove_equivalence eq prods base =
  let partition v1 v2 =
    let norm_vars vars = fold_left (fun s v -> s + (norm v prods)) 0 in

    let rec partition' v11 v12 v21 v22 =
      (* TODO: check if first variables of v12 and v22 didn't appear yet in
         proof before *)
      if base_equals base v11 v21 then
        (v11, v12, v21, v22)
      else if norm_vars v11 < norm_vars v21 then
        match v12 with
          | [] -> raise Empty_product
          | hd::tl -> partition' (v11@[hd]) tl v21 v22
      else if norm_vars v11 > norm_vars v21 then
        match v22 with
          | [] -> raise Empty_product
          | hd::tl -> partition' v11 v12 (v21@[hd]) tl
      else raise Proof_impossible in
    partition' [] v1 [] v2 in

  let rec prove_eq e = match e with (a, b) ->
    if a = b then
      (a, b), Refl
    else match a with
      | Product [] -> raise Empty_product
      | Product (pah::[]) -> let gr = Sum(nth prods pah) in
          e, Trans(((a, gr), Gr), prove_eq (gr, b))
      | Product (pah::pat) ->
          begin match b with
            | Product [] -> raise Empty_product
            | Product (pbh::[]) -> e, Sym(prove_eq (b, a))
            | Product (pbh::pbt) -> e, Unsupported
            | Sum [] -> raise Empty_sum
            | _ -> e, Unsupported
          end
      | Sum [] -> raise Empty_sum
      | Sum ((sahc, sahv)::[]) ->
          begin match b with
            | Product [] -> raise Empty_product
            | Product (pbh::[]) -> e, Sym(prove_eq (b, a))
            | Product (pbh::pat) -> raise Proof_impossible
            | Sum [] -> raise Empty_sum
            | Sum ((sbhc, sbhv)::[]) ->
                if sahc = sbhc then
                  let sum_of_char c = Sum([(c, [])]) in
                  e, Times(((sum_of_char sahc, sum_of_char sbhc), Refl),
                           prove_eq (Product(sahv), Product(sbhv)))
                else
                  raise Proof_impossible
            | Sum (sbh::sbt) -> raise Proof_impossible
          end
      | Sum (sah::sat) -> e, Unsupported in

  prove_eq eq;;

let prove_var_eq a b = prove_equivalence (Product [a], Product [b]);;

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
