open Format;;
open Gnf;;
open List;;

type expr = Product of variables | Sum of variable_rules;;
type equiv = expr * expr;;

type sequent = equiv * rule and rule =
    Refl
  | Gr
  | Unsupported
  | Sym   of sequent
  | Plus  of sequent * sequent
  | Times of sequent * sequent
  | Trans of sequent * sequent;;

let string_of_expr = function
  | Product p -> string_of_variables p
  | Sum s -> string_of_variable_rules s;;

let string_of_equiv = function (a, b) ->
  (string_of_expr a) ^ " = " ^ (string_of_expr b);;

let rec string_of_sequent = function (e, r) ->
  (string_of_equiv e) ^ " -> " ^ (string_of_rule r) and
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

let rec prove_eq e prods = match e with (a, b) ->
  if a = b then
    (a, b), Refl
  else match a with
    | Product [] -> raise Empty_product
	| Product (pah::[]) -> let gr = Sum(nth prods pah) in
        e, Trans(((a, gr), Gr), prove_eq (gr, b) prods)
	| Product (pah::pat) ->
	    begin match b with
		  | Product [] -> raise Empty_product
		  | Product (pbh::[]) -> e, Sym(prove_eq (b, a) prods)
		  | Product (pbh::pbt) -> e, Unsupported
		  | Sum [] -> raise Empty_sum
		  | _ -> e, Unsupported
		end
	| Sum [] -> raise Empty_sum
	| Sum ((sahc, sahv)::[]) ->
	    begin match b with
		  | Product [] -> raise Empty_product
		  | Product (pbh::[]) -> e, Sym(prove_eq (b, a) prods)
		  | Product (pbhd::patl) -> raise Proof_impossible
		  | Sum [] -> raise Empty_sum
		  | Sum ((sbhc, sbhv)::[]) ->
			  if sahc = sbhc then
				let sum_of_char c = Sum([(c, [])]) in
				e, Times(((sum_of_char sahc, sum_of_char sbhc), Refl),
						 prove_eq (Product(sahv), Product(sbhv)) prods)
	          else
				raise Proof_impossible
		  | Sum (sbhd::sbtl) -> raise Proof_impossible
		end
	| Sum (sahd::satl) -> e, Unsupported;;

let prove_var_eq a b = prove_eq (Product [a], Product [b]);;

let _ =
  let p0 = [[('a', [])]; [('a', [])]] in
  let p1 = [[('a', [1; 3])]; [('a', [2])]; [('b', [])]; [('c', [])];
            [('a', [5; 7])]; [('a', [])]; [('c', [])]; [('b', [6])]] in
  let ps = [p0; p1] in
  let prods = nth ps 1 in

  let proof = prove_var_eq 0 4 prods in
  print_string "Proof: ";
  print_endline (string_of_sequent proof);
;;
