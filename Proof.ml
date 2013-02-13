open Format;;
open Gnf;;
open List;;

type expr = Product of variables | Sum of variable_rules;;
type equiv = expr * expr;;

type sequent = equiv * rule and rule =
    Refl
  | Gr
  | Sym   of sequent
  | Trans of sequent * sequent;;

let string_of_expr = function
  | Product p -> string_of_variables p
  | Sum s -> string_of_variable_rules s;;

let string_of_equiv = function (a, b) ->
  (string_of_expr a) ^ " = " ^ (string_of_expr b);;

let rec string_of_sequent = function (e, r) ->
  (string_of_equiv e) ^ " -> " ^ (string_of_rule r) and
string_of_rule = function
  | Refl -> "Refl"
  | Gr -> "Gr"
  | Sym s -> "Sym(" ^ (string_of_sequent s) ^ ")"
  | Trans (s1, s2) -> "Trans(" ^
    (string_of_sequent s1) ^ ", " ^ (string_of_sequent s2) ^ ")";;


exception Unsupported;;
exception Empty_product;;
exception Empty_sum;;
exception Proof_impossible;;

let rec prove_eq e prods = match e with (a, b) ->
  if a = b then
    (a, b), Refl
  else match a with
    | Product pa ->
	  begin match pa with
	    | [] -> raise Empty_product
	    | pahd::[] -> let gr = Sum(nth prods pahd) in
          e, Trans(((a, gr), Gr), prove_eq (gr, b) prods)
	    | pahd::patl -> raise Unsupported
	  end
	| Sum sa ->
	  begin match sa with
	    | [] -> raise Empty_sum
		| sahd::[] ->
		  begin match b with
		    | Product pb ->
		      begin match pb with
			    | [] -> raise Empty_sum
		        | pbhd::[] -> let gr = Sum(nth prods pbhd) in
				  e, Trans(prove_eq (a, gr) prods, ((gr, b), Sym((b, gr), Gr)))
			    | pbhd::patl -> raise Proof_impossible
			  end
		    | Sum sb -> raise Unsupported
		  end
		| sahd::satl -> raise Unsupported
	  end;;

let prove_var_eq a b = prove_eq (Product [a], Product [b]);;

let _ =
  let prods = [[('a', [])]; [('a', [])]] in
  let proof = prove_var_eq 0 1 prods in
  print_string "Proof: ";
  print_endline (string_of_sequent proof);
;;
