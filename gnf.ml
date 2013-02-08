open List;;

type variable = int;;
type variables = variable list;;
type variable_rule = char * variables;;
type variable_rules = variable_rule list;;
type production_rules = variable_rules list;;

type gnf = int * char list * production_rules;;

(* variable -> string *)
let string_of_variable var =
  "X" ^ string_of_int var;;

(* variables -> string *)
let string_of_variables vars =
  String.concat "" (map string_of_variable vars);;

(* variable_rule -> string *)
let string_of_variable_rule = function
  (c, vars) -> (String.make 1 c) ^ string_of_variables vars;;

(* variable_rules -> string *)
let string_of_variable_rules r =
  String.concat " | " (map string_of_variable_rule r);;

(* production_rules -> unit *)
let print_production_rules r =
  for i = 0 to (length r)-1 do
    Format.printf "X%d -> %s\n" i (string_of_variable_rules (nth r i));
  done;;

(* calculate the norm of the i-th variable of a grammar *)
(* int -> production_rules -> int *)
let rec norm i prods =
  let vars = snd (hd (nth prods i)) in
  fold_left (fun prev_sum var -> prev_sum + (norm var prods)) 1 vars;;

exception Negative_norm_reduce

(* int -> int list -> production_rules -> int list *)
let rec norm_reduce p vars prods =
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
		  let first_production = snd (hd (nth prods head)) in
		  (norm_reduce (p - 1) first_production prods) @ tail;;

let initial_base prods =
  let n = length prods in
  let rec addji j i =
    if j >= n then
	  []
	else if i > j then
	  addji (j + 1) 0
	else
	  (j, i, (norm_reduce (norm i prods) [j] prods)) :: (addji j (i+1)) in
  addji 0 0;;

(* return first n elements of a list *)
(* 'a list -> 'a list *)
let rec first_n n = function
  | [] -> []
  | head::tail -> if n > 0 then head::(first_n (n-1) tail) else [];;

let base_equals base a b =
  let rec be g =
    let to_list = function (i, rest) -> i::rest in
    let gstar = fold_left (fun prev curr -> prev @ to_list (g curr)) [] in
	let gsa = gstar a and gsb = gstar b in
	if gsa = gsb then
	  true
	else
	  let min_len = min (length gsa) (length gsb) in
	  let gsa_cut = first_n min_len gsa in
	  let gsb_cut = first_n min_len gsb in
	  let gsab_cut = (combine gsa_cut gsb_cut) in
	  try
	    let mismatch = find (function (x,y) -> x <> y) gsab_cut in
	    match mismatch with (ma, mb) ->
	      let (i, j) = (min ma mb, max ma mb) in
		  let elem = find (function (x,y,_) -> x = j && y = i) base in
		  match elem with (_, _, rest) ->
			be (fun x -> if x = j then (i, rest) else g x)
	  with Not_found ->
		false in

  be (fun x -> (x, []));;


let rec range i j = if i > j then [] else i :: (range (i+1) j)

let rec refine_base base prods =
  let valid_pair = function (j, i, rest) ->
	  let check p q =
	    let vjq = nth (nth prods j) q in
		let vip = nth (nth prods i) p in
		fst vjq = fst vip && base_equals base (snd vjq) ((snd vip)@rest) in
	
	  let range_j = range 0 ((length (nth prods j))-1) in
	  let range_i = range 0 ((length (nth prods i))-1) in

	  for_all (fun q -> exists (fun p -> check p q) range_i) range_j &&
	  for_all (fun p -> exists (fun q -> check p q) range_j) range_i in

  let refined = filter valid_pair base in
  if base = refined then
    base
  else
    refine_base refined prods;;


let string_of_base b = String.concat ","
  (map (function (j,i,rest) ->
		"(" ^ (string_of_variable j) ^ "," ^
		(string_of_variable i) ^ (string_of_variables rest) ^ ")") b);;

let main () =
  (* let prods = [[('a', []); ('a', [1])];
               [('b', [0])]] in *)
  let prods = [[('a', []); ('a', [0])];
               [('a', []); ('a', [1]); ('a', [2])];
			   [('a', [])]] in
  
  let nr_test = norm_reduce 0 [1;1;1] prods in
  let i_base = initial_base prods in
  let r_base = refine_base i_base prods in

  print_endline "Production rules:";
  print_production_rules prods;

  for i = 0 to (length prods)-1 do
    Format.printf "Variable %d has norm: %d\n" i (norm i prods);
  done;

  print_endline "Initial base:";
  print_endline (string_of_base i_base);

  print_endline "Refined base:";
  print_endline (string_of_base r_base);

  print_endline "Test of norm_reduce:";
  print_endline (string_of_variables nr_test);
;;

main ();;
