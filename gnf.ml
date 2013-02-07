open List;;

type variable_rule = char * int list;;
type variable_rules = variable_rule list;;
type production_rules = variable_rules list;;

type gnf = int * char list * production_rules;;

(* variable_rule -> string *)
let string_of_variable_rule = function
  (c, vars) ->
    fold_left (fun s v -> s ^ "X" ^ (string_of_int v)) (String.make 1 c) vars;;

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
	  ([j], i::(norm_reduce (norm i prods) [j] prods)) :: (addji j (i+1)) in
  addji 0 0;;

let print_int_list = iter (Printf.printf "%d ")

let main () =
  let prods = [[('a', []); ('a', [1])];
				  [('b', [0])]] in
  let test = norm_reduce 0 [1;1;1] prods in

  print_int_list test;
  print_endline "";

  print_endline "Production rules:";
  print_production_rules prods;

  for i = 0 to (length prods)-1 do
    Format.printf "Variable %d has norm: %d\n" i (norm i prods);
  done;
;;

main ();;
