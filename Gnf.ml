open List;;


(************************************************
 **************** Type definitions **************
 ************************************************)

type variable = int;;
type variables = variable list;;
type variable_rule = char * variables;;
type variable_rules = variable_rule list;;
type production_rules = variable_rules list;;

type base = (variable * variable * variables) list;;


(************************************************
 *************** Printing functions *************
 ************************************************)

(* variable -> string *)
let string_of_variable (var : variable) =
  "X" ^ string_of_int var;;

(* variables -> string *)
let string_of_variables (vars : variables) =
  String.concat "" (map string_of_variable vars);;

(* variable_rule -> string *)
let string_of_variable_rule = function
  (c, vars) -> (String.make 1 c) ^ string_of_variables vars;;

(* variable_rules -> string *)
let string_of_variable_rules (r : variable_rules) =
  String.concat " | " (map string_of_variable_rule r);;

(* production_rules -> string *)
let string_of_production_rules (r : production_rules) =
  let rec aux i rules = match rules with
  | [] -> []
  | head::tail ->
    (Format.sprintf "X%d -> %s" i (string_of_variable_rules head))::
    (aux (i+1) tail) in
  String.concat "\n" (aux 0 r);;

(* base -> string *)
let string_of_base (bs : base) = String.concat ","
  (map (function (j,i,rest) ->
        "(" ^ (string_of_variable j) ^ "," ^
        (string_of_variable i) ^ (string_of_variables rest) ^ ")") bs);;


(************************************************
 *************** Auxiliary functions ************
 ************************************************)

(* return first n elements of a list *)
(* int -> 'a list -> 'a list *)
let rec first_n n = function
  | [] -> []
  | head::tail -> if n > 0 then head::(first_n (n-1) tail) else [];;

(* take two lists, shorten them to length of smaller list and combine them *)
(* 'a list -> 'a list -> ('a * 'a) list *)
let equalize_combine l1 l2 =
  let min_len = min (length l1) (length l2) in
  let l1_cut = first_n min_len l1 in
  let l2_cut = first_n min_len l2 in
  (combine l1_cut l2_cut);;

(* construct a list of integers [i; i+1; ... ; j] *)
(* int -> int -> int list *)
let rec range i j = if i > j then [] else i::(range (i+1) j);;


(************************************************
 ***************** Norm functions ***************
 ************************************************)

(* calculate the norm of a variable of a grammar *)
(* variable -> production_rules -> int *)
let rec norm (v : variable) (prods : production_rules) =
  let vars = snd (hd (nth prods v)) in
  fold_left (fun prev_sum curr_var -> prev_sum + (norm curr_var prods)) 1 vars;;

exception Negative_norm_reduce

(* int -> variables -> production_rules -> int list *)
let rec norm_reduce (p : int) (vars : variables) (prods : production_rules) =
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

(* verify that production rules adhere to required restrictions:
   * for all variables X_i in the production rules, norm(X_i) <= norm(X_(i+1))
   * the first rule for each variable generates a norm-reducing transition,
     i.e. norm(X_i) < norm(alpha_i1) *)
(* production_rules -> bool *)
let productions_valid (prods : production_rules) =
  let rec is_sorted curr_var max_var prev_norm =
    if curr_var = max_var then
      true
    else
      let curr_norm = norm curr_var prods in
      if curr_norm >= prev_norm &&
      for_all (fun v -> v < curr_var) (snd (hd (nth prods curr_var))) then
        is_sorted (curr_var+1) max_var curr_norm
      else false in
  is_sorted 0 (length prods) 0;;
  

(************************************************
 ***************** Base functions ***************
 ************************************************)

exception Invalid_productions

(* production_rules -> base *)
let initial_base (prods : production_rules) =
  if not (productions_valid prods) then
    raise Invalid_productions
  else
    let n = length prods in
    let rec addji j i =
      if j >= n then
        []
      else if i > j then
        addji (j + 1) 0
      else
        (j, i, (norm_reduce (norm i prods) [j] prods)) :: (addji j (i+1)) in
    addji 0 0;;

(* compute equality of two variable lists with respect to a certain base *)
(* base -> variables -> variables -> bool *)
let base_equals (bs : base) (a : variables) (b : variables) =
  let rec base_eq (g : variable -> variable * variable list) =
    let to_list = function (i, rest) -> i::rest in
    let gstar = fold_left (fun prev curr -> prev @ to_list (g curr)) [] in
    let ga = gstar a and gb = gstar b in
    if ga = gb then
      true
    else
      let gab = equalize_combine ga gb in
      try
        let mismatch = find (function (x,y) -> x <> y) gab in
        match mismatch with (ma, mb) ->
          let (i, j) = (min ma mb, max ma mb) in
          let elem = find (function (x,y,_) -> x = j && y = i) bs in
          match elem with (_, _, rest) ->
            base_eq (fun x -> if x = j then (i, rest) else g x)
      with Not_found ->
        false in

  base_eq (fun x -> (x, []));;


let rec refine_base (bs : base) (prods : production_rules) =
  let valid_pair = function (j, i, rest) ->
      let check p q =
        let vjq = nth (nth prods j) q in
        let vip = nth (nth prods i) p in
        fst vjq = fst vip && base_equals bs (snd vjq) ((snd vip)@rest) in
    
      let range_j = range 0 ((length (nth prods j))-1) in
      let range_i = range 0 ((length (nth prods i))-1) in

      for_all (fun q -> exists (fun p -> check p q) range_i) range_j &&
      for_all (fun p -> exists (fun q -> check p q) range_j) range_i in

  print_endline ("Refine base: " ^ (string_of_base bs));

  let refined = filter valid_pair bs in
  if bs = refined then
    bs
  else
    refine_base refined prods;;


(************************************************
 ****************** Main function ***************
 ************************************************)

let _ =
  (* X0 -> a | aX1, X1 -> bX0 *)
  let p0 = [[('a', []); ('a', [1])];
            [('b', [0])]] in
  (* X0 -> a | bX1, X1 -> a | bX0 *)
  let p1 = [[('a', []); ('b', [1])];
            [('a', []); ('b', [0])]] in
  (* X0 -> a | aX0, X1 -> a | aX1 | aX2, X2 -> a *)
  let p2 = [[('a', []); ('a', [0])];
            [('a', []); ('a', [1]); ('a', [2])];
            [('a', [])]] in
  (* X0 -> c | aX0X1, X1 -> b, X2 -> c | aX2X3, X3 -> b *)
  let p3 = [[('c', []); ('a', [0; 1])];
            [('b', [])];
            [('c', []); ('a', [2; 3])];
            [('b', [])]] in

  let ps = [p0; p1; p2; p3] in
  let prods = nth ps 3 in

  
  print_endline "Production rules:";
  print_endline (string_of_production_rules prods);

  for i = 0 to (length prods)-1 do
    Format.printf "Variable %d has norm: %d\n" i (norm i prods);
  done;

  let i_base = initial_base prods in
  print_string "Initial base: ";
  print_endline (string_of_base i_base);

  let r_base = refine_base i_base prods in
  print_string "Refined base: ";
  print_endline (string_of_base r_base);

  let nontrivial_equivalences = filter
    (fun x -> match x with (j, i, rest) -> j <> i || rest <> []) in

  let nte = nontrivial_equivalences r_base in
  print_string "Nontrivial equivalences: ";
  print_endline (string_of_base nte);

  let nr_test = norm_reduce 0 [1;1;1] prods in
  print_string "Test of norm_reduce: ";
  print_endline (string_of_variables nr_test);
;;
