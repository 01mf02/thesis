open List;;


(************************************************
 **************** Example grammars **************
 ************************************************)

let zero_variables = map (fun (v, c) -> (v, [(c, [])]));;
let one_variable = map (fun (v, c, v1) -> (v, [(c, [v1])]));;
let two_variables = map (fun (v, c, v1, v2) -> (v, [(c, [v1; v2])]));;
let soi = string_of_int;;

let rec ab_grammar n =
  let unequal_var vu ve t vt = function
    | 0 -> one_variable [(vu ^ "0", t, vt)]
    | n -> one_variable [(vu ^ soi n, t, ve ^ soi n)] in

  let equal_var ve vu t = function
    | 0 -> []
    | n -> two_variables [(ve ^ soi n, t, vu ^ soi (n-1), vu ^ soi (n-1))] in

  let ab = unequal_var "AB" "BB" 'a' "B" in
  let ba = unequal_var "BA" "AA" 'b' "A" in
  let aa = equal_var "AA" "BA" 'a' in
  let bb = equal_var "BB" "AB" 'b' in

  let fg n = two_variables [("F" ^ soi n, 'a', "B", "AB" ^ soi n);
                            ("G" ^ soi n, 'a', "BA" ^ soi n, "B")] in

  match n with
    | 0 -> zero_variables [("A", 'a'); ("B", 'b')] @ ab 0 @ ba 0 @ fg 0
    | n -> ab_grammar (n-1) @ aa n @ bb n @ ab n @ ba n @ fg n;;


let rec power_two_grammar n =
  let nonprime_var v vf1 vf2 = function
    | 0 -> zero_variables [(v ^ "0", 'a')]
    | 1 -> one_variable [(v ^ "1", 'a', v ^ "0")]
    | n -> let p = soi (n-1) in
           two_variables [(v ^ soi n, 'a', vf1 p, vf2 p)] in

  let prime_var v = function
    | 0 -> []
    | 1 -> zero_variables [(v ^ "1'", 'a')]
    | n -> let pp = v ^ soi (n-1) ^ "'" in
           two_variables [(v ^ soi n ^ "'", 'a', pp, pp)] in

  let s = nonprime_var "S" (fun p -> "S" ^ p) (fun p -> "S" ^ p ^ "'") in
  let t = nonprime_var "T" (fun p -> "T" ^ p ^ "'") (fun p -> "T" ^ p) in
  let s' = prime_var "S" in
  let t' = prime_var "T" in

  match n with
    | 0 -> s 0 @ t 0
    | n -> power_two_grammar (n-1) @ s' n @ t' n @ s n @ t n;;


let rec fibonacci_grammar n =
  let nonprime_var v vf1 vf2 = function
    | 0 -> zero_variables [(v ^ "0", 'a')]
    | 1 -> zero_variables [(v ^ "1", 'a')]
    | 2 -> one_variable [(v ^ "2", 'a', v ^ "0")]
    | n -> two_variables [(v ^ soi n, 'a', vf1 n, vf2 n)] in

  let prime_var v vf1 vf2 = function
    | 0 -> []
    | 1 -> []
    | 2 -> zero_variables [(v ^ "2'", 'a')]
    | 3 -> one_variable [(v ^ "3'", 'a', v ^ "2'")]
    | n -> two_variables [(v ^ soi n ^ "'", 'a', vf1 n, vf2 n)] in

  let f = nonprime_var "F"
    (fun n -> "F" ^ soi (n-2)) (fun n -> "F" ^ soi (n-1) ^ "'") in
  let g = nonprime_var "G"
    (fun n -> "G" ^ soi (n-1) ^ "'") (fun n -> "G" ^ soi (n-2)) in

  let f' = prime_var "F"
    (fun n -> "F" ^ soi (n-2) ^ "'") (fun n -> "F" ^ soi (n-1) ^ "'") in
  let g' = prime_var "G"
    (fun n -> "G" ^ soi (n-1) ^ "'") (fun n -> "G" ^ soi (n-2) ^ "'") in

  match n with
    | 0 -> f 0 @ g 0
    | n -> fibonacci_grammar (n-1) @ f' n @ g' n @ f n @ g n;;

let rec branching_grammar fx fy n =
  let rec summands v f = function
    | 0 -> [('a', [])]
    | n -> (Char.chr (n + 97), (f n) @ [v ^ soi n])::summands v f (n-1) in

  let var v f = function
    | 0 -> []
    | n -> [(v ^ soi n, rev (summands v f (n-1)))] in

  let x = var "X" fx in
  let y = var "Y" fy in

  match n with
  | 0 -> []
  | 1 -> x 1 @ y 1
  | n -> (branching_grammar fx fy (n-1)) @ x n @ y n;;


let branching_fibonacci_grammar n =
  branching_grammar (fun n -> ["F" ^ soi n]) (fun n -> ["G" ^ soi n]) n @
  fibonacci_grammar n;;


let recursive_grammar =
  [("X", [('a', []); ('b', ["X"])]);
   ("Y", [('a', []); ('b', ["Y"])])];;
