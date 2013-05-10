open Format;;
open List;;

open Grammar;;
open Groof;;


(************************************************
 ********************** Tests *******************
 ************************************************)

let tests =
  print_endline "Testing if invalid proof is denied ...";
  let crazy_proof =
    [((Product("A", []), Product("B", [])),
      Sym(Product("B", []), Product("A", [])));
     ((Product("B", []), Product("A", [])),
      Sym(Product("A", []), Product("B", [])))] in
  if verify_proof crazy_proof then
    print_endline "Test failed!"
  else
    print_endline "Test passed!";;


(************************************************
 *************** Auxiliary functions ************
 ************************************************)

(* returns [i; i+1; ...; j] *)
let rec range i j = if i > j then [] else i::(range (i+1) j);;


(************************************************
 ****************** Main function ***************
 ************************************************)

let procedure prods vars enable_decomposition =
  print_newline ();

  if false then begin
    print_endline "Production rules:";
    print_endline (string_of_production_rules prods)
  end;

  print_endline "Calculating norms and checking if productions are valid ...";
  let gram = grammar_of_production_rules prods in
  print_endline "Productions valid. :)";

  let mode = if enable_decomposition then "with" else "without" in
  print_endline ("Constructing proof " ^ mode ^ " decomposition ... ");
  let eq = pair_map product_of_variable vars in
  let seqs = prove_equivalence eq gram enable_decomposition in

  if false then begin
    print_endline "Proof:";
    print_sequents seqs
  end;

  if false then begin
    print_endline "LaTeX proof: ";
    print_endline (latex_of_sequents seqs eq)
  end;

  print_endline "Done.";
  let n_sequents = length seqs in
  let n_symbols = sum (map size_of_sequent seqs) in
  print_endline ("Proof size: " ^
    string_of_int (n_sequents) ^ " sequents with " ^
    string_of_int (n_symbols ) ^ " symbols");

  if false then begin
    print_endline "Verifying proof ...";
    if verify_proof seqs then
      print_endline "Proof valid. :)"
    else begin
      print_endline "Proof invalid!";
      exit 1
    end
  end;

  (n_sequents, n_symbols);;

let calc_proof_sizes prods vars_f max_i enable_decomposition =
  map (fun i ->
    let vars = vars_f (string_of_int i) in
    (i, procedure prods vars enable_decomposition)) (range 1 max_i);;

let save_proof_sizes sizes filename =
  print_newline ();
  print_endline ("Writing " ^ filename ^ " ...");

  let output = open_out filename in
  let lines =
    map (fun (n, (seq, sym)) ->
      (String.concat " " (map string_of_int [n; seq; sym])) ^ "\n") sizes in
  iter (output_string output) lines;
  close_out output;

  print_endline "Done.";;

let _ =
  tests;

  let n0 = 25 in
  let n1 = 25 in
  let n2 = 25 in
  let n3 = 25 in
  let n4 = 1 in
  let ns = [n0; n1; n2; n3; n4] in

  let p0 = Examples.ab_grammar ['a'] ['b'] n0 in
  let p1 = Examples.power_two_grammar n1 in
  let p2 = Examples.branching_fibonacci_grammar n2 in
  let p3 = Examples.ab_grammar ['a'; 'b'] ['b'; 'a'] n3 in
  let p4 = Examples.recursive_grammar in
  let ps = [p0; p1; p2; p3; p4] in

  let v0 = fun i -> ("F" ^ i, "G" ^ i) in
  let v1 = fun i -> ("S" ^ i, "T" ^ i) in
  let v2 = fun i -> ("X" ^ i, "Y" ^ i) in
  let v3 = fun i -> ("F" ^ i, "G" ^ i) in
  let v4 = fun i -> ("X", "Y") in
  let vs = [v0; v1; v2; v3; v4] in

  let es = combine (combine ps vs) ns in

  for e = 0 to (length es) - 1 do
    let ((p, v), n) = nth es e in
    iter (fun enable_decomposition ->
      let proof_sizes = calc_proof_sizes p v n enable_decomposition in

      let prefix = "sizes_" ^ if enable_decomposition then "d" else "b" in
      let filename = (prefix ^ (string_of_int e) ^ ".dat") in

      save_proof_sizes proof_sizes filename) [true; false];
  done;

  exit 0;
;;
