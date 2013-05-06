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
 ****************** Main function ***************
 ************************************************)

let procedure prods vars =
  print_newline ();

  if false then begin
    print_endline "Production rules:";
    print_endline (string_of_production_rules prods)
  end;

  print_endline "Calculating norms and checking if productions are valid ...";
  let gram = grammar_of_production_rules prods in
  print_endline "Productions valid. :)";

  print_endline "Constructing proof ... ";
  let eq = pair_map product_of_variable vars in
  let seqs = prove_equivalence eq gram in

  if false then begin
    print_endline "Proof:";
    print_sequents seqs
  end;

  if false then begin
    print_endline "LaTeX proof: ";
    print_endline (latex_of_sequents seqs eq)
  end;

  print_endline "Done.";
  print_endline ("Proof size: " ^ string_of_int (length seqs) ^ " sequents");

  print_endline "Verifying proof ...";
  if verify_proof seqs then
    print_endline "Done."
  else begin
    print_endline "Proof invalid!";
    exit 1
  end;;


let _ =
  tests;

  let p0 = Examples.ab_grammar ['a'] ['b'] 25 in
  let p1 = Examples.power_two_grammar 25 in
  let p2 = Examples.branching_fibonacci_grammar 25 in
  let p3 = Examples.recursive_grammar in
  let p4 = Examples.ab_grammar ['a'; 'b'] ['b'; 'a'] 25 in
  let ps = [p0; p1; p2; p3; p4] in

  let v0 = ("F25", "G25") in
  let v1 = ("S25", "T25") in
  let v2 = ("X23", "Y23") in
  let v3 = ("X", "Y") in
  let v4 = ("F25", "G25") in
  let vs = [v0; v1; v2; v3; v4] in

  let es = combine ps vs in
  List.iter (fun (p, v) -> procedure p v) es;

  exit 0;
;;
