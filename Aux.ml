open List;;

(* taken from OCaml 4.01 *)
let rec iteri i f = function
  [] -> ()
| a::l -> f i a; iteri (i + 1) f l
let iteri f l = iteri 0 f l

let fold_left1 f = function
  [] -> raise Not_found
| a::l -> fold_left f a l

(* return smallest element of a list, or raise Not_found if list empty *)
let min_list l = fold_left1 min l

let ilsum = fold_left (+) 0

(* determine whether the first list is a prefix of the second list,
 * and if so, return the remaining part of the second list *)
let rec is_prefix = function
  ([], postfix) -> Some postfix
| (_::_, []) -> None
| (h1::t1, h2::t2) -> if h1 = h2 then is_prefix (t1, t2) else None

(* returns [i; i+1; ...; j] *)
let rec range_incl i j = if i > j then [] else i::(range_incl (i+1) j)

let pair_map f (x, y) = (f x, f y)

