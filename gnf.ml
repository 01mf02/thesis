open List;;

type production_rule = char * int list;;

type gnf = int * char list * production_rule list list;;

let rec norm i grammar =
  match grammar with (_, _, p) ->
    match hd (nth i p) with (_, vars) ->
      vars;;
