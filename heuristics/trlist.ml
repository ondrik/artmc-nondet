(*tail recursive variants of some ocaml list functions*)
(*I need some tail recursive iterators - map, map2, concat*)
let rec do_map f l accum =
	match l with
	[] -> accum
	| h::t -> do_map f t ((f h)::accum)

let map f l = List.rev (do_map f l [])

let rec do_concat l accum =
	match l with
	[] -> accum
	| h::t -> do_concat t (List.rev_append h accum)

let concat l = List.rev (do_concat l [])

let rec do_map2 f l1 l2 accum = 
	match l1,l2 with
	[],[] -> accum
	| h1::t1,h2::t2 -> do_map2 f t1 t2 ((f h1 h2)::accum)
	| _ -> failwith"Trlist.do_map2"

let map2 f l1 l2 =  List.rev (do_map2 f l1 l2 [])


