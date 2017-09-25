(*open Taml*)
open FixpointAntichain (*I want module IndexTuple*)

let _ = Random.self_init ()

let fn = false

(*maintaining tuples of inteegrs*)
let rec exp x e = 
	if e<0 then 0 else if e=0 then 1 else x * (exp x (e-1));;  

let num_of_tuple ic tuple =
	let rec get_num_of_tuple ic tuple = 
		let arity = List.length tuple in
		match tuple with
		[] -> 0
		| h::t -> (h*(exp ic (arity-1)))+(get_num_of_tuple ic t) 
	in
	get_num_of_tuple ic (List.rev tuple)

;;

let tuple_of_num arity ic n =
	let rec get_tuple_of_num arity ic n =
		if arity = 0 then [] else
		((((n/(exp ic (arity-1))))+ ic) mod ic)::(get_tuple_of_num (arity-1) ic (n mod (exp ic (arity-1))))
	in
	List.rev (get_tuple_of_num arity ic n)
;;

let tuples_of_nums arity ic nums = 
   Trlist.map (tuple_of_num arity ic) nums	
;;

let count_of_tuples arity ic = exp ic arity -1
;;

let rec do_add_to_occupied big small elem =
	match small with 
	[] -> elem::big
	| e2::small_tail -> 
		if e2 = elem then failwith "do_add_to_occupied"
		else if e2 > elem then List.rev_append (List.rev small_tail) (elem::big)
		else do_add_to_occupied small_tail (e2::big) elem 

let add_to_occupied occupied elem =
	do_add_to_occupied occupied [] elem

	
let rotate_occupied occupied elem =
	let rec do_rotate_occupied bigger smaller elem =
(*tl*)
		match bigger with
		[] ->  []
		| elem2::bigger_rest -> 
			if elem=elem2 then List.rev_append (List.rev bigger) (List.rev smaller)
			else if elem2>elem then []
			else do_rotate_occupied bigger_rest (elem2::smaller) elem 
	in 
	do_rotate_occupied occupied [] elem
;;

(*tl*)
let rec get_nearest_unoccupied max occupied elem =
	match occupied with
	[] -> elem
	| h::t -> 
		if h=elem then get_nearest_unoccupied max t ((elem + 1 + (max+1)) mod (max+1))
		else elem
;;

let get_random_num max_num occupied =
	let first_try = Random.int (max_num+1) in
	let r_occ = (rotate_occupied occupied first_try) in
	get_nearest_unoccupied max_num r_occ first_try 
;;

(*tl*)
let rec do_get_random_nums max_num occupied n =
	if n<=0 then occupied
	else (
		let new_num = get_random_num max_num occupied in
		do_get_random_nums max_num (add_to_occupied occupied new_num) (n-1)
	)
;;

let get_random_nums max_num n = 
	if ((max_num+1) / n) < 2 then ( 
		let excluded = do_get_random_nums max_num [] ((max_num+1) - n) in (*it's ordered*)
		let rec all_without_excluded current max_num excluded accum = 
			if current>max_num then accum
			else (
				match excluded with
				[] -> all_without_excluded (current+1) max_num excluded (current::accum)
				| h::t -> if current<h then all_without_excluded (current+1) max_num excluded (current::accum)
				  else all_without_excluded (current+1) max_num t accum
			)
		in
		(*
		all_without_excluded 0 max_num excluded 
		*)
		all_without_excluded 0 max_num excluded []
	)
	else do_get_random_nums max_num [] n
;;

let get_random_tuples ic arity n =
	tuples_of_nums arity ic (get_random_nums (count_of_tuples arity ic) n)
;;

let rec do_get_int_list m accum =
  if m < 0 then accum
  else do_get_int_list (m-1) (m :: accum);;

let get_int_list m =
  do_get_int_list m [];;


(*name of state qx from integer x*)
let state_name m = Printf.sprintf "q%d" m;;

(*list of state-names from list of integers*)
let ints_to_states ints =
	Trlist.map state_name ints;;

(*
let get_ops count =
	let states = Array.init count (fun i -> i) in
	Array.fold_left (fun ops q ->
		Taml.Alphabet.add_symbol (Taml.Symbol.of_string (state_name q)) 0 ops)
		Taml.Alphabet.new_alphabet states
;;
*)

(*
let get_states count =  
	let states = Array.init count (fun i -> i) in
	Array.fold_left (fun t_sts q ->
		Taml.State_set.add (Common.Const (Taml.Symbol.of_string (state_name q))) t_sts)
		Taml.State_set.empty states
*)


let get_stateset_str count =
        let concat_string_int a b = String.concat "" [a;(string_of_int b)] in
        let ints = get_int_list count in
        let strings = Trlist.map (concat_string_int "q") ints in
        let res = String.concat " " strings in
	res

(*float round*)
let round x = int_of_float (x+.0.5);;

(*proportional part to an integer*)
let part count rate = round ((float count)*.rate);;

let rec do_get_random_int_list length max accum =
	if length <= 0 then accum
	else do_get_random_int_list (length-1) max ((Random.int(max))::accum);;

let get_random_int_list length max =
	 do_get_random_int_list length max []

(*list of count random integer lists (max, length) *)
(*mozna*)
let rec do_get_random_lists length max count accum =
	if count<=0 then accum
	else do_get_random_lists length max (count-1) ((get_random_int_list length max)::accum)

let get_random_lists length max count =
	do_get_random_lists length max count []
	
(*symbol name*)
        (*
let symbol_name syma = 
	match syma with (s,_)->Taml.Symbol.to_string s;;
*)
let symbol_name = fst

(*count of transitions of symbol acording to its arity, ratio and count of states*)
let transition_count syma ratio states_c = (*part states_c ratio;;*)
	let b = max 1 (int_of_float(0.5 +. (ratio *. (float_of_int (exp  states_c (snd syma)))))) in
	b

(*creates rule-string from (symb, ar) list of numbers of left states, number of right state*)
let get_rule syma left_int_list right_int =
	let left_str_list = ints_to_states left_int_list in
	let state_str = String.concat ", " left_str_list in
	if (snd syma)>0 then Printf.sprintf "%s(%s) -> %s" (symbol_name syma) state_str (state_name right_int)
	else Printf.sprintf "%s -> %s" (symbol_name syma) (state_name right_int);;

(*
let get_rule3 syma left_int_list right_int = 
	let symbol = Taml.Symbol.of_string (symbol_name syma) in
	let rhs = Common.Special (Common.Const (Taml.Symbol.of_string (state_name right_int))) in
	match left_int_list with
	[] -> Taml.Rewrite.new_rule (Common.Const (symbol)) rhs
	| _ -> 
		let lhs = List.map 
			(function q -> Common.Special (Common.Const (Taml.Symbol.of_string (state_name q)))) 
			left_int_list 
		in
		Taml.Rewrite.new_rule (Common.Fsym (symbol,lhs)) rhs
                *)

let get_rule2 syma tuple =
	match tuple with 
	h::t ->
		let rhs = state_name h in
		let lhs = String.concat ", " (ints_to_states t) in
		let symbol = symbol_name syma in
		if (snd syma)>0 then Printf.sprintf "%s(%s) -> %s" symbol lhs rhs
		else Printf.sprintf "%s -> %s" symbol rhs
    | _ -> failwith"get_rule2"	

(*list of str rules from symbol, list of lists of left states, list of right states*)
let get_rules syma left_int_llist right_int_list =
	let get_rule_syma l r = get_rule syma l r in(*?*)
	Trlist.map2 get_rule_syma left_int_llist right_int_list;;

(*
let get_rules3 syma left_int_llist right_int_list =
	let get_rule_syma l r = get_rule3 syma l r in(*?*)
	Trlist.map2 get_rule_syma left_int_llist right_int_list;;
*)

(*list of str rules from symbol, list of lists of left states, list of right states*)
let get_rules2 syma tuples =
	Trlist.map (get_rule2 syma) tuples;;

(*list of random trans. rules strings for one symbol, acording to the ratio,
 count of states and arity of symbol*)
let get_rules_for_symbol state_c syma ratio = 
	let trans_c = transition_count syma ratio state_c in 	
	let left_states = get_random_lists (snd syma) state_c trans_c in
	let right_states = get_random_int_list (trans_c) state_c in
	get_rules syma left_states right_states;;

(*
let get_rules_for_symbol3 state_c syma ratio = 
	let trans_c = transition_count syma ratio state_c in 	
	let left_states = get_random_lists (snd syma) state_c trans_c in
	let right_states = get_random_int_list (trans_c) state_c in
	get_rules3 syma left_states right_states;;
*)
	
let get_rules_for_symbol2 state_c syma ratio = 
	let trans_c = transition_count syma ratio state_c in 	
	let tuples = get_random_tuples state_c ((snd syma) +1) trans_c in
	get_rules2 syma tuples;;
	
(*I don't remember, propably it generates transition table string*)
let get_rules_for_alphabet alph state_c ratio = 
(*	let alph_list = Taml.Alphabet.to_list alph in*)
	let alph_list = alph in
	let get_rules_fs_state_c_ratio syma = get_rules_for_symbol state_c syma ratio in
	let rules_llist = Trlist.map get_rules_fs_state_c_ratio alph_list in
	String.concat "\n" (Trlist.concat rules_llist);;		

(*
let get_rules_for_alphabet3 alph state_c ratio = 
	let alph_list = Taml.Alphabet.to_list alph in
	let get_rules_fs_state_c_ratio syma = get_rules_for_symbol3 state_c syma ratio in
	let rules_llist = Trlist.map get_rules_fs_state_c_ratio alph_list in
	Taml.Rewrite.list_to_trs (Trlist.concat rules_llist);;		
*)

let get_rules_for_alphabet2 alph state_c ratio = 
(*	let alph_list = Taml.Alphabet.to_list alph in*)
	let alph_list = alph in
	let get_rules_fs_state_c_ratio syma = get_rules_for_symbol2 state_c syma ratio in
	let rules_llist = Trlist.map get_rules_fs_state_c_ratio alph_list in
	String.concat "\n" (Trlist.concat rules_llist);;		

(*
let generate_automaton3 ~alphabet:alph ~number_ofstates:state_c ~alphabet_ratio:alph_ratio ~final_states_ratio:fin_ratio =
	let transitions = get_rules_for_alphabet3 alph state_c alph_ratio in
	let final_c = part state_c fin_ratio in
	let ops = get_ops state_c in
	let states = get_states state_c in
	let final_states = get_states final_c in
	Taml.Automaton.make_automaton
		alph
		ops
		states
		final_states
		(Taml.Rewrite.empty)
		transitions;;
*)

let generate_automaton ~alphabet:alph ~number_ofstates:state_c ~alphabet_ratio:alph_ratio ~final_states_ratio:fin_ratio =
	let transitions = get_rules_for_alphabet alph state_c alph_ratio in
	let final_c = part state_c fin_ratio in
	let automaton_str = Printf.sprintf "States %s\nFinal States %s\nTransitions\n%s"
				(get_stateset_str state_c) (get_stateset_str final_c) transitions in
        automaton_str
(*	(*Automaton.simplify*) (Taml.automaton alph automaton_str);;
*)

let generate_automaton2 ~alphabet:alph ~number_ofstates:state_c ~alphabet_ratio:alph_ratio ~final_states_ratio:fin_ratio =
	let transitions = get_rules_for_alphabet2 alph state_c alph_ratio in
	let final_c = part state_c fin_ratio in
	let automaton_str = Printf.sprintf "States %s\nFinal States %s\nTransitions\n%s"
				(get_stateset_str state_c) (get_stateset_str final_c) transitions in
        automaton_str
(*	Interim.simplify_taml (Taml.automaton alph automaton_str);;
*	*)
