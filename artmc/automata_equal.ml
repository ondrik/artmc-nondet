open Taml
open Minimize_abstr_fin_length;;
(* if the given sets of rules not matching, we raise the exception *)
exception No_match;;

(* ----------------------------------------------------------------------------------*)
(* Handling pairs of states *)

let rec check_state_pair pairs x y=
	match pairs with [] -> true |
	(a,b)::rest ->
		if a=x then (
			if b=y then true
			else false)
		else
		if b=y then false
		else check_state_pair rest x y;;
	
let add_state_pair pairs x y fin1 fin2=
	if (List.mem (x,y) pairs) then pairs
	else 
	  if (List.mem x fin1) then
	     (if (List.mem y fin2) then 
		(x,y)::pairs
	     else raise No_match )
	  else
	     if (List.mem y fin2) then
	     	raise No_match
	     else (x,y)::pairs;;

let rec pairs_is_left_mem pairs x=
	match pairs with [] -> false |
	(a,b)::rest ->
		if x=b then true
		else pairs_is_left_mem rest x;;

(* ----------------------------------------------------------------------------------*)
(* handling INIT rules *)

(* This function search corresponding init rule (from rules2) for a given init rule
   founded state-pair is added to list of pairs 
   - when calling, set not_used2=[] *)
let rec pair_one_init_rule rule fin1 not_used2 rules2 fin2 pairs =
	match rules2 with [] -> raise No_match |
	first::rest ->
		match first with (a,[],b) ->
			(match rule with (x,[],y) ->
				if a=x then
					if check_state_pair pairs y b then
						(not_used2@rest,add_state_pair pairs y b fin1 fin2)
					else raise No_match
				else
					pair_one_init_rule
						rule
						fin1
						(not_used2@[first])
						rest
						fin2
						pairs 
			 | _ -> failwith("pair_one_init_rule")
			)
		| _ ->
			pair_one_init_rule
				rule
				fin1
				(not_used2@[first])
				rest
				fin2
				pairs;;

(* This function take all init rules from a set rules1, and
   search corresponding init rules (from rules2) - by function pair_one_init_rule
   - when calling, set rules1not_match=[] *)
let rec pair_init_rules rules1not_match rules1 fin1  rules2 fin2 pairs=
	match rules1 with [] -> (rules1not_match,rules2,pairs) |
	first::rest ->
		match first with (a,[],b) ->
			let (new_rules2,new_pairs)=pair_one_init_rule
				first
				fin1
				[]
				rules2
				fin2
				pairs in
			pair_init_rules
				rules1not_match
				rest
				fin1
				new_rules2
				fin2
				new_pairs
		| _ ->
		pair_init_rules 
			(rules1not_match@[first])
			rest
			fin1
			rules2
			fin2
			pairs;;
	
(* ----------------------------------------------------------------------------------*)
(* handling inner rules *)

(* This functions found rule, where all states on LHS is in set of pairs *)
let rec search_next_matching_rule not_cor rules2 pairs =
	let rec check_states states=
		match states with [] -> true 
		| first::rest -> 
			if (pairs_is_left_mem pairs first) then
				check_states rest
			else false in
	match rules2 with [] -> raise No_match (* rules sets are no equal *)
	| (a,b,c)::rest ->
	   if b=[] then raise No_match (* there is a no matching init rule *)
	   else
	   	if (check_states b) then ((not_cor@rest),(a,b,c)) (* rule founded *)
		else
		   search_next_matching_rule (not_cor@[(a,b,c)]) rest pairs;;
	     
(* to the selected rule from rules2 (with known both states on lhs)
   find corresponding rule from rules1 - !!! automaton is deterministic and minimal !!!
   -> there exist at most one *)


   
let rec find_corresponding_rule not_cor rules1 rule pairs fin1 fin2 =
	let rec pairs_match l1 l2=
		match l1 with [] -> true
		| f1::r1 ->
		  match l2 with f2::r2 -> (* l1 and l2 have equal length *) 
		  (List.mem (f1,f2) pairs) & ( pairs_match r1 r2) | _ -> failwith("find_corresponding_rule") in
	
	match rules1 with [] ->  raise No_match (* rules sets are no equal *)
	| (a,b,c)::rest ->
	  match rule with (x,y,z) ->
	    if (a=x)&((List.length b)=(List.length y))& (pairs_match b y) then 
	        if  (check_state_pair pairs c z) then
			(not_cor@rest,add_state_pair pairs c z fin1 fin2)
		else raise No_match 
	         
	    else
	      find_corresponding_rule (not_cor@[(a,b,c)]) rest rule pairs fin1 fin2;;

let rec make_pairs_of_rest rules1 fin1 rules2 fin2 pairs=
	if (rules2=[])&(rules1=[]) then true
	else
	  let (rest2,rule_to_process)=search_next_matching_rule [] rules2 pairs in
	  let (rest1,new_pairs)=find_corresponding_rule [] rules1 rule_to_process pairs fin1 fin2 in
	  make_pairs_of_rest rest1 fin1 rest2 fin2 new_pairs;;

(* ----------------------------------------------------------------------------------*)
(* global calls *)
	

let check_equal rules1 fin1 rules2 fin2=
	let (r1,r2,pairs)=pair_init_rules [] rules1 fin1 rules2 fin2 [] in
	try make_pairs_of_rest r1 fin1 r2 fin2 pairs
	with No_match -> false;;

let transform_rule rule =
	let lhs=Rewrite.lhs rule in
	let rhs_string=match (Rewrite.rhs rule) with Common.Special a -> a 
		       | _ -> failwith("transform_rule1") in
	match lhs with Common.Const a -> 
		(Symbol.to_string a,[],rhs_string)|
	Common.Fsym (a,b) ->
		let rec transf_states state_list=
			match state_list with [] -> [] |
			first::rest -> 
			  match first with Common.Special x ->
				x ::(transf_states rest) 
			  | _ -> failwith("transform_rule")	
		in
		(Symbol.to_string a,transf_states b,rhs_string)
	| _ -> failwith("transform_rule2");;
		

let automata_equal aut1 aut2=
	let aut1m=minimize(determinise(simplify aut1)) in
	let aut2m=minimize(determinise(simplify aut2)) in
	let rules1=Rewrite.to_list(Automaton.get_transitions aut1m) in
	let rules2=Rewrite.to_list(Automaton.get_transitions aut2m) in
	if not ((List.length rules1)=(List.length rules2)) then (
(*		print_string "pocet pravidel nesedi\n"; flush stdout;*)
		false )
	else 
	  let no_states1=List.length(State_set.to_list(Automaton.get_states aut1m)) in
	  let no_states2=List.length(State_set.to_list(Automaton.get_states aut2m)) in
	  if not (no_states1=no_states2) then (
(*		print_string "pocet stavu nesedi\n"; flush stdout;*)
		false )
	  else
	    let fin_states1=State_set.to_list(Automaton.get_states aut1m) in
	    let fin_states2=State_set.to_list(Automaton.get_states aut2m) in
	    let no_fin_states1=List.length fin_states1 in
	    let no_fin_states2=List.length fin_states2 in
	    if not (no_fin_states1=no_fin_states2) then (
(*		print_string "pocet stavu nesedi\n"; flush stdout;*)
		false )
	    else
	      check_equal
	      	(List.map transform_rule rules1)
		fin_states1
	      	(List.map transform_rule rules2)
		fin_states2;;

