open Taml;;


(* ------------------------------------------------------------------ *)
(* ------------------------------------------------------------------ *)
(* This file contains functions to handle rotations on binary trees in Timbuk *)
(* ------------------------------------------------------------------ *)
(* ------------------------------------------------------------------ *)


(* ------------------------------------------------------------------ *)
(* General functions                                                  *)
(* ------------------------------------------------------------------ *)
    
(*This version does not work*)
(*
let rec separate_rules_cont symbols rule_list =
	match rule_list with [] -> ([],[]) |
	first::rest ->
	    match (separate_rules_cont symbols rest) with (cont,not_cont) ->
		match (Rewrite.lhs first) with Common.Fsym(a,[_; _]) ->
			if (List.mem a symbols) then 
				(first::cont,not_cont)
			else
				(cont,first::not_cont)
		| _ ->  (cont,first::not_cont);;
*)

let separate_rules_cont symbols rule_list =
	let contains_symbol rule = List.mem (Taml.Term.top_symbol (Rewrite.lhs rule)) symbols in
	List.partition contains_symbol rule_list


let get_input_states rule=
	match (Rewrite.lhs rule) with Common.Fsym(_,[a; b]) -> (a,b)

(* This function return rules with RHS equal to "state" *)
let rec get_rules_state state rule_list=
	match rule_list with [] -> [] |
	first::rest ->
		if (Rewrite.rhs first)=state then
			first::(get_rules_state state rest)
		else (get_rules_state state rest);;

(* This function returns rules, with its left input state equal to "state" *)
let rec get_rules_input_state_left state rule_list = 
	match rule_list with [] -> [] |
	first::rest ->
		try
		  let (l,_)=get_input_states first in
		  if l=state then 
			first::(get_rules_input_state_left state rest)
		  else (get_rules_input_state_left state rest)
		with Match_failure _ -> 
		  (get_rules_input_state_left state rest);;

(* This function returns rules, with its right input state equal to "state" *)
let rec get_rules_input_state_right state rule_list = 
	match rule_list with [] -> [] |
	first::rest ->
		try
		  let (l,r)=get_input_states first in
		  if r=state then 
			first::(get_rules_input_state_right state rest)
		  else (get_rules_input_state_right state rest)
		with Match_failure _ -> 
		  (get_rules_input_state_right state rest);;
		  
(* Create `number' of new timbuk states, and state-ops 
   for number=2 -> XXX1, XXX2 *)
let rec new_states number=
	if (number=0) then
		(State_set.empty, Alphabet.new_alphabet)
	else
		let (states, state_ops)=(new_states (number-1)) in
		let new_symbol=Symbol.of_string (String.concat "" ["XXX";string_of_int number]) in
		(State_set.add (Common.Const new_symbol) states),(Alphabet.add_symbol new_symbol 0 state_ops);;

(* ------------------------------------------------------------------ *)
(* RIGHT ROTATE                                                       *)
(* ------------------------------------------------------------------ *)

let rec right_rotate_create_rules subrules_list upperrule iterator=
	match subrules_list with [] -> (Rewrite.empty,iterator) |
	first::rest ->
		let lhs1=Rewrite.lhs first in
(*		let rhs1=Rewrite.rhs first in*)
		let lhs2=Rewrite.lhs upperrule in
		let rhs2=Rewrite.rhs upperrule in
		let newstate= Common.Special(Common.Const(Symbol.of_string 
			(String.concat "" ["XXX";(string_of_int iterator)]))) in
		match lhs1,lhs2 with Common.Fsym(a1,[b1; c1]),Common.Fsym(a2,[b2; c2]) ->
		     let newrule1=Rewrite.new_rule
		     		(Common.Fsym(a1,[b1;newstate]))
				rhs2 in
		     let newrule2=Rewrite.new_rule
		     		(Common.Fsym(a2,[c1;c2]))
				newstate in
		     (match (right_rotate_create_rules rest upperrule (iterator+1)) with (rules, iter) ->
		     (Rewrite.add newrule1 (Rewrite.add newrule2 rules)),iter )
	        |_->failwith("right_rotate_create_rules")
;;



let rec right_rotate_do_for_all rules_with_x rules_without_x iterator=
	match rules_with_x with [] -> (Rewrite.empty,iterator) |
	first::rest ->
		let (left,right)=get_input_states first in
		let rules_under_x=get_rules_state left rules_without_x in
		let(changedrules1,iter1)=(right_rotate_create_rules rules_under_x first iterator) in
		let(changedrules2,iter2)=(right_rotate_do_for_all rest rules_without_x iter1) in

		(Rewrite.union changedrules1 changedrules2),iter2;;
		
let right_rotate_createrules orig_rules symbols =
	let rule_list=Rewrite.to_list orig_rules in
	(* separate rules containg symbols from list "symbols" *)
	let (x,notx)= separate_rules_cont symbols rule_list in
	let (new_rules,no_added_states)=(right_rotate_do_for_all x notx 1) in
	(Rewrite.union new_rules (Rewrite.list_to_trs notx)),no_added_states;;


let do_right_rotate symbols aut =
	let (new_rules,added_states_no)=right_rotate_createrules (Automaton.get_transitions aut) symbols in
	let (added_states,added_state_ops)=new_states added_states_no in
	Automaton.make_automaton
		(Automaton.get_alphabet aut)
		(Alphabet.union (Automaton.get_state_ops aut) added_state_ops)
		(State_set.union (Automaton.get_states aut) added_states)
		(Automaton.get_final_states aut)
		Rewrite.empty (* We suppose prior to be always empty *)
		new_rules;;
	
(* ------------------------------------------------------------------*)
(* REVERSE RIGHT ROTATE                                              *)
(* ------------------------------------------------------------------*)

let rec reverse_right_rotate_create_rules subrule upperrules_list iterator=
	match upperrules_list with [] -> (Rewrite.empty,iterator) |
	first::rest ->
		let lhs1=Rewrite.lhs subrule in
(*		let rhs1=Rewrite.rhs subrule in*)
		let lhs2=Rewrite.lhs first in
		let rhs2=Rewrite.rhs first in
		let newstate= Common.Special(Common.Const(Symbol.of_string 
			(String.concat "" ["XXX";(string_of_int iterator)]))) in
		match lhs1,lhs2 with Common.Fsym(a1,[b1; c1]),Common.Fsym(a2,[b2; c2]) ->
		     let newrule1=Rewrite.new_rule
		     		(Common.Fsym(a1,[newstate;c1]))
				rhs2 in
		     let newrule2=Rewrite.new_rule
		     		(Common.Fsym(a2,[b2;b1]))
				newstate in
		     (match (reverse_right_rotate_create_rules subrule rest (iterator+1)) with (rules, iter) ->
		     (Rewrite.add newrule1 (Rewrite.add newrule2 rules)),iter) 
		|_->failwith("reverse_right_rotate_create_rules")
;;


let rec reverse_right_rotate_do_for_all rules_with_x rules_without_x iterator=
	match rules_with_x with [] -> (Rewrite.empty,iterator) |
	first::rest ->
		let rules_over_x=get_rules_input_state_right (Rewrite.rhs first) rules_without_x in
		let(changedrules1,iter1)=(reverse_right_rotate_create_rules first rules_over_x iterator) in
		let(changedrules2,iter2)=(reverse_right_rotate_do_for_all rest rules_without_x iter1) in

		(Rewrite.union changedrules1 changedrules2),iter2;;
		

		
let reverse_right_rotate_createrules orig_rules symbols =
	let rule_list=Rewrite.to_list orig_rules in
	(* separate rules containg symbols from list "symbols" *)
	let (x,notx)= separate_rules_cont symbols rule_list in
	let (new_rules,no_added_states)=(reverse_right_rotate_do_for_all x notx 1) in
	(Rewrite.union new_rules (Rewrite.list_to_trs notx)),no_added_states;;

let do_reverse_right_rotate  symbols aut=
	let (new_rules,added_states_no)=reverse_right_rotate_createrules (Automaton.get_transitions aut) symbols in
	let (added_states,added_state_ops)=new_states added_states_no in
	Automaton.make_automaton
		(Automaton.get_alphabet aut)
		(Alphabet.union (Automaton.get_state_ops aut) added_state_ops)
		(State_set.union (Automaton.get_states aut) added_states)
		(Automaton.get_final_states aut)
		Rewrite.empty (* We suppose prior to be always empty *)
		new_rules;;
	
(* ------------------------------------------------------------------ *)
(* LEFT ROTATE                                                       *)
(* ------------------------------------------------------------------ *)

let rec left_rotate_create_rules subrules_list upperrule iterator=
	match subrules_list with [] -> (Rewrite.empty,iterator) |
	first::rest ->
		let lhs1=Rewrite.lhs first in
(*		let rhs1=Rewrite.rhs first in*)
		let lhs2=Rewrite.lhs upperrule in
		let rhs2=Rewrite.rhs upperrule in
		let newstate= Common.Special(Common.Const(Symbol.of_string 
			(String.concat "" ["XXX";(string_of_int iterator)]))) in
		match lhs1,lhs2 with Common.Fsym(a1,[b1; c1]),Common.Fsym(a2,[b2; c2]) ->
		     let newrule1=Rewrite.new_rule
		     		(Common.Fsym(a1,[newstate;c1]))
				rhs2 in
		     let newrule2=Rewrite.new_rule
		     		(Common.Fsym(a2,[b2;b1]))
				newstate in
		     (match (left_rotate_create_rules rest upperrule (iterator+1)) with (rules, iter) ->
		     (Rewrite.add newrule1 (Rewrite.add newrule2 rules)),iter) 
		|_->failwith"left_rotate_create_rules"
;;

let rec left_rotate_do_for_all rules_with_x rules_without_x iterator=
	match rules_with_x with [] -> (Rewrite.empty,iterator) |
	first::rest ->
		let (left,right)=get_input_states first in
		let rules_under_x=get_rules_state right rules_without_x in
		let(changedrules1,iter1)=(left_rotate_create_rules rules_under_x first iterator) in
		let(changedrules2,iter2)=(left_rotate_do_for_all rest rules_without_x iter1) in

		(Rewrite.union changedrules1 changedrules2),iter2;;
		
let left_rotate_createrules orig_rules symbols =
	let rule_list=Rewrite.to_list orig_rules in
	(* separate rules containg symbols from list "symbols" *)
	let (x,notx)= separate_rules_cont symbols rule_list in
	let (new_rules,no_added_states)=(left_rotate_do_for_all x notx 1) in
	(Rewrite.union new_rules (Rewrite.list_to_trs notx)),no_added_states;;

let do_left_rotate  symbols aut=
	let (new_rules,added_states_no)=left_rotate_createrules (Automaton.get_transitions aut) symbols in
	let (added_states,added_state_ops)=new_states added_states_no in
	Automaton.make_automaton
		(Automaton.get_alphabet aut)
		(Alphabet.union (Automaton.get_state_ops aut) added_state_ops)
		(State_set.union (Automaton.get_states aut) added_states)
		(Automaton.get_final_states aut)
		Rewrite.empty (* We suppose prior to be always empty *)
		new_rules;;
	
(* ------------------------------------------------------------------*)
(* REVERSE LEFT ROTATE                                              *)
(* ------------------------------------------------------------------*)

let rec reverse_left_rotate_create_rules subrule upperrules_list iterator=
	match upperrules_list with [] -> (Rewrite.empty,iterator) |
	first::rest ->
		let lhs1=Rewrite.lhs subrule in
(*		let rhs1=Rewrite.rhs subrule in*)
		let lhs2=Rewrite.lhs first in
		let rhs2=Rewrite.rhs first in
		let newstate= Common.Special(Common.Const(Symbol.of_string 
			(String.concat "" ["XXX";(string_of_int iterator)]))) in
		match lhs1,lhs2 with Common.Fsym(a1,[b1; c1]),Common.Fsym(a2,[b2; c2]) ->
		     let newrule1=Rewrite.new_rule
		     		(Common.Fsym(a1,[b1;newstate]))
				rhs2 in
		     let newrule2=Rewrite.new_rule
		     		(Common.Fsym(a2,[c1;c2]))
				newstate in
		     (match (reverse_left_rotate_create_rules subrule rest (iterator+1)) with (rules, iter) ->
		     (Rewrite.add newrule1 (Rewrite.add newrule2 rules)),iter) 
		|_->failwith"reverse_left_rotate_create_rules"
;;


let rec reverse_left_rotate_do_for_all rules_with_x rules_without_x iterator=
	match rules_with_x with [] -> (Rewrite.empty,iterator) |
	first::rest ->
		let rules_over_x=get_rules_input_state_left (Rewrite.rhs first) rules_without_x in
		let(changedrules1,iter1)=(reverse_left_rotate_create_rules first rules_over_x iterator) in
		let(changedrules2,iter2)=(reverse_left_rotate_do_for_all rest rules_without_x iter1) in

		(Rewrite.union changedrules1 changedrules2),iter2;;
		

		
let reverse_left_rotate_createrules orig_rules symbols =
	let rule_list=Rewrite.to_list orig_rules in
	(* separate rules containg symbols from list "symbols" *)
	let (x,notx)= separate_rules_cont symbols rule_list in
	let (new_rules,no_added_states)=(reverse_left_rotate_do_for_all x notx 1) in
	(Rewrite.union new_rules (Rewrite.list_to_trs notx)),no_added_states;;

let do_reverse_left_rotate  symbols aut=
	let (new_rules,added_states_no)=reverse_left_rotate_createrules (Automaton.get_transitions aut) symbols in
	let (added_states,added_state_ops)=new_states added_states_no in
	Automaton.make_automaton
		(Automaton.get_alphabet aut)
		(Alphabet.union (Automaton.get_state_ops aut) added_state_ops)
		(State_set.union (Automaton.get_states aut) added_states)
		(Automaton.get_final_states aut)
		Rewrite.empty (* We suppose prior to be always empty *)
		new_rules;;
	
