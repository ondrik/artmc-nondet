open Taml;;
let print_one (st,lab)= Printf.printf "%s=%s\n" (Term.to_string st) lab;; 
(****************************************************************************************************
***** Collapsing automata wrt. predicates [[ The version with "1 automaton = 1 predicate" ]]
****************************************************************************************************)

(*====================================================================================================
***** Labelling automata wrt. predicates
====================================================================================================*)

let aut_from_aut_and_final aut fin =
   Interim.simplify_taml (Automaton.make_automaton
         (Automaton.get_alphabet aut)
         (Automaton.get_state_ops aut)
         (Automaton.get_states aut)
         (State_set.add fin (State_set.empty))
         (Automaton.get_prior aut)
         (Automaton.get_transitions aut) );;

(*====================================================================================================*)

let state_to_be_labelled_by_pred aut st pred =
  not (Automaton.is_empty (Interim.simplify_taml (Automaton.inter
  (Interim.simplify_taml (aut_from_aut_and_final aut st)) pred)));;

(*====================================================================================================*)

let rec label_state_by_pred aut st pred_list =
  match pred_list with
      [] -> ""
    | (pred_name,pred)::pred_list_rest -> 
        let lab_str_rest = (label_state_by_pred aut st pred_list_rest) in
          if (state_to_be_labelled_by_pred aut st pred) then (String.concat "" [ pred_name; lab_str_rest ])
          else lab_str_rest;;

let rec label_states_by_pred aut states pred_list =
  if State_set.is_empty states then []
  else 
    let state,states_rest = State_set.first states,State_set.remainder states in
    let labels_rest = label_states_by_pred aut states_rest pred_list in
      (state,(label_state_by_pred aut state pred_list))::labels_rest;;

(*====================================================================================================
***** Collapsing automata labelled by predicates
====================================================================================================*)

let rec find_st_label lab_list st1 =
	match lab_list with
	(st2,label)::lab_list_rest -> 
		if st1 = st2 then label else find_st_label lab_list_rest st1
	| _ -> failwith("find_st_label")

(*====================================================================================================*)

let rename_const_to_lab lab_list const =
	Common.Const (Symbol.of_string (find_st_label lab_list const));;

let rename_spec_to_lab lab_list spec = 
	match spec with
	Common.Special const -> Common.Special (rename_const_to_lab lab_list const)
	| _ -> failwith("rename_spec_to_lab")

let rec rename_spec_list_to_lab lab_list spec_list = 
	match spec_list with 
	[] -> []
	| spec::spec_list_rest -> 
		(rename_spec_to_lab lab_list spec)::(rename_spec_list_to_lab lab_list spec_list_rest);;

let rename_aut_rule_to_lab lab_list rule =
	let lhs,targ = Rewrite.lhs rule, Rewrite.rhs rule in
	match lhs with
	Common.Fsym (op, arg) -> 
		(Rewrite.new_rule (Common.Fsym (op, (rename_spec_list_to_lab lab_list arg))) 
									   (rename_spec_to_lab lab_list targ))
	| Common.Const op ->
		(Rewrite.new_rule (Common.Const op) (rename_spec_to_lab lab_list targ))
	| _ -> failwith("rename_aut_rule_to_lab")

let rec rename_aut_rules_to_lab lab_list rules =
	if Rewrite.is_empty rules then Rewrite.empty
	else let rule,rules_rest = Rewrite.first rules, Rewrite.remainder rules in
	Rewrite.add (rename_aut_rule_to_lab lab_list rule) (rename_aut_rules_to_lab lab_list rules_rest);;

(*====================================================================================================*)

let rec gen_states_with_lab lab_list done_list =
	match lab_list with 
	[] -> (State_set.empty, Alphabet.new_alphabet)
	| (_,label)::lab_list_rest ->
		if (List.mem label done_list) then 
			(gen_states_with_lab lab_list_rest done_list)
		else 
			match (gen_states_with_lab lab_list_rest (label::done_list)) with (st_rest, st_ops_rest) -> 
				((State_set.add (Common.Const (Symbol.of_string label)) st_rest), 
				(Alphabet.add_symbol (Symbol.of_string label) 0 st_ops_rest));;

(*====================================================================================================*)

let rec rename_fin_states_to_lab lab_list fin_stset done_list =
	match lab_list with 
	[] -> State_set.empty
	| (st,label)::lab_list_rest ->
		if (List.mem label done_list) then 
			(rename_fin_states_to_lab lab_list_rest fin_stset done_list)
		else (
			if (State_set.mem st fin_stset) then 
				(let new_fin_rest = (rename_fin_states_to_lab lab_list_rest fin_stset (label::done_list)) in
				State_set.add (Common.Const (Symbol.of_string label)) new_fin_rest)
			else (rename_fin_states_to_lab lab_list_rest fin_stset done_list)
		);;

(*====================================================================================================*)

let do_bw_coll aut lab_list =
	let (st_set, st_ops) = gen_states_with_lab lab_list [] in
	let fin_st = rename_fin_states_to_lab lab_list (Automaton.get_final_states aut) [] in
	let tr_rules = rename_aut_rules_to_lab lab_list (Automaton.get_transitions aut) in
	(Interim.simplify_taml (Automaton.make_automaton
		(Automaton.get_alphabet aut)
		st_ops
		st_set
		fin_st
		Rewrite.empty
		tr_rules ) );;

(*====================================================================================================*)

let bw_coll aut pred_list =
  let lab_list = label_states_by_pred aut (Automaton.get_states aut) pred_list in
    do_bw_coll aut lab_list;;



(* ==================================================================================================== *)
(* **************************************************************************************************** *)
(* ***** Collapsing automata wrt. predicates [[ The version with "each automaton st. = 1 predicate" ]]  *)
(* **************************************************************************************************** *)
(* ==================================================================================================== *)

(* ==================================================================================================== *)
(* ***** Maintaining a table of labels -- i.e. a list of (state,list of states)                         *)
(* ==================================================================================================== *)

(* *** Maintaing a list-encoded set. The list is kept ordered! *)

let rec add_to_list list elem =
	match list with
	[] ->  [ elem ]
	| elem2::list_rest -> 
		if elem=elem2 then elem::list_rest
		else if elem2>elem then elem::(elem2::list_rest)
		else elem2::(add_to_list list_rest elem);;

let rec is_in_list list elem =
	match list with
	[] ->  false
	| elem2::list_rest -> 
		if elem=elem2 then true
		else if elem2>elem then false
		else is_in_list list_rest elem;;

(* ==================================================================================================== *)

(* *** We supose labelling of Common.Special by Common.Special... Again, we keep the lists ordered! *)

let rec add_label lab_table st label =
	match lab_table with
	[] -> [ (st, [ label ]) ]
	| (st2,lab_list)::lab_table_rest -> 
		if st=st2 then (st,(add_to_list lab_list label))::lab_table_rest
		else if st2>st then (st, [ label ])::((st2,lab_list)::lab_table_rest)
		else (st2,lab_list)::(add_label lab_table_rest st label);;

let rec is_lab_with lab_table st label =
	match lab_table with
	[] -> false
	| (st2,lab_list)::lab_table_rest -> 
		if st=st2 then (is_in_list lab_list label)
		else if st2>st then false
		else (is_lab_with lab_table_rest st label);;

let rec is_labelled lab_table st =
	match lab_table with
	[] -> false
	| (st2,_)::lab_table_rest -> 
		if st=st2 then true
		else if st2>st then false
		else (is_labelled lab_table_rest st);;

(* ==================================================================================================== *)
(* ***** Labelling wrt. leaf rules                                                                      *)
(* ==================================================================================================== *)

let is_leaf_rule rule = 
	match (Rewrite.lhs rule) with
	Common.Const(_) -> true
	| _ -> false;;

(* ==================================================================================================== *)

let rec label_with_leaf_rule rules leaf_rule_sym leaf_rule_st lab_table to_do_list =
	match rules with
	[] -> (lab_table, to_do_list)
	| rule::rules_rest -> 
		let aux = (label_with_leaf_rule rules_rest leaf_rule_sym leaf_rule_st lab_table to_do_list) in
		if ((Rewrite.lhs rule) = leaf_rule_sym) then
			match aux with (new_lab_table, new_to_do_list) ->
				let rule_st = (Rewrite.rhs rule) in
				((add_label new_lab_table rule_st leaf_rule_st),
				(add_to_list new_to_do_list (rule_st,leaf_rule_st)))
		else aux;;  

(* *** We suppose only leaf rules at the input... *)

let rec label_with_leaf_rules rules labwith_rules lab_table to_do_list =
	match labwith_rules with
	[] -> (lab_table, to_do_list)
	| labwith_rule::labwith_rules_rest ->
		let aux = (label_with_leaf_rules rules labwith_rules_rest lab_table to_do_list) in
		match aux with (new_lab_table, new_to_do_list) -> 
			(label_with_leaf_rule rules (Rewrite.lhs labwith_rule) 
			(Rewrite.rhs labwith_rule) new_lab_table new_to_do_list);;

(* ==================================================================================================== *)
(* ***** Labelling wrt. inner (non-leaf) rules                                                          *)
(* ==================================================================================================== *)

let rec lhs_st_list_match lhs_st_list labwith_lhs_st_list lab_table =
	match lhs_st_list with
	[] -> (labwith_lhs_st_list = [])      
	| st::lhs_st_list_rest ->
		(match labwith_lhs_st_list with
		[] -> false
		| labwith_st::labwith_lhs_st_list_rest ->
			if (is_lab_with lab_table st labwith_st) then
				(lhs_st_list_match lhs_st_list_rest labwith_lhs_st_list_rest lab_table)
			else false);;

let inner_lhs_match lhs labwith_lhs lab_table =
	match lhs with
	Common.Fsym(lhs_sym,lhs_st_list) -> 
		(match labwith_lhs with Common.Fsym(labwith_lhs_sym,labwith_lhs_st_list) -> 
			if (lhs_sym = labwith_lhs_sym) then
				(lhs_st_list_match lhs_st_list labwith_lhs_st_list lab_table)
			else false
		|_->failwith("inner_lhs_match1"))  
	|_->failwith("inner_lhs_match2")  

(* ==================================================================================================== *)

(* *** We suppose only inner rules at the input... *)

let rec label_with_inner_rule rules labwith_rule_lhs labwith_rule_st lab_table to_do_list =
	match rules with
	[] -> (lab_table, to_do_list)
	| rule::rules_rest -> 
		let aux = (label_with_inner_rule rules_rest labwith_rule_lhs labwith_rule_st lab_table to_do_list) in
		match aux with (new_lab_table, new_to_do_list) ->
			let rhs = (Rewrite.rhs rule) in
			if (is_lab_with new_lab_table rhs labwith_rule_st) then
				(new_lab_table, new_to_do_list)
			else if (inner_lhs_match (Rewrite.lhs rule) labwith_rule_lhs new_lab_table) then
				((add_label new_lab_table rhs labwith_rule_st),(add_to_list new_to_do_list (rhs,labwith_rule_st)))
			else (new_lab_table, new_to_do_list);;

let rec label_with_inner_rules rules labwith_rules lab_table to_do_list =
	match labwith_rules with
	[] -> (lab_table, to_do_list)
	| inner_rule::labwith_rules_rest -> 
		let aux = (label_with_inner_rules rules labwith_rules_rest lab_table to_do_list) in
		match aux with (new_lab_table, new_to_do_list) ->
			(label_with_inner_rule rules (Rewrite.lhs inner_rule) (Rewrite.rhs inner_rule) new_lab_table new_to_do_list);;

(* ==================================================================================================== *)
(* ***** Labelling of inner rules wrt. inner rules in both cases starting from certain states           *)
(* ==================================================================================================== *)
let print_todo to_do_list= (List.iter (fun (a,b) -> print_string(Printf.sprintf "(%s,%s)" (Term.to_string a) (Term.to_string b))) to_do_list);; 
let pr_rl rl = List.iter (fun r -> Printf.printf "%s\n" (Rewrite.rule_to_string r)) rl;;
let pr_sl sl = Printf.printf "[%s]: " (String.concat ";" (List.map Term.to_string sl));;

(* *** We suppose only inner rules at the input... *)

let rec inner_rules_going_from inner_rules st =
	
(*	Printf.printf "\n\nINNER_RULES_GOING_FROM %s:\n" (Term.to_string st);*)
(*	pr_rl inner_rules;*)
	match inner_rules with
	[] -> []
	| inner_rule::inner_rules_rest ->
		let inner_rules_going_from_rest = (inner_rules_going_from inner_rules_rest st) in
(*		let res =*)
(*		Printf.printf "%s: %s: " (Term.to_string st) (Rewrite.rule_to_string inner_rule);*)
		match (Rewrite.lhs inner_rule) with 
		Common.Fsym(_,st_list) -> (*pr_sl st_list;*)
(*			if (is_in_list st_list st) then ((*print_endline "true";*) *)
			if (List.mem st st_list) then ((*print_endline "true";*)
				inner_rule::inner_rules_going_from_rest)
			else ((*print_endline "false";*)
				inner_rules_going_from_rest)
		|_->failwith("inner_rules_going_from ")  
(*		in*)
(*		print_string "\nRESULT\n";*)
(*	pr_rl res;*)
(*		res*)
;;
              
(* ==================================================================================================== *)

(* *** A further opimization could be such that we choose only rules that have tolab_st and labwith_st *)
(* *** at the same pozitions...                                                                        *)

let label_inner_from tolab_st labwith_st tolab_inner_rules labwith_inner_rules lab_table to_do_list =
(*	print_string "\n\nLABEL_INNER_FROM\n";*)
(*	Printf.printf "(%s.%s)\n" (Term.to_string tolab_st)(Term.to_string labwith_st);*)
	let use_tolab_inner_rules = (inner_rules_going_from tolab_inner_rules tolab_st) in
(*	print_endline "tolab_rs";*)
(*	pr_rl use_tolab_inner_rules; *)
	let use_labwith_inner_rules = (inner_rules_going_from labwith_inner_rules labwith_st) in
(*	print_endline "labwith_rs";*)
(*	pr_rl use_labwith_inner_rules;*)
	(label_with_inner_rules use_tolab_inner_rules use_labwith_inner_rules lab_table to_do_list);;

(* ==================================================================================================== *)
(* ***** Labelling of inner rules wrt. inner rules                                                      *)
(* ==================================================================================================== *)

let rec label_inner tolab_inner_rules labwith_inner_rules lab_table to_do_list =
(*	print_string "todo:";print_todo to_do_list;print_newline();*)
	match to_do_list with
	[] -> lab_table
	| (tolab_from,labwith_from)::to_do_list_rest ->    
		let (new_lab_table,new_to_do_list) = 
			(label_inner_from tolab_from labwith_from tolab_inner_rules labwith_inner_rules lab_table to_do_list_rest) in
		(label_inner tolab_inner_rules labwith_inner_rules new_lab_table new_to_do_list);;

(* ==================================================================================================== *)
(* ***** Global label table                                                                             *)
(* ==================================================================================================== *)

(* *** The labels are strings. We keep the table ordered! *)

let lab_list_to_string lab_list pred_name = 
	String.concat "" (pred_name::(List.map Term.to_string lab_list));;

let rec add_to_glob_lab_table glob_lab_table st lab_list pred_name =
	match glob_lab_table with
		[] -> [ (st, (lab_list_to_string lab_list pred_name)) ]
		| (st2,lab_string)::glob_lab_table_rest -> 
		if st=st2 then 
			(st,(String.concat "_" [lab_string; (lab_list_to_string lab_list pred_name)]))::glob_lab_table_rest
		else if st2>st then 
			(st, (lab_list_to_string lab_list pred_name))::((st2,lab_string)::glob_lab_table_rest)
		else 
			(st2,lab_string)::(add_to_glob_lab_table glob_lab_table_rest st lab_list pred_name);;

(* ==================================================================================================== *)
(* ***** Labelling by backward languages with "each automaton state = 1 predicate"                      *)
(* ==================================================================================================== *)

let rec leaf_and_inner_rules rules =
	match rules with
	[] -> ([],[])
	| rule::rules_rest -> 
		let (leaf_rules_rest,inner_rules_rest) = (leaf_and_inner_rules rules_rest) in
		if (is_leaf_rule rule) then 
			(rule::leaf_rules_rest,inner_rules_rest)
		else 
			(leaf_rules_rest,rule::inner_rules_rest);;

(* ==================================================================================================== *)

let label_by_states_of_pred tolab_leaf_rules tolab_inner_rules pred =
	let (labwith_leaf_rules,labwith_inner_rules) = 
		leaf_and_inner_rules (Rewrite.to_list (Automaton.get_transitions pred)) in
	let (lab_table,to_do_list) = (label_with_leaf_rules tolab_leaf_rules labwith_leaf_rules [] []) in
    (label_inner tolab_inner_rules labwith_inner_rules lab_table to_do_list);;

(* ==================================================================================================== *)

(* *** Could be further optimised by not always going through the entire global table. *)

let rec add_lab_table_to_glob_lab_table lab_table glob_lab_table pred_name =
	match lab_table with
	[] -> glob_lab_table
	| (st,lab_list)::lab_table_rest ->
 		let new_glob_lab_table = (add_lab_table_to_glob_lab_table lab_table_rest glob_lab_table pred_name) in
		(add_to_glob_lab_table new_glob_lab_table st lab_list pred_name);;

(* ==================================================================================================== *)

let rec do_label_by_states_of_preds tolab_leaf_rules tolab_inner_rules preds =
	match preds with
	[] -> []
	| (pred_name,pred)::preds_rest ->
		let glob_lab_table = (do_label_by_states_of_preds tolab_leaf_rules tolab_inner_rules preds_rest) in
		let lab_table = (label_by_states_of_pred tolab_leaf_rules tolab_inner_rules pred) in
		(add_lab_table_to_glob_lab_table lab_table glob_lab_table pred_name);;

(* ==================================================================================================== *)

let rec special_to_const_in_lab lab_table =
	match lab_table with
	[] -> []
	| (Common.Special const,label)::lab_table_rest -> (const,label)::(special_to_const_in_lab lab_table_rest)
	| _ -> failwith"special_to_const_in_lab"

let label_by_states_of_preds tolab preds =
	let (tolab_leaf_rules,tolab_inner_rules) = leaf_and_inner_rules (Rewrite.to_list (Automaton.get_transitions tolab)) in
	let lab_table = (do_label_by_states_of_preds tolab_leaf_rules tolab_inner_rules preds) in
	(special_to_const_in_lab lab_table);;

(* ==================================================================================================== *)
(* ***** Adding dummy labels for states not otherwise labelled...                                       *)
(* ==================================================================================================== *)


let rec do_add_dummy_labels states lab_list =
	if (State_set.is_empty states) then lab_list
	else 
	let state,states_rest = State_set.first states,State_set.remainder states in
(*       Printf.printf "STATE:%s\n" (Term.to_string state);*)
(*       Printf.printf "STATES_REST:(%s)\n" (String.concat "," (List.map Term.to_string (State_set.to_list states_rest)));*)
(*       print_endline "LAB_LIST";*)
(*       List.map print_one lab_list;*)
	if (is_labelled lab_list state) then 
		do_add_dummy_labels states_rest lab_list  
	else 
		(state,"-")::(do_add_dummy_labels states_rest lab_list)

(* ==================================================================================================== *)
(* ***** Collapsing automata labelled by predicates "each automaton state = 1 predicate"                *)
(* ==================================================================================================== *)


let bw_coll_allstpred aut pred_list =
	let lab_list = label_by_states_of_preds aut pred_list in
(*  print_endline "LAB_LIST:";*)
(*  List.iter print_one lab_list;*)
	let complete_lab_list = do_add_dummy_labels (Automaton.get_states aut) lab_list in
(*  print_endline "COMPLETE_LAB_LIST:";*)
(*  List.iter print_one complete_lab_list;*)
    do_bw_coll aut complete_lab_list;;
 
