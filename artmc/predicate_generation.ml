open Taml;;
open Rotation;;
open Transducer_st_pres;;
open Create_transducers;;
open Input;;
	   
let set_of_comb=create_alpha_combination_as_list ["x";"y"];;

let lhs=x_ass_y_get_elements_contains_discontains [] ["x"] set_of_comb;;

List.map (x_ass_y_get_rhs [] ["y"] ["x";"y"]) lhs;;

let rec pred_create_rules_ll label_set  st_left st_right st_out =
	match label_set with [] -> Rewrite.empty |
	first::rest ->
		let symbol=Symbol.of_string first in
		let new_lhs=Common.Fsym(symbol,[st_left ;st_right]) in
		let processed_rest=pred_create_rules_ll rest st_left st_right st_out in
		Rewrite.add 
			(Rewrite.new_rule new_lhs st_out)
			processed_rest;;

let pred_create_rules label_set st_left st_right st_out =
	let st_l=Common.Special(Common.Const(Symbol.of_string st_left)) in
	let st_r=Common.Special(Common.Const(Symbol.of_string st_right)) in
	let st_o=Common.Special(Common.Const(Symbol.of_string st_out)) in
	pred_create_rules_ll label_set st_l st_r st_o;;

let rec transform_and_add_data_ll symbols data =
	match data with [] -> [] |
	first::rest ->
		String.concat "" (symbols@[first]) 
		:: transform_and_add_data_ll symbols rest;;

let rec transform_and_add_data symbols_list data=
	match symbols_list with [] -> [] |
	first::rest -> transform_and_add_data_ll first data 
		@ transform_and_add_data rest data;;

let rec big_rewrite_union in_list=
	match in_list with [] -> Rewrite.empty |
	first::rest ->
		Rewrite.union first (big_rewrite_union rest);;

let create_all_rules x var_list data_list =
	let set_of_comb=create_alpha_combination_as_list var_list in
	let cont_x=x_ass_y_get_elements_contains_discontains [x] [] set_of_comb in
	let notcont_x=x_ass_y_get_elements_contains_discontains [] [x] set_of_comb in
	
	let cont_x_data=transform_and_add_data cont_x data_list in
	let notcont_x_data=transform_and_add_data notcont_x data_list in
	let cont_null=transform_and_add_data cont_x ["NULL"] in
	let notcont_null=transform_and_add_data notcont_x ["NULL"] in
	let cont_undef=transform_and_add_data cont_x ["UNDEF"] in
	let notcont_undef=transform_and_add_data notcont_x ["UNDEF"] in
	let generic=transform_and_add_data set_of_comb (data_list@["NULL";"UNDEF"]) in
	
	let r1=pred_create_rules cont_x_data "q1" "q1" "qx" in
	let r2=pred_create_rules cont_x_data "qx" "q1" "qb" in
	let r3=pred_create_rules cont_x_data "q1" "qx" "qb" in
	let r4=pred_create_rules cont_x_data "qx" "qx" "qb" in
	let r5=pred_create_rules notcont_x_data "q1" "q1" "q1" in
	let r6=pred_create_rules notcont_x_data "qx" "q1" "qx" in
	let r7=pred_create_rules notcont_x_data "q1" "qx" "qx" in
	let r8=pred_create_rules notcont_x_data "qx" "qx" "qb" in
	let r9=pred_create_rules generic "qb" "q1" "qb" in
	let r10=pred_create_rules generic "qb" "qb" "qb" in
	let r11=pred_create_rules generic "q1" "qb" "qb" in
	let r12=pred_create_rules generic "qx" "qb" "qb" in
	let r13=pred_create_rules generic "qb" "qx" "qb" in

	let r14=pred_create_rules cont_null "q1" "qbot" "qxnull" in
	let r15=pred_create_rules cont_null "qx" "qbot" "qb" in
	let r16=pred_create_rules notcont_null "qx" "qbot" "qxnull" in
	let r17=pred_create_rules notcont_null "q1" "qbot" "qnull" in
	let r18=pred_create_rules cont_undef "qnull" "qbot" "qxundef" in
	let r19=pred_create_rules cont_undef "qx" "qbot" "qb" in
	let r20=pred_create_rules notcont_undef "qxnull" "qbot" "qxundef" in
	let r21=pred_create_rules notcont_undef "qnull" "qbot" "qb" in

	let r22=pred_create_rules ["normal"] "qxundef" "qbot" "qacc" in
	let r23=pred_create_rules ["normal"] "qb" "qbot" "qb" in
	let r24=pred_create_rules ["bad"] "qxundef" "qbot" "qb" in
	let r25=pred_create_rules ["bad"] "qb" "qbot" "qb" in

	let r26=pred_create_rules ["bot2"] "qbot" "qbot" "q1" in
	let r27=pred_create_rules ["bot2"] "qbot" "qbot" "qbot" in
	let big_union=big_rewrite_union [r1;r2;r3;r4;r5;r6;r7;r8;r9;r10;r11;r12;r13;r14;r15;r16;r17;r18;r19;r20;r21;r22;r23;r24;r25;r26;r27] in

	let init_rule=Rewrite.new_rule
		(Common.Const(Symbol.of_string "bot0"))
		(Common.Special(Common.Const(Symbol.of_string "qbot"))) in
	Rewrite.add init_rule big_union ;;

let create_predicate_automaton x var_list data_list=
	let make_state xx=Common.Const (Symbol.of_string xx) in
	let alpha=create_alphabeth  var_list data_list in
	let state_ops=alphabet "q1:0 qx:0 qb:0 qbot:0 qxnull:0 qxundef:0 qnull:0 qacc:0" in
	let states=State_set.list_to_set(List.map make_state ["q1";"qx";"qb";"qbot";"qxnull";"qxundef";"qnull";"qacc"]) in
	let final_states=State_set.list_to_set(List.map make_state ["qb"]) in
	let rules=create_all_rules x var_list data_list in
	Automaton.make_automaton
		alpha
		state_ops
		states
		final_states
		Rewrite.empty
		rules;;

(** let pred_x=create_predicate_automaton "x" ["root";"x";"y"] ["marked";"unmarked"];; **)
(** let pred_y=create_predicate_automaton "y" ["root";"x";"y"] ["marked";"unmarked"];; **)

(* let pred_x=create_predicate_automaton "x" ["root";"x";"xp";"xpp";"y"] ["red";"black"];; *)
(* let pred_xp=create_predicate_automaton "xp" ["root";"x";"xp";"xpp";"y"] ["red";"black"];; *)
(* let pred_xpp=create_predicate_automaton "xpp" ["root";"x";"xp";"xpp";"y"] ["red";"black"];; *)
(* let pred_y=create_predicate_automaton "y" ["root";"x";"xp";"xpp";"y"] ["red";"black"];; *)

(* let pred_l=create_predicate_automaton "l" ["l";"a";"x";"o"] ["odd";"even"];;*)
(* let pred_a=create_predicate_automaton "a" ["l";"a";"x";"o"] ["odd";"even"];;*)
(* let pred_x=create_predicate_automaton "x" ["l";"a";"x";"o"] ["odd";"even"];;*)
(* let pred_o=create_predicate_automaton "o" ["l";"a";"x";"o"] ["odd";"even"];;*)

(*let pred_x=create_predicate_automaton "x" ["root";"x";"y"]["marked";"unmarked"];;*)
(*let pred_y=create_predicate_automaton "y" ["root";"x";"y"]["marked";"unmarked"];;*)


(******** Tomas: additional functions for generating predicates that distinguish nodes with different data *******)

(****** Note: these automata do not contain the NULL and UNDEF sections: we do not care about them... ******)
(****** We also do not care of how many times various variables appear in the predicates... *****)

let create_all_data_rules given_data var_list data_list =
	let all_var_comb=create_alpha_combination_as_list var_list in
	let all_var_comb_with_all_data=transform_and_add_data all_var_comb data_list in
	let all_var_comb_with_given_data=transform_and_add_data all_var_comb [ given_data ] in
	
	let r1=pred_create_rules all_var_comb_with_all_data "q1" "q1" "q1" in
	let r2=pred_create_rules all_var_comb_with_given_data "q1" "q1" "q2" in

	let r3=pred_create_rules ["bot2"] "qbot" "qbot" "q1" in
	let r4=pred_create_rules ["bot2"] "qbot" "qbot" "qbot" in

	let big_union=big_rewrite_union [r1;r2;r3;r4] in

	let init_rule=Rewrite.new_rule
		(Common.Const(Symbol.of_string "bot0"))
		(Common.Special(Common.Const(Symbol.of_string "qbot"))) in
	Rewrite.add init_rule big_union ;;

let create_data_predicate_automaton given_data var_list data_list=
	let make_state xx=Common.Const (Symbol.of_string xx) in
	let alpha=create_alphabeth  var_list data_list in
	let state_ops=alphabet "qbot:0 q1:0 q2:0" in
	let states=State_set.list_to_set(List.map make_state ["qbot";"q1";"q2"]) in
	let final_states=State_set.list_to_set(List.map make_state ["q2"]) in
	let rules=create_all_data_rules given_data var_list data_list in
	Automaton.make_automaton
		alpha
		state_ops
		states
		final_states
		Rewrite.empty
		rules;;


(*********************************************************************************************************************)
