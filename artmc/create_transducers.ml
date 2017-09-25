open Taml;;
(* ****************************************************************************** *)
(* ****************************************************************************** *)
(* This file contains functions to create transducers for selected commands       *)
(*                                                                                *)
(* Adam Rogalewicz                                                                *)
(* ****************************************************************************** *)
(* ****************************************************************************** *)

(* ****************************************************************************** *)
(* General functions                                                              *)
(* ****************************************************************************** *)

let concat_2strings str1 str2 =
(* concat 2 strings *)
	String.concat "" [str1; str2];;

let rec create_alpha_combination_as_list symbol_set =
(* INPUT: a set
   OUTPUT: a potential set (set of all subsets) *)
	match symbol_set with [] -> [[]] |
	first::rest ->
		List.map (List.append [first]) (create_alpha_combination_as_list rest)
		@ (create_alpha_combination_as_list rest);;
	
(* Comparison of two elements by its order in given list *)
exception Error_in_sorting;;

let rec compare_by_given_list_ll in_list a b =
	match in_list with [] -> raise Error_in_sorting |
	first::rest ->
		if (first=a) then -1
		else
		if (first=b) then 1
		else compare_by_given_list_ll rest a b;;

let compare_by_given_list in_list a b  =
	if ((List.mem a in_list)&&(List.mem b in_list)) then
		compare_by_given_list_ll in_list a b
	else raise Error_in_sorting;;

(* INPUT: set_of_comb (A) - set of lists
   OUTPUT: subset of set A, where each element contains all elements from inside,
           and does not contain any element from restrict *)
let rec x_ass_y_get_elements_contains_discontains inside restrict set_of_comb =
	let not_list_mem x y=not (List.mem y x) in
	let list_mem x y=List.mem y x in
	let not_intersect_with_restricted x= 
		[] = (List.filter (list_mem restrict) x) in
	let intersect_with_inside x=
		[] = (List.filter (not_list_mem x) inside) in
	match set_of_comb with [] -> [] |
	first::rest ->
		if (not_intersect_with_restricted first && intersect_with_inside first) then
			first :: x_ass_y_get_elements_contains_discontains inside restrict rest 
		else x_ass_y_get_elements_contains_discontains inside restrict rest;;

(* Create RHS based on lhs - add elements in list add, and remove elements in list "remove" *)
let x_ass_y_get_rhs add remove order lhs=
	let not_list_mem x y=not (List.mem y x) in
	let added=lhs @ (List.filter (not_list_mem lhs) add) in
	let rhs_unserted=List.filter (not_list_mem remove) added in
	let rhs = List.sort (compare_by_given_list order) rhs_unserted in
	(lhs,rhs);;

(* Transform rules, and combine it with data values
   INPUT: set of rules of the type ([x,y,z,...],[q,r,s,...]); set of data values
   OUTPUT: ("xyz...data1","qrs...data1"),("xyz...data2","qrs...data2"), ... *)
let rec x_ass_y_transform_rules_and_add_data_ll rule data =
	match data with [] -> [] |
	first::rest ->
		match rule with (a,b) ->
			(String.concat "" (a@[first]), String.concat "" (b@[first])) 
			:: x_ass_y_transform_rules_and_add_data_ll rule rest;;

let rec x_ass_y_transform_rules_and_add_data rules_orig data=
	match rules_orig with [] -> [] |
	first::rest -> x_ass_y_transform_rules_and_add_data_ll first data 
		@ x_ass_y_transform_rules_and_add_data rest data;;

(* This function is equal to previews one, but combine with data ONLY lhs of rule *)
(* Transform rules, and combine its lhs with data values
   INPUT: set of rules of the type ([x,y,z,...],[q,r,s,...]); set of data values
   OUTPUT: ("xyz...data1","qrs..."),("xyz...data2","qrs..."), ... *)
let rec x_ass_y_transform_rules_and_add_data_on_LHS_ll rule data =
	match data with [] -> [] |
	first::rest ->
		match rule with (a,b) ->
			(String.concat "" (a@[first]), String.concat "" b) 
			:: x_ass_y_transform_rules_and_add_data_on_LHS_ll rule rest;;

let rec x_ass_y_transform_rules_and_add_data_on_LHS rules_orig data=
	match rules_orig with [] -> [] |
	first::rest -> x_ass_y_transform_rules_and_add_data_on_LHS_ll first data 
		@ x_ass_y_transform_rules_and_add_data_on_LHS rest data;;

(* create transducer rules:
   INPUT: set of pairs (x,y)
   OUTPUT set of rules (x,[st1,st2],y,st3) *)
let rec x_ass_y_create_rules rulebase st1 st2 st3= 
	match  rulebase with [] -> [] |
	(x,y)::rest ->
		(x,[st1;st2],y,st3)::x_ass_y_create_rules rest st1 st2 st3;;

(* ****************************************************************************** *)
(* y:=x                                                                           *)
(* ****************************************************************************** *)

(* Now create rules with x in LHS *)
let x_ass_y_create_rules_with_x x y set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [x] [] set_of_comb in
	(*let lhs=x_ass_y_get_elements_with_x x set_of_comb in*)
	List.map (x_ass_y_get_rhs [y] [] set_of_symbols) lhs;;

(* Create rules without y in LHS *)
let x_ass_y_create_rules_without_x x y set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [x] set_of_comb in
	List.map (x_ass_y_get_rhs [] [y] set_of_symbols) lhs;;

(* Create transducer for command y:=x
   INPUT: x,y, list of variables(x nad y must be inside), list of data values
   OUTPUT: transducer structure *)
let create_transducer_x_ass_y x y var_list data_list conf_id1 conf_id2 conf_idbad =
	(* Create LHS without data *)
	let prerules_with_x=x_ass_y_create_rules_with_x x y var_list in
	let prerules_without_x=x_ass_y_create_rules_without_x x y var_list in
	
	(* Add data nad RHS *)
	let rulebase1=x_ass_y_transform_rules_and_add_data prerules_with_x data_list in 
	let rulebase2=x_ass_y_transform_rules_and_add_data prerules_without_x data_list in
	let rulebase_null1=x_ass_y_transform_rules_and_add_data prerules_with_x ["NULL"] in
	let rulebase_null2=x_ass_y_transform_rules_and_add_data prerules_without_x ["NULL"] in
	let rulebase_undef1=x_ass_y_transform_rules_and_add_data prerules_with_x ["UNDEF"] in
	let rulebase_undef2=x_ass_y_transform_rules_and_add_data prerules_without_x ["UNDEF"] in
	
	(* Create final rules *)
	let rules=(x_ass_y_create_rules rulebase1 "q1" "q1" "q1")@
		(x_ass_y_create_rules rulebase2 "q1" "q1" "q1")@
		(x_ass_y_create_rules rulebase_null1 "q1" "q1" "qnull")@
		(x_ass_y_create_rules rulebase_null2 "q1" "q1" "qnull")@
		(x_ass_y_create_rules rulebase_undef1 "qnull" "q1" "qundefbad")@
		(x_ass_y_create_rules rulebase_undef2 "qnull" "q1" "qundef") in

	let top_line_rule =[(conf_id1,["qundef";"q1"],conf_id2,"qfin");(conf_id1,["qundefbad";"q1"],conf_idbad,"qfin")] in
	let init_rules=[("bot0",[],"bot0","q1");("bot2",["q1";"q1"],"bot2","q1")] in

		(["q1";"qnull";"qundef";"qfin";"qundefbad"],["qfin"],rules@init_rules@top_line_rule);;


(* ****************************************************************************** *)
(* y=x.left                                                                       *)
(* y=x.right                                                                       *)
(* ****************************************************************************** *)


(* create rules: *)
let x_ass_ynext_create_rules_without_x x y set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [x] set_of_comb in
	(*let lhs=x_ass_y_get_elements_with_x x set_of_comb in*)
	List.map (x_ass_y_get_rhs [] [y] set_of_symbols) lhs;;

let x_ass_ynext_create_rules_with_without_x2 x y set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [x] set_of_comb in
	(*let lhs=x_ass_y_get_elements_with_x x set_of_comb in*)
	List.map (x_ass_y_get_rhs [y] [] set_of_symbols) lhs;;

let x_ass_ynext_create_rules_with_x x y set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [x] [] set_of_comb in
	(*let lhs=x_ass_y_get_elements_with_x x set_of_comb in*)
	List.map (x_ass_y_get_rhs [] [y] set_of_symbols) lhs;;

let x_ass_ynext_create_rules_null_undef_without_x x y set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [x] set_of_comb in
	(*let lhs=x_ass_y_get_elements_with_x x set_of_comb in*)
	List.map (x_ass_y_get_rhs [] [y] set_of_symbols) lhs;;

let x_ass_ynext_create_rules_null_undef_with_x x y set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [x] [] set_of_comb in
	(*let lhs=x_ass_y_get_elements_with_x x set_of_comb in*)
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let x_ass_ynext_create_rules_all_comb set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [] set_of_comb in
	(*let lhs=x_ass_y_get_elements_with_x x set_of_comb in*)
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

	
		
let create_transducer_y_ass_xnext x y var_list data_list conf_id1 conf_id2 conf_idbad direction=
(* direction \in {left; right} *)
	let rulebase1=x_ass_y_transform_rules_and_add_data 
		(x_ass_ynext_create_rules_without_x x y var_list) 
		data_list in
	let rulebase2=x_ass_y_transform_rules_and_add_data 
		(x_ass_ynext_create_rules_with_without_x2  x y var_list)
		data_list in
	let rulebase3=x_ass_y_transform_rules_and_add_data 
		(x_ass_ynext_create_rules_with_x  x y var_list)
		data_list in
	let rulebase_null_set_y=x_ass_y_transform_rules_and_add_data 
		(x_ass_ynext_create_rules_with_without_x2  x y var_list)
		["NULL"] in
	let rule_base_null_ok=x_ass_y_transform_rules_and_add_data
		(x_ass_ynext_create_rules_null_undef_without_x x y var_list)
		["NULL"] in
	let rule_base_undef_ok=x_ass_y_transform_rules_and_add_data
		(x_ass_ynext_create_rules_null_undef_without_x x y var_list)
		["UNDEF"] in
	let rule_base_null_bad=x_ass_y_transform_rules_and_add_data
		(x_ass_ynext_create_rules_null_undef_with_x x y var_list)
		["NULL"] in
	let rule_base_undef_bad=x_ass_y_transform_rules_and_add_data
		(x_ass_ynext_create_rules_null_undef_with_x x y var_list)
		["UNDEF"] in
	let rule_base_allcombinations = x_ass_y_transform_rules_and_add_data
		(x_ass_ynext_create_rules_all_comb var_list) 
		["UNDEF"] in
		
	let rules_1=(x_ass_y_create_rules rulebase1 "q1" "q1" "q1")@
		(x_ass_y_create_rules rulebase2 "q1" "q1" "qy") @
		(x_ass_y_create_rules rule_base_null_ok "q1" "q1" "qnull") @
		(x_ass_y_create_rules rule_base_undef_ok "qnull" "q1" "qundef") @
		(x_ass_y_create_rules rule_base_null_bad "q1" "q1" "qnullbad") @
		(x_ass_y_create_rules rule_base_undef_bad "qnull" "q1" "qundefbad") @
		(x_ass_y_create_rules rule_base_allcombinations "qnullbad" "q1" "qundefbad") @
		(* rules for case x.next=NULL *)
		(x_ass_y_create_rules rulebase1 "qytonull" "q1" "qytonull")@
		(x_ass_y_create_rules rulebase1 "q1" "qytonull" "qytonull") @
		(x_ass_y_create_rules rulebase_null_set_y "qytonull" "q1" "qnull")
		in
	let top_line_rule =[(conf_id1,["qundef";"q1"],conf_id2,"qfin");(conf_id1,["qundefbad";"q1"],conf_idbad,"qfin")] in
	let init_rules=[("bot0",[],"bot0","qbot");("bot2",["qbot";"qbot"],"bot2","qbot");("bot2",["qbot";"qbot"],"bot2","q1")] in
	(* There is just one diference between x=y.left, x=y.right *)
	if direction="left" then
		let rules=rules_1 @ 
			(x_ass_y_create_rules rulebase3 "qy" "q1" "q1") @
			(x_ass_y_create_rules rulebase3 "qbot" "q1" "qytonull") in
		(["qbot";"q1";"qy";"qnull";"qundef";"qfin";"qnullbad";"qundefbad";"qytonull"],["qfin"],rules@init_rules@top_line_rule)
	else
		let rules=rules_1 @ 
			(x_ass_y_create_rules rulebase3 "q1" "qy" "q1") @
			(x_ass_y_create_rules rulebase3 "q1" "qbot" "qytonull") in
		(["qbot";"q1";"qy";"qnull";"qundef";"qfin";"qnullbad";"qundefbad";"qytonull"],["qfin"],rules@init_rules@top_line_rule);;



let create_transducer_y_ass_xUP x y var_list data_list conf_id1 conf_id2 conf_idbad =
(* This function creates transducer for operation y:=x.up *)
	let rulebase1=x_ass_y_transform_rules_and_add_data 
		(x_ass_ynext_create_rules_without_x x y var_list) 
		data_list in (* NOT x, REMOVE y *)
	let rulebase2=x_ass_y_transform_rules_and_add_data 
		(x_ass_ynext_create_rules_with_without_x2  x y var_list)
		data_list in (* NOT x, SET y *)
	let rulebase3=x_ass_y_transform_rules_and_add_data 
		(x_ass_ynext_create_rules_with_x  x y var_list)
		data_list in (* x, REMOVE y *)
	let rulebase_null_set_y=x_ass_y_transform_rules_and_add_data 
		(x_ass_ynext_create_rules_with_without_x2  x y var_list)
		["NULL"] in (* NOT x, SET y *)
	let rule_base_null_ok=x_ass_y_transform_rules_and_add_data
		(x_ass_ynext_create_rules_null_undef_without_x x y var_list)
		["NULL"] in (* NOT x, REMOVE y *)
	let rule_base_undef_ok=x_ass_y_transform_rules_and_add_data
		(x_ass_ynext_create_rules_null_undef_without_x x y var_list)
		["UNDEF"] in (* NOT x, REMOVE y *)
	let rule_base_null_bad=x_ass_y_transform_rules_and_add_data
		(x_ass_ynext_create_rules_null_undef_with_x x y var_list)
		["NULL"] in (* X NULL => error *)
	let rule_base_undef_bad=x_ass_y_transform_rules_and_add_data
		(x_ass_ynext_create_rules_null_undef_with_x x y var_list)
		["UNDEF"] in (* X UNDEF => error *)
	let rule_base_allcombinations = x_ass_y_transform_rules_and_add_data
		(x_ass_ynext_create_rules_all_comb var_list) 
		["UNDEF"] in (* GENERIC RULE *)
		
	let rules=(x_ass_y_create_rules rulebase1 "q1" "q1" "q1")@
		(x_ass_y_create_rules rulebase2 "qx" "q1" "q1") @
		(x_ass_y_create_rules rulebase2 "q1" "qx" "q1") @
		(x_ass_y_create_rules rulebase3 "q1" "q1" "qx") @

		(x_ass_y_create_rules rule_base_null_ok "q1" "q1" "qnull") @
		(x_ass_y_create_rules rule_base_undef_ok "qnull" "q1" "qundef") @
		(x_ass_y_create_rules rule_base_null_bad "q1" "q1" "qnullbad") @
		(x_ass_y_create_rules rule_base_undef_bad "qnull" "q1" "qundefbad") @
		(x_ass_y_create_rules rule_base_allcombinations "qnullbad" "q1" "qundefbad") @
		(* rules for case x.up=NULL *)
		(x_ass_y_create_rules rulebase_null_set_y "qx" "q1" "qnull")
		
		in
	let top_line_rule =[(conf_id1,["qundef";"q1"],conf_id2,"qfin");(conf_id1,["qundefbad";"q1"],conf_idbad,"qfin")] in
	let init_rules=[("bot0",[],"bot0","qbot");("bot2",["qbot";"qbot"],"bot2","qbot");("bot2",["qbot";"qbot"],"bot2","q1")] in
	(["qbot";"q1";"qx";"qnull";"qundef";"qfin";"qnullbad";"qundefbad";"qytonull"],["qfin"],rules@init_rules@top_line_rule);;

(* ****************************************************************************** *)
(* x=null                                                                         *)
(* ****************************************************************************** *)

(* create rules: *)
let x_ass_null_create_rules_del_x x set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [] set_of_comb in
	(*let lhs=x_ass_y_get_elements_with_x x set_of_comb in*)
	List.map (x_ass_y_get_rhs [] [x] set_of_symbols) lhs;;

let x_ass_null_create_rules_add_x x set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [] set_of_comb in
	(*let lhs=x_ass_y_get_elements_with_x x set_of_comb in*)
	List.map (x_ass_y_get_rhs [x] [] set_of_symbols) lhs;;


let create_transducer_x_ass_null x var_list data_list conf_id1 conf_id2 =
	(* Create LHS without data *)
	let prerules_del_x=x_ass_null_create_rules_del_x x var_list in
	let prerules_add_x=x_ass_null_create_rules_add_x x var_list in

	(* Add data nad RHS *)
	let rulebase1=x_ass_y_transform_rules_and_add_data prerules_del_x data_list in
	let rulebase2=x_ass_y_transform_rules_and_add_data prerules_add_x ["NULL"] in
	let rulebase3=x_ass_y_transform_rules_and_add_data prerules_del_x ["UNDEF"] in
	
	(* Create final rules *)
	let rules=(x_ass_y_create_rules rulebase1 "q1" "q1" "q1")@
		(x_ass_y_create_rules rulebase2 "q1" "q1" "qnull")@
		(x_ass_y_create_rules rulebase3 "qnull" "q1" "qundef") in
		
	let init_rules=[("bot0",[],"bot0","q1");("bot2",["q1";"q1"],"bot2","q1")] in
	let top_line_rule =[(conf_id1,["qundef";"q1"],conf_id2,"qfin")] in
		
	(["q1";"qnull";"qundef";"qfin"],["qfin"],rules@init_rules@top_line_rule);;


(***********************************************************************************)
(* IF x=y                                                                          *)
(***********************************************************************************)

(* create rules: *)

let if_x_eq_y_create_rules_EQ x y set_of_symbols =
	(* rules for node with x, and y *)
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [x;y] [] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let if_x_eq_y_create_rules_NONEQ x y set_of_symbols =
	(* rules for nodes without x, or y *)
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=(x_ass_y_get_elements_contains_discontains [y] [x] set_of_comb)@
		(x_ass_y_get_elements_contains_discontains [x] [y] set_of_comb)@
		(x_ass_y_get_elements_contains_discontains [] [x;y] set_of_comb) in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let if_x_eq_y_create_rules_not_contains x y set_of_symbols =
	(* Node does not contain values x, and y *)
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [x;y] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let if_x_eq_y_create_rules_contains x y set_of_symbols =
	(* Node contains values x, and y *)
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=(x_ass_y_get_elements_contains_discontains [y] [x] set_of_comb)@
		(x_ass_y_get_elements_contains_discontains [x] [y] set_of_comb)@
		(x_ass_y_get_elements_contains_discontains [x;y] [] set_of_comb) in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let create_transducer_x_eq_y x y var_list data_list conf_id1 conf_then conf_else conf_ERR =
	let prerules_eq=if_x_eq_y_create_rules_EQ x y var_list in
	let prerules_noneq=if_x_eq_y_create_rules_NONEQ x y var_list in
	let prerules_undef1=if_x_eq_y_create_rules_contains x y var_list in
	let prerules_undef2=if_x_eq_y_create_rules_not_contains x y var_list in
	(* ADD data values *)
	let rulebase1=x_ass_y_transform_rules_and_add_data prerules_eq (data_list@["NULL"]) in
	let rulebase2=x_ass_y_transform_rules_and_add_data prerules_noneq (data_list@["NULL"]) in
	let rulebase3=x_ass_y_transform_rules_and_add_data prerules_undef2 (data_list@["NULL"]) in
	let rulebase_undef1=x_ass_y_transform_rules_and_add_data prerules_undef1 ["UNDEF"] in
	let rulebase_undef2=x_ass_y_transform_rules_and_add_data prerules_undef2 ["UNDEF"] in
	(* Create final rules *)
	let rulescommon=(x_ass_y_create_rules rulebase1 "q1" "q1" "qeq")@
		(x_ass_y_create_rules rulebase2 "q1" "q1" "q1")@
		(x_ass_y_create_rules rulebase3 "qeq" "q1" "qeq")@
		(x_ass_y_create_rules rulebase3 "q1" "qeq" "qeq") in
	
	let rules_then=(x_ass_y_create_rules rulebase_undef2 "qeq" "q1" "qacc")@
			[(conf_id1,["qacc";"q1"],conf_then,"qfin")] in	
	let rules_else=(x_ass_y_create_rules rulebase_undef2 "q1" "q1" "qacc") @
			(x_ass_y_create_rules rulebase_undef1 "q1" "q1" "qerr")@
			[(conf_id1,["qacc";"q1"],conf_else,"qfin");(conf_id1,["qerr";"q1"],conf_ERR,"qfin") ] in	
	
	let init_rules=[("bot0",[],"bot0","q1");("bot2",["q1";"q1"],"bot2","q1")] in
	
	(* Create then and else transducers *)
	((["q1";"qeq";"qacc";"qfin"],["qfin"],init_rules@rulescommon@rules_then),
	(["q1";"qeq";"qacc";"qfin";"qerr"],["qfin"],init_rules@rulescommon@rules_else));;


(***********************************************************************************)
(* IF x=NULL                                                                          *)
(***********************************************************************************)

let if_x_eq_null_create_rules_cont_x x set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [x] [] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let if_x_eq_null_create_rules_discont_x x set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [x] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let if_x_eq_null_create_rules_generic set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let create_transducer_x_eq_null x var_list data_list conf_id1 conf_then conf_else conf_ERR =
	let prerules_cont=if_x_eq_null_create_rules_cont_x x var_list in
	let prerules_notcont=if_x_eq_null_create_rules_discont_x x var_list in
	let prerules_gen=if_x_eq_null_create_rules_generic var_list in
	(* ADD data values *)
	let rulebase1=x_ass_y_transform_rules_and_add_data prerules_gen data_list in
	let rulebase_null1=x_ass_y_transform_rules_and_add_data prerules_cont ["NULL"] in
	let rulebase_null2=x_ass_y_transform_rules_and_add_data prerules_notcont ["NULL"] in
	let rulebase_undef1=x_ass_y_transform_rules_and_add_data prerules_cont ["UNDEF"] in
	let rulebase_undef2=x_ass_y_transform_rules_and_add_data prerules_notcont ["UNDEF"] in
	(* Create final rules *)
	let rulescommon=(x_ass_y_create_rules rulebase1 "q1" "q1" "q1") in
	let rules_then=(x_ass_y_create_rules rulebase_null1 "q1" "q1" "qnull")@
			(x_ass_y_create_rules rulebase_undef2 "qnull" "q1" "qok")@
			[(conf_id1,["qok";"q1"],conf_then,"qfin")] in	


	let rules_else=(x_ass_y_create_rules rulebase_null2 "q1" "q1" "qnull")@
			(x_ass_y_create_rules rulebase_undef2 "qnull" "q1" "qok")@
			(x_ass_y_create_rules rulebase_undef1 "qnull" "q1" "qerr")@
			[(conf_id1,["qok";"q1"],conf_else,"qfin");(conf_id1,["qerr";"q1"],conf_ERR,"qfin") ] in	

	let init_rules=[("bot0",[],"bot0","q1");("bot2",["q1";"q1"],"bot2","q1")] in
	(* Create then and else transducers *)
	((["q1";"qeq";"qok";"qnull";"qfin"],["qfin"],init_rules@rulescommon@rules_then),
	(["q1";"qeq";"qok";"qnull";"qfin";"qerr"],["qfin"],init_rules@rulescommon@rules_else));;


(***********************************************************************************)
(* New (x.left)                                                                    *)
(* New (x.right)                                                                    *)
(***********************************************************************************)

let x_letfnew_create_rules_cont_x x set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [x] [] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let x_leftnew_create_rules_discont_x x set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [x] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let x_letfnew_create_rules_generic set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;


let create_transducer_x_left_new  x new_value var_list data_list conf_id1 conf_id2 conf_UNPOSSIBLE conf_ERR direction =
(* direction \in {left; right} *)
	let prerules_cont=x_letfnew_create_rules_cont_x x var_list in
	let prerules_notcont=x_leftnew_create_rules_discont_x x var_list in
	let prerules_generic=x_letfnew_create_rules_generic var_list in
	(* ADD data values *)
	let rulebase1=x_ass_y_transform_rules_and_add_data prerules_cont data_list in
	let rulebase2=x_ass_y_transform_rules_and_add_data prerules_notcont data_list in
	let rulebase_null1=x_ass_y_transform_rules_and_add_data prerules_cont ["NULL"] in
	let rulebase_null2=x_ass_y_transform_rules_and_add_data prerules_notcont ["NULL"] in
	let rulebase_undef1=x_ass_y_transform_rules_and_add_data prerules_cont ["UNDEF"] in
	let rulebase_undef2=x_ass_y_transform_rules_and_add_data prerules_notcont ["UNDEF"] in
	let rulebase_generic=x_ass_y_transform_rules_and_add_data prerules_generic (data_list@["NULL";"UNDEF"]) in
	(* Create rules *)	
	let rules_1=
		(x_ass_y_create_rules rulebase1 "q1" "q1" "qunpos")@
		(x_ass_y_create_rules rulebase2 "q1" "q1" "q1")@
		(x_ass_y_create_rules rulebase2 "qbot" "q1" "q1")@
		(x_ass_y_create_rules rulebase2 "qbot" "qbot" "q1")@
		(x_ass_y_create_rules rulebase2 "q1" "qbot" "q1")@
		(x_ass_y_create_rules rulebase_generic "q1" "qunpos" "qunpos")@
		(x_ass_y_create_rules rulebase_generic "qunpos" "q1" "qunpos")@
		(x_ass_y_create_rules rulebase_null2 "q1" "qbot" "qnull")@
		(x_ass_y_create_rules rulebase_null1 "q1" "qbot" "qerr")@
		(x_ass_y_create_rules rulebase_undef2 "qnull" "qbot" "qok")@
		(x_ass_y_create_rules rulebase_undef1 "qnull" "qbot" "qerr")@
		(x_ass_y_create_rules rulebase_undef2 "qerr" "qbot" "qerr")@
		[(conf_id1,["qok";"qbot"],conf_id2,"qfin");
		(conf_id1,["qerr";"qbot"],conf_ERR,"qfin");
		(conf_id1,["qunpos";"qbot"],conf_UNPOSSIBLE,"qfin");
		("bot2",["qbot";"qbot"],new_value,"qnew")] in
		
	let init_rules=[("bot0",[],"bot0","qbot");("bot2",["qbot";"qbot"],"bot2","qbot")] in
	(* Here is the diference between x.left=new, and x.right=new *)
	if direction="left" then
		let rules=rules_1@
			(x_ass_y_create_rules rulebase1 "qnew" "qbot" "q1")@
			(x_ass_y_create_rules rulebase1 "qnew" "q1" "q1")@
			(x_ass_y_create_rules rulebase1 "q1" "qbot" "qunpos") in
		(["q1";"qbot";"qnew";"qnull";"qok";"qunpos";"qerr";"qfin"],["qfin"],rules@init_rules)
	else
		let rules=rules_1@
			(x_ass_y_create_rules rulebase1 "qbot" "qnew" "q1")@
			(x_ass_y_create_rules rulebase1 "q1" "qnew" "q1") @
			(x_ass_y_create_rules rulebase1 "qbot" "q1" "qunpos") in
		(["q1";"qbot";"qnew";"qnull";"qok";"qunpos";"qerr";"qfin"],["qfin"],rules@init_rules);;
	
(***********************************************************************************)
(* if x->data==value                                                               *)
(***********************************************************************************)

let if_data_create_rules_cont_x x set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [x] [] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let if_data_create_rules_discont_x x set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [x] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let if_data_create_rules_generic set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let create_transducer_if_data x data var_list data_list conf_id1 conf_then conf_else conf_ERR =
	let prerules_cont=if_data_create_rules_cont_x x var_list in
	let prerules_notcont=if_data_create_rules_discont_x x var_list in
	let prerules_gen=if_data_create_rules_generic var_list in
	(* ADD data values *)
	let filterdata value1 value2= not (value1=value2) in
	let rulebase_x1=x_ass_y_transform_rules_and_add_data prerules_cont [data] in
	let rulebase_x2=x_ass_y_transform_rules_and_add_data prerules_cont (List.filter (filterdata data) data_list) in
	let rulebase_notx=x_ass_y_transform_rules_and_add_data prerules_notcont data_list in
	let rulebase_nullundef=x_ass_y_transform_rules_and_add_data prerules_gen ["NULL";"UNDEF"] in

	(* Create rules *)	
	let rulescommon=(x_ass_y_create_rules rulebase_notx "q1" "q1" "q1") in

	let rules_then=
		(x_ass_y_create_rules rulebase_x1 "q1" "q1" "qcont")@
		(x_ass_y_create_rules rulebase_notx "qcont" "q1" "qcont")@
		(x_ass_y_create_rules rulebase_notx "q1" "qcont" "qcont")@
		(x_ass_y_create_rules rulebase_nullundef "qcont" "q1" "qnullcont")@
		(x_ass_y_create_rules rulebase_nullundef "qnullcont" "q1" "qundefcont")@
		[(conf_id1,["qundefcont";"q1"],conf_then,"qfin")] in	
	let rules_else=
		(x_ass_y_create_rules rulebase_x2 "q1" "q1" "qnot_cont")@
		(x_ass_y_create_rules rulebase_notx "qnot_cont" "q1" "qnot_cont")@
		(x_ass_y_create_rules rulebase_notx "q1" "qnot_cont" "qnot_cont")@
		(x_ass_y_create_rules rulebase_nullundef "qnot_cont" "q1" "qnull_notcont")@
		(x_ass_y_create_rules rulebase_nullundef "q1" "q1" "qnullerr")@
		(x_ass_y_create_rules rulebase_nullundef "qnullerr" "q1" "qundeferr")@
		(x_ass_y_create_rules rulebase_nullundef "qnull_notcont" "q1" "qundef_notcont")@
		[(conf_id1,["qundef_notcont";"q1"],conf_else,"qfin");(conf_id1,["qundeferr";"q1"],conf_ERR,"qfin") ] in	

	let init_rules=[("bot0",[],"bot0","q1");("bot2",["q1";"q1"],"bot2","q1")] in
	(* Create then and else transducers *)
	((["q1";"qcont";"qnullcont";"qundefcont";"qfin"],["qfin"],init_rules@rulescommon@rules_then),
	(["q1";"qnot_cont";"qnull_notcont";"qundef_notcont";"qnullerr";"qundeferr";"qfin"],["qfin"],init_rules@rulescommon@rules_else));;

(***********************************************************************************)
(* Dispose (x)                                                                     *)
(***********************************************************************************)

(* !!!!! IMPORTANT
 * This functions suppose, that there is just one pointer variable in disposed node
 * -> It is necessary to move all other variables from this node before runing this procedure *)

let dispose_x_create_rules_generic set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;


let dispose_x_create_rules_not_x x set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [x] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let dispose_x_create_rules_x x set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [x] [] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;
	
let dispose_x_create_rules_x_DISPOSE x set_of_symbols =
	let disposed_rhs lhs=(lhs,["bot2"]) in
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [x] [] set_of_comb in
	List.map (disposed_rhs) lhs;;
	
let dispose_x_create_rules_not_x_undef x set_of_symbols =
(* ADD x into the list of undefined variables *)
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [x] set_of_comb in
	List.map (x_ass_y_get_rhs [x] [] set_of_symbols) lhs;;

let create_transducer_dispose x var_list data_list conf_id1 conf_id2 conf_ERR =
	let prerules_cont=dispose_x_create_rules_x x var_list in
	let prerules_notcont=dispose_x_create_rules_not_x x var_list in
	let prerules_generic=dispose_x_create_rules_generic var_list in
	let prerules_dispose=dispose_x_create_rules_x_DISPOSE x var_list in
	let prerules_undef=dispose_x_create_rules_not_x_undef x var_list in

	(* ADD data values *)
	let rulebase_notx=x_ass_y_transform_rules_and_add_data prerules_notcont data_list in
	let rulebase_x=x_ass_y_transform_rules_and_add_data prerules_cont data_list in
	let rulebase_generic=x_ass_y_transform_rules_and_add_data prerules_generic data_list in
	
	let rulebase_dispose=x_ass_y_transform_rules_and_add_data_on_LHS prerules_dispose data_list in
	let rulebase_null_notx=x_ass_y_transform_rules_and_add_data prerules_notcont ["NULL"] in
	let rulebase_null_x=x_ass_y_transform_rules_and_add_data prerules_cont ["NULL"] in
	let rulebase_null_generic=x_ass_y_transform_rules_and_add_data prerules_generic ["NULL"] in
	let rulebase_undef_x=x_ass_y_transform_rules_and_add_data prerules_cont ["UNDEF"] in
	let rulebase_undef_notx=x_ass_y_transform_rules_and_add_data prerules_undef ["UNDEF"] in
	let rulebase_undef_generic=x_ass_y_transform_rules_and_add_data prerules_generic ["UNDEF"] in
	(* CREATE RULES *)
	let rules=
		(x_ass_y_create_rules rulebase_notx "q1" "q1" "q1") @
		(x_ass_y_create_rules rulebase_notx "qbot" "q1" "q1") @
		(x_ass_y_create_rules rulebase_notx "q1" "qbot" "q1") @
		(x_ass_y_create_rules rulebase_notx "qbot" "qbot" "q1") @
		(x_ass_y_create_rules rulebase_dispose "qbot" "qbot" "q1") @
		(x_ass_y_create_rules rulebase_x "q1" "q1" "qerr") @
		(x_ass_y_create_rules rulebase_x "q1" "qbot" "qerr") @
		(x_ass_y_create_rules rulebase_x "qbot" "q1" "qerr") @
		(x_ass_y_create_rules rulebase_generic "qerr" "q1" "qerr") @
		(x_ass_y_create_rules rulebase_generic "qerr" "qerr" "qerr") @
		(x_ass_y_create_rules rulebase_generic "q1" "qerr" "qerr") @
		(x_ass_y_create_rules rulebase_null_notx "q1" "qbot" "qnull") @
		(x_ass_y_create_rules rulebase_null_x "q1" "qbot" "qnullerr") @
		(x_ass_y_create_rules rulebase_null_generic "qerr" "qbot" "qnullerr") @
		(x_ass_y_create_rules rulebase_undef_notx "qnull" "qbot" "qok") @
		(x_ass_y_create_rules rulebase_undef_x "qnull" "qbot" "qundeferr") @
		(x_ass_y_create_rules rulebase_undef_generic "qnullerr" "qbot" "qundeferr") @

		[(conf_id1,["qok";"qbot"],conf_id2,"qfin");(conf_id1,["qundeferr";"qbot"],conf_ERR,"qfin") ] in	

	let init_rules=[("bot0",[],"bot0","qbot");("bot2",["qbot";"qbot"],"bot2","qbot")] in
	(["qbot";"q1";"qerr";"qnull";"qnullerr";"qok";"qundeferr";"qfin"],["qfin"],init_rules@rules);;

(* Set x to undef, if x=y *)

let set_x_undef_A x y set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [x;y] [] set_of_comb in
	List.map (x_ass_y_get_rhs [] [y] set_of_symbols) lhs;;

let set_x_undef_B x y set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=(x_ass_y_get_elements_contains_discontains [x] [y] set_of_comb)@
		(x_ass_y_get_elements_contains_discontains [y] [x] set_of_comb)@
		(x_ass_y_get_elements_contains_discontains [x] [y] set_of_comb) in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let set_x_undef_set_it y set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [] set_of_comb in
	List.map (x_ass_y_get_rhs [y] [] set_of_symbols) lhs;;
let set_x_undef_generic set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let create_transducer_set_x_undef y x var_list data_list conf_id1 =
	let prerules_A=set_x_undef_A y x var_list in
	let prerules_B=set_x_undef_B y x var_list in
	let prerules_undef=set_x_undef_set_it x var_list in
	let prerules_generic=set_x_undef_generic var_list in
	(* ADD data values *)
	let rulebase_xy=x_ass_y_transform_rules_and_add_data prerules_A data_list in
	let rulebase_not_xy=x_ass_y_transform_rules_and_add_data prerules_B data_list in
	let rulebase_generic=x_ass_y_transform_rules_and_add_data prerules_generic (data_list@["NULL"]) in
	let rulebase_set_undef=x_ass_y_transform_rules_and_add_data prerules_undef ["UNDEF"] in
	let rulebase_undef_null=x_ass_y_transform_rules_and_add_data prerules_generic ["UNDEF";"NULL"] in
	(* CREATE RULES *)
	let rules=(x_ass_y_create_rules rulebase_xy "q1" "q1" "qset") @
		(x_ass_y_create_rules rulebase_not_xy "q1" "q1" "q1") @
		(x_ass_y_create_rules rulebase_generic "qset" "q1" "qset") @
		(x_ass_y_create_rules rulebase_generic "q1" "qset" "qset") @
		(x_ass_y_create_rules rulebase_undef_null "q1" "q1" "qnull") @
		(x_ass_y_create_rules rulebase_undef_null "qnull" "q1" "qok") @
		(x_ass_y_create_rules rulebase_set_undef "qset" "q1" "qok") @
		[(conf_id1,["qok";"q1"],conf_id1,"qfin") ] in
	let init_rules=[("bot0",[],"bot0","q1");("bot2",["q1";"q1"],"bot2","q1")] in
	(["q1";"qnull";"qok";"qset";"qfin"],["qfin"],init_rules@rules);;

(***********************************************************************************)
(* x->data:=value                                                                  *)
(***********************************************************************************)

let x_data_ass_val_notx x set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [] [x] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

(* do assigment *)
let x_data_ass_val_x x value set_of_symbols =
	let assign_rhs lhs=(lhs,lhs@[value]) in
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [x] [] set_of_comb in
	List.map (assign_rhs) lhs;;

(* If x is null/undefined => error *)
let x_data_ass_val_x_nullundef x set_of_symbols =
	let set_of_comb=create_alpha_combination_as_list set_of_symbols in
	let lhs=x_ass_y_get_elements_contains_discontains [x] [] set_of_comb in
	List.map (x_ass_y_get_rhs [] [] set_of_symbols) lhs;;

let create_transducer_x_data_ass_val x value var_list data_list conf_id1 conf_id2 conf_ERR=
	let prerules_cont=x_data_ass_val_x x value var_list in
	let prerules_notcont=x_data_ass_val_notx x var_list in
	let prerules_cont_nullundef=x_data_ass_val_x_nullundef x var_list in
	(* ADD data values *)
	let rulebase_x=x_ass_y_transform_rules_and_add_data_on_LHS prerules_cont data_list in
	let rulebase_notx=x_ass_y_transform_rules_and_add_data prerules_notcont data_list in
	let rulebase_notx_undefnull=x_ass_y_transform_rules_and_add_data prerules_notcont ["NULL";"UNDEF"] in
	let rulebase_x_undefnull=x_ass_y_transform_rules_and_add_data prerules_cont_nullundef ["NULL";"UNDEF"] in
	(* CREATE RULES *)
	let rules=
		(x_ass_y_create_rules rulebase_x "q1" "q1" "q1") @
		(x_ass_y_create_rules rulebase_notx "q1" "q1" "q1") @
		(x_ass_y_create_rules rulebase_notx_undefnull "q1" "q1" "qnull") @
		(x_ass_y_create_rules rulebase_notx_undefnull "qnull" "q1" "qok") @
		(x_ass_y_create_rules rulebase_x_undefnull "q1" "q1" "qnullerror") @
		(x_ass_y_create_rules rulebase_x_undefnull "qnull" "q1" "qundeferror") @
		(x_ass_y_create_rules rulebase_notx_undefnull "qnullerror" "q1" "qundeferror") @
		[(conf_id1,["qok";"q1"],conf_id2,"qfin");(conf_id1,["qundeferror";"q1"],conf_ERR,"qfin") ] in	
	let init_rules=[("bot0",[],"bot0","q1");("bot2",["q1";"q1"],"bot2","q1")] in
	(["q1";"qnull";"qnullerror";"qok";"qundeferror";"qfin"],["qfin"],init_rules@rules);;


