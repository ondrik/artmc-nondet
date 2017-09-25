open Taml;;
open Transducer_st_pres;;
open Create_transducers;;

type program_description =
	X_ass_y of string*string*int |
	X_ass_yleft of string*string*int |
	X_ass_yright of string*string*int |
	X_ass_yup of string*string*int |
	X_ass_null of string*int |
	If_xeqy of string*string*int*int |
	If_xnull of string*int*int |
	New_xleft of string*string*int |
	New_xright of string*string*int |
	If_xdata of string*string*int*int |
	Dispose of string*int |
	Setdata of string*string*int |
	Leftrotate of string*int |
	Rightrotate of string*int |
	If_nondet of int*int |
	Exit ;;



type 'a compiled_program =
	One_trans of 'a*'a*int |
	Two_trans of 'a*'a*int*'a*'a*int |
	Trans_set of ('a list)*('a list)*int |
	Nondet of int*int |
	Leftrotate_comp of  Taml.Symbol.t list* int |
	Rightrotate_comp of  Taml.Symbol.t list* int |
	Exit_comp;;

(* input program compilation *)
let rec create_transducers_dispose x var_list data_list =
	match var_list with [] -> [] |
	first::rest ->
		if first=x then
			(create_transducers_dispose x rest data_list)
		else
			(create_transducer_set_x_undef x first var_list data_list "normal") ::
			(create_transducers_dispose x rest data_list);;
			
let create_alpha_combination_with_data_as_list var_list data_list =
   List.concat (
      List.map (function data ->
         List.map (function symbol ->
				symbol@[data]
         ) (create_alpha_combination_as_list var_list)
      ) data_list
   )

let rec compile_program input var_list data_list =
	let tr=compile_transducer in
	let itr=inverse_transducer in
	match input with [] -> [] |
	  first::rest ->
	  let next=(compile_program rest var_list data_list) in
	    match first with
		X_ass_y (x,y,next_line) ->
			let trans=(create_transducer_x_ass_y y x var_list data_list "normal" "normal" "bad" ) in
			One_trans (tr trans, itr trans, next_line)::next |
		Exit -> Exit_comp ::next |
		X_ass_yleft (x,y,next_line) ->
			let trans=(create_transducer_y_ass_xnext y x var_list data_list "normal" "normal" "bad" "left") in
			One_trans (tr trans, itr trans, next_line)::next |
		X_ass_yright (x,y,next_line) ->
			let trans=(create_transducer_y_ass_xnext y x var_list data_list "normal" "normal" "bad" "right") in
			One_trans (tr trans, itr trans, next_line)::next |
		X_ass_yup (x,y,next_line) ->
			let trans=(create_transducer_y_ass_xUP y x var_list data_list "normal" "normal" "bad") in
			One_trans (tr trans, itr trans, next_line)::next |
		X_ass_null (x,next_line) ->
			let trans=(create_transducer_x_ass_null x var_list data_list "normal" "normal") in
			One_trans (tr trans, itr trans, next_line)::next |
		If_xeqy (x,y,nextthen,nextelse) ->
			let (transthen,transelse)=
			   create_transducer_x_eq_y x y var_list data_list "normal" "normal" "normal" "bad" in
			Two_trans (tr transthen, itr transthen, nextthen,tr transelse, itr transelse, nextelse)::next |
		If_xnull (x,nextthen, nextelse) ->
			let (transthen,transelse)=
			   create_transducer_x_eq_null x var_list data_list "normal" "normal" "normal" "bad" in
			Two_trans (tr transthen, itr transthen, nextthen,tr transelse, itr transelse, nextelse)::next |
		New_xleft (x,value,next_line) ->
			let trans=
			  create_transducer_x_left_new x value var_list data_list 
				"normal" "normal" "sorry" "bad" "left" in
			One_trans (tr trans, itr trans, next_line)::next |
		New_xright (x,value,next_line) ->
			let trans=
			  create_transducer_x_left_new x value var_list data_list 
				"normal" "normal" "sorry" "bad" "right" in
			One_trans (tr trans, itr trans, next_line)::next |
		If_xdata (x,data,nextthen,nextelse) ->
			let (transthen,transelse)=
			  create_transducer_if_data x data var_list data_list 
				"normal" "normal" "normal" "bad" in
			Two_trans (tr transthen, itr transthen, nextthen,tr transelse, itr transelse, nextelse)::next |
		Setdata (x,data,next_line) -> 
			let trans=
			   create_transducer_x_data_ass_val x data var_list data_list 
				"normal" "normal" "bad" in
			One_trans (tr trans, itr trans, next_line)::next |
		If_nondet (linethen,lineelse) ->
			Nondet (linethen,lineelse)::next |
		Dispose (x,next_line) ->
		let transducers=(create_transducers_dispose x var_list data_list)@
			[(create_transducer_dispose x var_list data_list "normal" "normal" "bad")] in
			Trans_set (List.map tr transducers, List.map itr transducers, next_line) :: next |			
		Leftrotate (x, next_line) ->
			(* Create all combinations, where x occurs *)
			let set_of_comb=create_alpha_combination_with_data_as_list var_list data_list in
			let conf_with_x1=x_ass_y_get_elements_contains_discontains [x] [] set_of_comb in
			let conf_with_x=List.map (String.concat "") conf_with_x1 in 
			let conf_with_x_symbols=List.map (Symbol.of_string) conf_with_x in
			Leftrotate_comp	(conf_with_x_symbols, next_line) ::next |
		Rightrotate (x, next_line) ->
			(* Create all combinations, where x occurs *)
			let set_of_comb=create_alpha_combination_with_data_as_list var_list data_list in
			let conf_with_x1=x_ass_y_get_elements_contains_discontains [x] [] set_of_comb in
			let conf_with_x=List.map (String.concat "") conf_with_x1 in
			let conf_with_x_symbols=List.map (Symbol.of_string) conf_with_x in
			Rightrotate_comp (conf_with_x_symbols, next_line) ::next ;;
	

(* ------------------------------------------------------------------------------------------- *)
(* Alphabeth creation                                                                          *)
(* ------------------------------------------------------------------------------------------- *)

let rec compose_symbol_with_set symbol1 symbol_set =
	match symbol_set with [] -> [] |
	first::rest ->
		String.concat "" [ symbol1; first ] :: compose_symbol_with_set symbol1 rest ;;

let rec compose_set_and_set set1 set2 =
	match set1 with [] -> [] |
	first::rest ->
		(compose_symbol_with_set first set2 )
		@ (compose_set_and_set rest set2);;

let concat_2strings str1 str2 =
(* concat 2 strings *)
	String.concat "" [str1; str2];;

let rec create_alpha_combination symbol_set =
(* INPUT: a set of strings
   OUTPUT: set of all possible string obtained by concatenation from original one
           - one string from original set can occur maximally once
	   - order of substrings in newly set is given by order in input set *)
	match symbol_set with [] -> [""] |
	first::rest ->
		List.map (concat_2strings first) (create_alpha_combination rest)
		@ (create_alpha_combination rest);;


let create_alphabeth_final symbol_set =
	alphabet (String.concat ":2 " (symbol_set @ ["bot0:0 bot2:2 normal:2 bad:2"]));;

let create_alphabeth var_list data_list =
	let var_combinations=create_alpha_combination var_list in
	let vars_and_data=compose_set_and_set var_combinations (data_list@["NULL";"UNDEF"]) in
	create_alphabeth_final vars_and_data;;



