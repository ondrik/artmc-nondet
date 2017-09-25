open Mess;;

(**********************************************************************)
       (*functions with added info printing or consitency checks*)
(**********************************************************************)

(*	let print_aut_sizes = false*)
	let print_aut_sizes = true 

	let consistency_testing = false
(*	let consistency_testing = true*)


let size_blah s f a = if print_aut_sizes then size_blah s f a else f a
let size_blahb s f a = if print_aut_sizes then size_blahb s f a else f a
let size_blah2 s f a1 a2 = if print_aut_sizes then size_blah2 s f a1 a2 else f a1 a2
let size_blah2b s f a1 a2 = if print_aut_sizes then size_blah2b s f a1 a2 else f a1 a2

let apply_tr_aut tr  = size_blah "transduce\t\t" 
	(function aut ->
		let res = Transducer_st_pres.apply_tr_aut tr aut in
		if consistency_testing then ( 
			let inv_tr = (Transducer_st_pres.inverse_transducer2 tr) in
			let back =  Transducer_st_pres.apply_tr_aut inv_tr res in
			let res_back =  Transducer_st_pres.apply_tr_aut tr back in
			if not (Heuristics.are_equiv res res_back) then failwith "apply_tr_aut"
		); 
		res 
	) 

let simplify  = 	
	(function aut ->
		let res = Interim.simplify_taml aut in
		if consistency_testing then ( 
			if not (Heuristics.are_equiv (Taml.simplify aut) res) then failwith"simplify"
		);
		res 
	) 

let union  = size_blah2 "union\t\t\t" 
	(fun aut1 aut2 -> 
		let res = Interim.to_taml (Interim.union (Interim.of_taml aut1) (Interim.of_taml aut2))in
		if consistency_testing then ( 
			let res2 = Taml.union aut1 aut2 in
			if not (Heuristics.are_equiv res res2) then failwith"union"
		);
		res
	) 

let inter  = size_blah2 "intersection\t\t" 
	(fun aut1 aut2 ->
		let res = simplify (Taml.inter aut1 aut2) in
		if consistency_testing then 
		();(* BACHA! - the consistency test is missing*)
		res
	) 

let is_language_empty a = size_blahb "is_empty\t\t" 
	(function b -> Taml.Automaton.is_empty (simplify  b)) a 

let rotate_left x aut = 
   let res = simplify (size_blah "rotate_left\t\t" (Rotation.do_left_rotate x) aut) in
	if consistency_testing then ( 
		let back = simplify(Rotation.do_reverse_left_rotate x res) in
		let res_back = simplify(Rotation.do_left_rotate x back) in
		if not (Heuristics.are_equiv res res_back) then failwith"rotate_left"
	);
   res

let rotate_right x aut = 
   let res = simplify (size_blah "rotate_right\t\t" (Rotation.do_right_rotate x) aut) in
	if consistency_testing then ( 
		let back = simplify(Rotation.do_reverse_right_rotate x res) in
		let res_back = simplify(Rotation.do_right_rotate x back) in
		if not (Heuristics.are_equiv res res_back) then failwith"rotate_right"
	);
   res

let rev_rotate_left x aut = 
   let res =size_blah "rev_rotate_left\t" (Rotation.do_reverse_left_rotate x) aut in
	if consistency_testing then ( 
		let back = Rotation.do_left_rotate x res in
		let res_back = Rotation.do_reverse_left_rotate x back in
		if not (Heuristics.are_equiv res res_back) then failwith"rev_rotate_left"
	); 
	res

let rev_rotate_right x aut = 
   let res =size_blah "rev_rotate_right\t" (Rotation.do_reverse_right_rotate x) aut in
	if consistency_testing then ( 
		let back = Rotation.do_right_rotate x res in
		let res_back = Rotation.do_reverse_right_rotate x back in
		if not (Heuristics.are_equiv res res_back) then failwith"rev_rotate_right"
	);
	res

let are_identical a b = 
	size_blah2b "are_identical\t\t" (fun a b -> a=b) a b  

let identity aut = 
	size_blah "identity\t\t" (function a -> a) aut

let predicate_abstraction preds aut = 
	let abs a =  Colapsing_v3.bw_coll_allstpred a preds in
	let res = size_blah "abstract\t\t" abs aut in
	if consistency_testing then ( 
		if not (Heuristics.is_included aut res) then failwith"abstract"
	);
	res

let determinise a = 
(*	size_blah "determinise\t" Taml.determinise a;;*)
	Taml.determinise a;;

let inverse_deterministic a = 
	Interim.to_taml (Interim.inverse_deterministic (Interim.of_taml a))

let is_included_det = size_blah2b "is_included_det\t" 
	(fun aut1 aut2 ->
		let inv = Interim.simplify_taml (Interim.to_taml (Interim.inverse_deterministic (Interim.of_cripple_taml aut2))) in
(*		let inv = Interim.simplify_taml (Interim.to_taml (Interim.inverse_deterministic (Interim.of_taml aut2))) in*)
		let inter = simplify  (Taml.Automaton.inter aut1 inv) in
		let res = Taml.Automaton.is_empty inter in
		if consistency_testing then ( 
			if not (Interim.is_deterministic_taml aut2) then failwith"is_included_det2";
			if res <> Heuristics.is_included aut1 aut2 then (
				Mess.print_bool (Taml.is_included aut1 aut2);
	 			print_bool res;
	  			Taml.Automaton.print aut1;
	  			Taml.Automaton.print aut2;
	  			Taml.Automaton.print inv;
				failwith"is_included_det"
			)
		);
		res
	)

let minimize_det = size_blah "minDet\t\t\t" 
	(function a ->
		let res =  simplify (Minimize_abstr_fin_length.minimize (simplify a)) in
		if consistency_testing then ( 
			if not (Interim.is_deterministic_taml a) then ( 
				let ia = Interim.of_taml a in
				print_string (Interim.rule_list_to_string ia.Interim.a_states ia.Interim.a_alphabet (List.sort compare ia.Interim.a_rules));
				Taml.Automaton.print a;
				failwith"minimize_det1"
			);
			if not (Heuristics.are_equiv a res) then failwith"minimize_det2"
		);
		res
	)
	  
let are_equal_det = size_blah2b "are_equal_det\t\t" 
	(fun a b ->
		let res =  Automata_equal.automata_equal a b in
		if consistency_testing then ( 
			if not (Interim.is_deterministic_taml a) || not (Interim.is_deterministic_taml b) then ( 
				failwith"are_equal_det1"
			);
			if not ((Heuristics.are_equiv a b) = res) then failwith"are_equal_det2"
		);
		res
	)
	

(************************************************************************
 *               Some printing functions
 ************************************************************************)
let print_tr tr =
	match tr with (alph,sts1,sts2,rules) ->
	print_endline (Taml.Alphabet.to_string alph);
	print_endline (Taml.State_set.to_string sts1); 
	print_endline (Taml.State_set.to_string sts2);
	let print_rule r = match r with (s1,args,s2,tar) ->
		let s1_s = Taml.Symbol.to_string s1 in
		let s2_s = Taml.Symbol.to_string s2 in
		let args_sl = List.map Taml.Term.to_string args in 
		let tar_s = Taml.Term.to_string tar in
		Printf.printf "%s/%s(%s)->%s\n" s1_s s2_s (String.concat "," args_sl) tar_s
	in
	List.iter print_rule rules
;;

let comp_point_str line step round=    
	Printf.sprintf "_l%d_s%d_r%d" line step round
;;
let name_ver name line step round = name^(comp_point_str line step round)
;;

let print_trace trace =  
	print_endline (String.concat "," (List.map string_of_int (trace)))
;;
