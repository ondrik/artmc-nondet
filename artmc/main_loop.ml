open Main_loop_utility;;



(*saving of automata which were tested on inclusion. Works for rb-insert only.*)
let open_append file_name = 
    open_out_gen [Open_wronly;Open_append;Open_creat;Open_text] 0o666 file_name
let open_delete name = open_out_gen [Open_wronly;Open_creat;Open_text] 0o666 name

;;
(*automaton will be saved into file file_name.spec and named as aut_name*)
let save_aut aut name =
    let f = open_append (name^".spec") in
    let aut_str = Taml.Automaton.to_string aut in
    Printf.fprintf f "Automaton A\n%s\n" aut_str;
    close_out f
;;

let write_alphabet_to_files alpha file_name_list= 
	List.iter
	(function fnm ->
		let f = open_delete (fnm^".spec") in
		Printf.fprintf f "Ops %s\n\n"
		(Taml.Alphabet.to_string alpha);close_out f
	)
	file_name_list
;;

(*
let f = Input.create_alphabeth  ["root";"x";"xp";"xpp";"y"] ["red";"black"];;
write_alphabet_to_files f ["from_run_a";"from_run_b"];;
*)



(************************************************************************
 *			             Basic settings of the main loop 
 ************************************************************************)

module Deterministic =
(*	intersection and union of two deterministic auts is deterministic aut!! TODO*)
struct
	let minimize_nondet =  
		(function a -> a) 	
	let minimize = minimize_det
	let determinise = size_blah "determinise\t\t" 
		(function aut -> simplify (determinise aut))
	let is_included = are_equal_det
(*		is_included_det*)
	let test_fixopint_with_new_only = false
end

module NonDeterministic =
struct
	let minimize aut = 
		let a = size_blah "minComp\t\t" Simin.composed aut in
(*		let a = size_blah "minComp\t\t" Simin.downward aut in*)
(*		let b = size_blah "minCompOld\t\t" Simin_old.composed aut in*)
(*		if a <> b then failwith "minimization" else a*)
		a
	let minimize_nondet =  
		minimize
	let determinise =  
		(function a -> a) 	
	let is_included a b =
        (*save_aut a "from_run_a";*)
        (*save_aut b "from_run_b";*)
      size_blah2b "is_included_ach\t" Heuristics.is_included a b
	let test_fixopint_with_new_only = true
end

(*open Deterministic*)
open NonDeterministic

(************************************************************************
 *			     The top-most function of the verification loop
 ************************************************************************)

type restriction_of_abstraction =
	Unrestricted | Positive of int list | Negative of int list 

let run_main_loop_predabs ?(abstr_restriction=Unrestricted) name program init_line init_conf init_predicates bad_set = 
	(*global main_loop variables	*)
	let empty_aut = Taml.automaton (Taml.Automaton.get_alphabet init_conf) "States Final States Transitions" in 
	let l = Array.length program in
	let changed = Array.make l false in 
	let configs = Array.make l empty_aut in 
	let predicates = Array.make l init_predicates in
	let step = ref 0 in
	let badOnLine = Array.make l empty_aut in
	let new_predicates = Array.make l [] in 
	let path_to_bad = ref [] in

	let loop_point = Array.map (function ln -> 
		match ln with Input.Nondet _ | Input.Two_trans _ -> true | _ -> false) 
		program
	in
	(*
	let loop_point = Array.make l false in
	loop_point.(0)<-true;
	loop_point.(21)<-true;
	loop_point.(28)<-true;
	*)

	(*Procedure for testing bad states - is some tree with "bad" root acceptable? *)
	(* is there (!in SIMPLIFIED automaton!) rule bad(_,...,_) -> f, where f is final state?*)
	(*returns rimplified aut, so ti is sufficient to test is_empty*)
	let inter_with_bad_basic aut = 
		let finals = Taml.State_set.to_list (Taml.Automaton.get_final_states aut) in
		let final_strs = List.map Taml.Term.to_string finals in
		let rules  = Taml.Rewrite.to_list (Taml.Automaton.get_transitions aut) in
		let bad_rule rule = 
			let symbol = Taml.Symbol.to_string(Taml.Term.top_symbol (Taml.Rewrite.lhs rule)) in
			symbol = "bad"
		in
		let target_bad_final l rule = 
			let target = Taml.Term.to_string (List.hd (Taml.Term.list_leaves (Taml.Rewrite.rhs rule))) in
			if (bad_rule rule) && (List.mem target final_strs) then target::l else l
		in
		let bad_finals_strs = List.fold_left target_bad_final [] rules in
		match bad_finals_strs with 
		[] -> None
		| _ ->
		let bad_finals = List.filter (fun s -> (List.mem (Taml.Term.to_string s) bad_finals_strs)) finals in
		let bad_or_nonfinal rule = 
			let target = Taml.Term.to_string (List.hd (Taml.Term.list_leaves (Taml.Rewrite.rhs rule))) in
			let symbol = Taml.Symbol.to_string(Taml.Term.top_symbol (Taml.Rewrite.lhs rule)) in
			not (List.mem target final_strs) || (symbol="bad")
		in
		let new_transitions = Taml.Rewrite.list_to_trs (List.filter bad_or_nonfinal (Taml.Rewrite.to_list (Taml.Automaton.get_transitions aut))) in
		let bad =
			minimize(determinise(simplify(Taml.Automaton.make_automaton
				(Taml.Automaton.get_alphabet aut)
				(Taml.Automaton.get_state_ops aut)
				(Taml.Automaton.get_states aut)
				(Taml.State_set.list_to_set bad_finals)
				(Taml.Automaton.get_prior aut)
				(new_transitions)
				)))
		in
		if is_language_empty bad then None else Some bad
	in

	(*first, it test the basic consistency - the previous procedure. Then it tests shape invariant (if bad_set is not Null)
	 *The bad_set can be given as set of all bad configs. - then it computes intersection  ....etc, in a common way. 
	 *Or bad_set can be givan also as set of all good configs. 
	 *Then, it first test inclusion in good configs (this can be faster then computing intersction with bad).*)
	let intersection_with_bad ?(bad_set = None) aut  =
		print_endline "Checking for intersection with bad:";flush stdout;
		print_endline"basic check ... ";
		let basic_bad = inter_with_bad_basic aut in
		match basic_bad with
		Some inter_with_bad ->
			Some inter_with_bad
		| None -> (
			print_endline "ok";
			match bad_set with 
			None -> 
				basic_bad
			| Some (bad,good) -> (
				print_endline"\tshape check ... ";
				match good with
				None -> (
					let inter_with_bad = (inter aut bad) in
					if is_language_empty inter_with_bad then
						None
					else
						Some inter_with_bad
				)
				| Some gd -> (
					if is_included aut gd then (
						print_endline "ok";
						None
					)
					else (
						let inter_with_bad = minimize(determinise (inter aut bad)) in
						Some inter_with_bad
					)
				)
			)
		)
	in

 	(*Performs abstract and union and checks Bad. Then it changes configuraion and updates chenged.
	 * Returns None if the intersection with Bad is empty, else returns Some intersection_with_bad*)
	let change_conf new_conf line =

		if test_fixopint_with_new_only then (

			if (is_included new_conf configs.(line)) then (
				if changed.(line) then failwith"chage_conf";
				print_string "Included -> skip \n"; flush stdout;
			)
			else (
				let uni = union new_conf configs.(line) in 
				let abs_uni = 
					let do_abstraction = match abstr_restriction with
						Unrestricted -> true
						| Positive lines -> List.mem line lines
						| Negative lines -> not (List.mem line lines)
					in
					if do_abstraction then minimize (determinise (predicate_abstraction predicates.(line) (minimize_nondet uni)))
(*					if do_abstraction then minimize (determinise (predicate_abstraction predicates.(line) (uni)))*)
					else minimize (determinise uni)
				in
				configs.(line) <- abs_uni;
				changed.(line) <- true
			)

		) else (

	(*version where we assume that fixpoint is tested using det. equivalence*)
			let uni = union new_conf configs.(line) in 
			let abs_uni = 
				let do_abstraction = match abstr_restriction with
					Unrestricted -> true
					| Positive lines -> List.mem line lines
					| Negative lines -> not (List.mem line lines)
				in
				if do_abstraction then minimize (determinise (predicate_abstraction predicates.(line) (minimize_nondet uni)))
(*				if do_abstraction then minimize (determinise (predicate_abstraction predicates.(line) (uni)))*)
				else minimize (determinise uni)
			in
			if is_included abs_uni configs.(line) then (
				if changed.(line) then failwith"chage_conf";
				print_string "Included -> skip \n"; flush stdout;
			)
			else (
				configs.(line) <- abs_uni;
				changed.(line) <- true
			)

		)
	in



	(*main loop - dft traversal through a control flow graph*)
	let rec main_loop program round trace this_line =
		print_trace (this_line::trace);
		match intersection_with_bad configs.(this_line) with
		Some bad -> 
			Mess.print_problem "BAD CONFIGURATION REACHED";print_trace (this_line::trace);
			Array.fill badOnLine 0 l empty_aut;
			Array.fill new_predicates 0 l []; 
			Some bad
		| None -> (

			(*we have two types of steps - simple and branching:*)
			let simple_step (operation,rev_operation,next_line) = 
				path_to_bad:=(operation,next_line)::!path_to_bad;
				let step_forward = (minimize_nondet(operation configs.(this_line))) in
(*				let step_forward = ((operation configs.(this_line))) in*)
				let old_next_line_conf = configs.(next_line) in

				let backstep bad =
					print_endline "Counterexample testing ...";
					Printf.printf "this-%d,next-%d\n" this_line next_line;
					let all_bad = minimize_nondet(union badOnLine.(next_line) bad) in
					let before_abs = minimize_nondet(union step_forward old_next_line_conf) in
					let all_bad_before_abs = minimize_nondet(inter before_abs all_bad) in
					badOnLine.(next_line) <- minimize(determinise (union badOnLine.(next_line) all_bad_before_abs));
					let all_bad_in_new = minimize(determinise(inter step_forward all_bad))  in
					let refinement = (determinise all_bad) in
					if is_language_empty all_bad_before_abs then if not (is_language_empty refinement) then 
					(
						(*let add_aut a l = if not (List.exists (function b -> are_identical a b) l) then a::l else l in*)
						let add_aut a l = 
                                                        if not (List.exists (function b -> are_identical a b) l) 
                                                        then (Interim.print
                                                        (Interim.of_taml a); a::l) 
                                                        else l in
						new_predicates.(next_line) <- add_aut (refinement) new_predicates.(next_line);
					);
					Some ((minimize_nondet(rev_operation all_bad_in_new)))
				in

				incr step;
				change_conf step_forward next_line;
				let bad_opt = 	main_loop program round (this_line::trace)  next_line in
				match bad_opt with 
				None -> None
				| Some bad -> backstep bad
			in

			let branching (operation1,rev_operation1,next_line1) (operation2,rev_operation2,next_line2) =
				let current_path_to_bad = !path_to_bad in
				match simple_step (operation1,rev_operation1,next_line1) with
				(*fixpoint reached, we have to connect the next branch with this line*)
				Some bad -> Some bad 
				| None ->
					path_to_bad := current_path_to_bad; 
					Printf.printf "********* Second branch %s\n" (comp_point_str this_line !step round); 
					simple_step (operation2,rev_operation2,next_line2)
			in

			Printf.printf "********* Processing%s *************\n" (comp_point_str this_line !step round); 
			if not changed.(this_line) then (
				print_string "... nothing to do\n"; flush stdout; None
			)
			else (
				changed.(this_line) <- false;
				match program.(this_line) with
				Input.Exit_comp -> 
					intersection_with_bad ~bad_set:bad_set configs.(this_line) 
				|
				Input.Nondet (t,f) -> 
					branching (identity,identity,t) (identity,identity,f)
				|
				Input.Leftrotate_comp (x,t) -> 
					simple_step (rotate_left x,rev_rotate_left x,t)
				|
				Input.Rightrotate_comp (x,t) -> 
					simple_step (rotate_right x,rev_rotate_right x,t)
				|
				Input.One_trans (transd, rev_transd, t) -> 
					simple_step (apply_tr_aut transd,apply_tr_aut rev_transd,t)
				|
				Input.Two_trans (trans1, rev_trans1,t, trans2, rev_trans2, f) ->  
					branching (apply_tr_aut trans1,apply_tr_aut rev_trans1,t) (apply_tr_aut trans2,apply_tr_aut rev_trans2, f)
				|
				Input.Trans_set (forward, backward, t) -> 
					let apply transds aut = List.fold_left (fun a tr -> apply_tr_aut tr a) aut transds in
					simple_step (apply forward,apply (List.rev backward),t)
			)
		)
   in

	(*if you intend to use this function, 
	 * do not add predicates labeled by "P[number]" manually 
	 * returns true iff p is really added (it was not there before)
	 * *)
	(*adds all predicates from list, returns true iff at least one of them was added*)
	let add_predicates predicates p_list =
		let add_predicate predicates p = 
			let add = List.fold_left (fun vl (_,pred) -> vl && not (are_identical p pred)) true predicates in
			if not add then 
				(add,predicates) 
			else
				let n = List.length predicates in
				let new_pred = ("P"^(string_of_int n),p) in
				(add,new_pred::predicates)
		in

		List.fold_left (fun (tmp,preds) p -> let added,newpreds = add_predicate preds p in (tmp||added),newpreds) 
		(false,predicates) p_list
	in

	(*the CEGAR loop*) 
	let rec do_run_main_loop_predabs round = 
		print_endline "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
		print_endline ("++++++++++++++++++++++++++--"^name^":"^(string_of_int round)^"--+++++++++++++++++++++++++++");
		print_endline "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
      
		Array.fill changed 0 l false; changed.(init_line) <- true;
		Array.fill configs 0 l empty_aut; configs.(init_line) <- init_conf;
		step := 0;
		path_to_bad:=[];

		match main_loop program round [] init_line with
		None -> print_string"VERIFIED"
		| Some bad_from_first -> (
			let inter_with_init = inter (union bad_from_first badOnLine.(init_line)) init_conf in
			if is_language_empty inter_with_init then (
				let refined = ref false in
				for i = 0 to l-1 do
					print_int i;print_newline();
					let was_added,new_predicates_i = add_predicates predicates.(i) new_predicates.(i) in
					refined := !refined || was_added;
					predicates.(i) <- new_predicates_i;
				done;
				if not !refined then failwith"abstaction cycling";
				do_run_main_loop_predabs (round+1)

			)
			else (
				let rec bite_off pred list = 
					match list with
					[] -> []
					| h::t -> if pred h then t else bite_off pred t
				in

				Mess.print_problem "BUGGYBUG";

				(*checking, if (and how exactly) is the counterexample reachable*)
				let found_traces = ref [] in

				let rec find_error_trace path (trace,states) this_line newconf = 
					if is_language_empty newconf then ()
					else
						match path with
						[] -> (
							let bad_set_here = match program.(this_line) with Input.Exit_comp -> bad_set | _ -> None in
							match intersection_with_bad ~bad_set:bad_set_here newconf with
                     None -> ()
                     | Some bad -> 
                        if not (List.mem (this_line::trace,newconf::states) !found_traces) then (
                           found_traces :=
                              (this_line::trace,newconf::states)::!found_traces;
                        )
                     )
						| (oper,next_line)::path_tl -> (
							if loop_point.(this_line) then (
								find_error_trace (bite_off (function (_,nl) -> nl=this_line) path_tl) (trace,states) this_line newconf
							);
							find_error_trace path_tl (this_line::trace,newconf::states) next_line (oper newconf)
						)
				in

				find_error_trace (List.rev !path_to_bad) ([],[]) init_line init_conf;
				let traces_by_lenght = List.sort (fun (t1,_) (t2,_)  -> 
					compare (List.length t1) (List.length t2)) !found_traces 
				in
				List.iter (function (t,s) -> print_endline "\n\nTrace:"; print_trace t; print_endline "\nTrace in detail:";
					List.iter2 (fun line aut -> 
						Printf.printf "\nLine %d:\n" line; 
						Taml.Automaton.print
						(simplify(Minimize_abstr_fin_length.minimize(determinise aut)))
					) t s
				) 
				traces_by_lenght;

				print_endline "\nError traces:";
				List.iter (function (t,_) -> print_trace t) traces_by_lenght
			)
		)
	in

	(*the computation starts here*)
	do_run_main_loop_predabs 0;
	Printf.printf "\nTIME:%f\n" (Mess.time()); 
;;
