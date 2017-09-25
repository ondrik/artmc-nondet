open Taml
open Transducer_st_pres
open Simple_main_loop
open Colapsing_v3

type whatrun = N | D | ND | DN

let tester run_what fdet fndet abstr bw sigma_str init_str tr_str bad_str init_preds_str_list = 

   let ndet () = 
   (***********************************)
   (**)  switch_to_nondeterminism ();
   (**)	print_endline "\n***************************";
   (**)	print_endline "* Non-deterministic ARTMC *";
   (**)	print_endline "***************************";
   (**) 	let n_start_time=Sys.time () in
   (**)	let n_res_opt = (
   (**)		try fndet sigma_str init_str tr_str bad_str init_preds_str_list;None
   (**)		with Result_OK res -> Some res
   (**)	) in
   (**)	let n_stop_time=Sys.time () in
   (***********************************)
      n_res_opt,(n_stop_time -. n_start_time)
   in

   let det () = 
   (***********************************)
   (**)  switch_to_determinism ();
   (**)	print_endline "\n\n***********************";
   (**)	print_endline "* Deterministic ARTMC *";
   (**)	print_endline "***********************";
   (**) 	let d_start_time=Sys.time () in
   (**)	let d_fix_opt = (
   (**)		try fdet sigma_str init_str tr_str bad_str init_preds_str_list;None
   (**)		with Result_OK fix -> Some fix
   (**)	) in
   (**)	let d_stop_time=Sys.time () in
   (***********************************)
      d_fix_opt,(d_stop_time -. d_start_time)
   in


	let check_nondet n_res_opt =
		match n_res_opt with Some (n_fix,n_preds) -> 
		print_endline "*****************************************************";
		print_endline "* Checking correctness of nondeterministic version: *";
		print_endline "*****************************************************";

		let sigma = (alphabet sigma_str) in
		let init = (automaton sigma init_str) in
		let tr = if not bw then (compile_transducer tr_str) else (inverse_transducer tr_str) in
		let bad = (automaton sigma bad_str) in

		let next = 
			let abstr_act = abstr n_fix n_preds in
			Automaton.union (apply_tr_aut tr abstr_act) abstr_act
		in

		let is_fixpoint = Heuristics.is_included next n_fix in
		let init_included = Heuristics.is_included init n_fix in
		let bad_included = Heuristics.is_included bad n_fix in
		let ok = if not bw 
				then (is_fixpoint && init_included && not bad_included) 
				else (is_fixpoint && not init_included && bad_included) 
		in
		print_endline "done";

		print_endline "*********************************";
		print_endline "* Correctness checking results: *";
		print_endline "*********************************";
		Printf.printf "  fixpoint: %b\n  init in: %b\n  bad in: %b\n%s\n" 
			is_fixpoint init_included bad_included (if ok then "OK" else "ERROR!!!");

		| _ -> print_endline "checking of unsuccessfull verification not implemented"
	in


	let compare (n_res_opt,n_time) (d_fix_opt,d_time) =

		print_endline "\n****************************************";
		print_endline "* Comparing det. and non-det. results: *";
		print_endline "****************************************";

		match (n_res_opt,d_fix_opt) with  (None,None) -> print_endline "Both failed"

		| Some (n_fix,n_preds),Some (d_fix,_) ->
			let d_sub_n = Heuristics.is_included d_fix n_fix in
			let n_sub_d = Heuristics.is_included n_fix d_fix in

			Printf.printf "  %s %s %s\n" "L(N-fix)" (if d_sub_n && n_sub_d then "=" 
							    else if d_sub_n then ">" 
							    else if n_sub_d then "<"
							    else "x") "L(D-fix)";
			Printf.printf "  Non-det. CPU time: %f\n" (n_time); flush stdout;
			Printf.printf "  Det. CPU time    : %f\n\n" (d_time); flush stdout;
			flush_all();

		| _,_ -> print_endline "ERROR, different results!!"
	in


	
	match run_what with 
	D -> (match det () with (_,d_time) -> Printf.printf "\n  Det. CPU time: %f\n" (d_time); flush stdout)
	| N -> (match ndet () with (n_res_opt,n_time) -> check_nondet n_res_opt;Printf.printf "  Non-det. CPU time: %f\n" (n_time); flush stdout)
	| ND -> (let n = ndet() in let d= det() in check_nondet (fst n);compare n d)
	| DN -> (let d = det() in let n= ndet() in check_nondet (fst n);compare n d)

	
let atrmc_strpres_fwcomp_bwcoll_allstpred ?(what_run=DN) sigma_str init_str tr_str bad_str init_preds_str_list =
	(tester what_run 
		atrmc_strpres_fwcomp_bwcoll_allstpred 
		atrmc_strpres_fwcomp_bwcoll_allstpred
		bw_coll_allstpred
		false 
		sigma_str init_str tr_str bad_str init_preds_str_list) 


let atrmc_strpres_fwcomp_bwcoll ?(what_run=DN) sigma_str init_str tr_str bad_str init_preds_str_list =
	(tester what_run
		atrmc_strpres_fwcomp_bwcoll
		atrmc_strpres_fwcomp_bwcoll
		bw_coll
		false 
		sigma_str init_str tr_str bad_str init_preds_str_list) 


let atrmc_strpres_bwcomp_bwcoll_allstpred ?(what_run=DN) sigma_str init_str tr_str bad_str init_preds_str_list  =
	(tester what_run 
		atrmc_strpres_bwcomp_bwcoll_allstpred 
		atrmc_strpres_bwcomp_bwcoll_allstpred
		bw_coll_allstpred
		true
		sigma_str init_str tr_str bad_str init_preds_str_list) 


let atrmc_strpres_bwcomp_bwcoll ?(what_run=DN) sigma_str init_str tr_str bad_str init_preds_str_list =
	(tester what_run 
		atrmc_strpres_bwcomp_bwcoll
		atrmc_strpres_bwcomp_bwcoll
		bw_coll
		true
		sigma_str init_str tr_str bad_str init_preds_str_list) 



