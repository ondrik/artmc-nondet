open Taml;;
open Mess;;
open Transducer_st_pres;;
open Minimize_abstr_fin_length;;
open Colapsing_v3;;



type minimization_t = 
	Det | Bisim | Down | Comp | Vubeczadna

type how_to_test_inclusion_t = 
	Det_equiv | Antichain_equiv| Antichain_inclusion | Taml_inclusion | Det_inclusion | Nijak

let minimization = ref Comp
let how_to_test_inclusion = ref Nijak

let switch_to_determinism _ = 
   minimization:=Det;
(*   how_to_test_inclusion:=Taml_inclusion*)
   how_to_test_inclusion:=Det_inclusion

let switch_to_nondeterminism _  = 
   minimization:=Comp;
(*   minimization:=Vubeczadna;*)
(*   minimization:=Down;*)
   how_to_test_inclusion:=Antichain_inclusion



let determinise a = size_blah "det" Taml.determinise a;;

let minimize aut = 
	match !minimization with 
	Det ->
		size_blah "min" Minimize_abstr_fin_length.minimize (determinise aut)
	| Bisim -> 
		size_blah "bis" Heuristics.bisimin aut
	| Down -> 
		size_blah "down" Simin.downward aut
	| Comp -> 
		size_blah "comp" Simin.composed aut
   | Vubeczadna -> print_string "nomin\n"; aut


(**********************************************************************)
                   (*functions with added info printing*)
(**********************************************************************)
(*functions with added info-printing*)
(*let size_blah s f a = if print_aut_sizes then size_blah s f a else f a*)
(*let size_blah2 s f a1 a2 = if print_aut_sizes then size_blah2 s f a1 a2 else f a1 a2*)
(*let size_blah2b s f a1 a2 = if print_aut_sizes then size_blah2b s f a1 a2 else f a1 a2*)


let apply_tr_aut tr a = size_blah "app" (Transducer_st_pres.apply_tr_aut tr) a
let simplify a = size_blah "sim" Interim.simplify_taml a;;
(*let union a1 a2 = size_blah2 "uni" Taml.union a1 a2;;*)
let union = size_blah2 "uni" (fun aut1 aut2 ->
	Interim.to_taml (Interim.union (Interim.of_taml aut1) (Interim.of_taml aut2)))
let inter a1 a2 = (*size blah can not be applied on non simplified automaton*)
	let intersim a1 a2 = Interim.simplify_taml(Taml.inter a1 a2) in
(*	let intersim a1 a2 = Taml.inter a1 a2 in*)
	size_blah2 "int" intersim a1 a2

;;
let inverse a= 
	let det_complete= (minimize (Taml.Automaton.make_complete a)) in
	Taml.Automaton.modify_final det_complete 
	(Taml.State_set.minus (Taml.Automaton.get_states det_complete) (Taml.Automaton.get_final_states det_complete))
let is_language_empty a = Taml.Automaton.is_empty (simplify a)
let is_included_det a1 a2= is_language_empty (inter (inverse a2) a1);;
let is_included_ndet a1 a2= size_blah2b "inc" Heuristics.is_included a1 a2;;

let antichain_equiv aut1 aut_orig =
    (*print_string "Antichain equivalence test ...\n";*)
    (*flush stdout;*)
	Heuristics.are_equiv aut1 aut_orig
;;
(*I want to count up the overall running time of antichain_incl - profilling
 * doesn't work*)
let incl_time = ref 0.0;;
let antichain_incl aut1 aut_orig =
    (*print_string "Antichain inclusion test ...\n";*)
    (*flush stdout;*)
   is_included_ndet aut1 aut_orig
;;
let determ_incl aut1 aut_orig =
    (*print_string "Determ. inclusion test ...\n";*)
    (*flush stdout;*)
	is_included_det aut1 aut_orig
;;
let determ_equiv aut1 aut_orig =
    (*print_string "Determ. equivalence test ...\n";*)
    (*flush stdout;*)
	Automata_equal.automata_equal aut1 aut_orig
;;

let inclusion_test a1 a2= 
    let start = time() in
	let res = 
		match !how_to_test_inclusion with
		Det_equiv -> determ_equiv a1 a2 
		| Antichain_equiv -> antichain_equiv a1 a2
		| Antichain_inclusion -> antichain_incl a1 a2 
		| Det_inclusion -> Main_loop_utility.is_included_det a1 a2 
		| Taml_inclusion ->  determ_incl a1 a2 
		| Nijak  ->  failwith "no inclusion method set" 
	in
	let plus_time = time() -. start in
    (*Printf.printf "incl_time:%f\n" plus_time;*)
	incl_time := !incl_time +. plus_time; 
	res
;;


let print_autom_size str aut = print_endline (str^(aut_size_str aut))


(* ==================================================================================================== *)
(* **************************************************************************************************** *)
(* ***** Abstract tree regular model checking - the main loop.                                          *)
(* **************************************************************************************************** *)
(* ==================================================================================================== *)

(* If we find a fixpoint or a real error, we throw Result_OK. *)
exception Result_OK of (Taml.Automaton.t * ((string * Taml.Automaton.t) list));;

(* We throw Not_real_error if we encounter a spurious counterexample. *)
exception Not_real_error of Taml.Automaton.t;;

(* Tests whether a counterexample is
   - a real one -> we go on backtracking,
   - a spurious one -> we throw an exception. *)

let test_to_continue actual result_back =
	print_endline ("testing the counterexample property with:"^(aut_size_str result_back));
	let inter_act_resback = inter actual result_back in
	if (Automaton.is_language_empty inter_act_resback) then
		raise (Not_real_error result_back)
	else (inter_act_resback);;

(* ==================================================================================================== *)

(* We perform recursive tests, abstraction, transduction, ...
   - when a fixpoint is reached -> we throw Result_OK
   - when bad states are intersected, we backtrack and check whether this is a real counterexample.
   - when no exception is thrown, a counterexample is returned. *)

(*TODO - opitmize is bad (intersection only once)*)
let rec do_atrmc_main_loop actual last bad trsd_step_on trsd_step_back abstr refine predicates pred_num step_no run_no =
	print_endline ("processing new configurations:"^(aut_size_str actual));
	let fixpoint aut1 aut2 = inclusion_test aut1 aut2 in
(*	let is_bad aut = not (Taml.Automaton.is_language_empty(inter aut bad)) in*)
	let badpart aut = inter aut bad in
	let nonempty aut = not (Automaton.is_empty aut) in

	Printf.printf "- checking the bad property...\n"; flush stdout;
	let bad_actual = badpart actual in
	if (nonempty bad_actual) then(
		Printf.printf "XXXXX\n"; flush stdout; 
      bad_actual
   )
	else (

      Printf.printf "checking the fixpoint property...\n"; flush stdout;
      if (fixpoint actual last) then raise (Result_OK (last,predicates));

      Printf.printf "union with the last and abstract...\n"; flush stdout;
		let uni = union actual last in

		let rec abstraction_loop tmp_predicates tmp_pred_num =
			let abstract aut = abstr aut tmp_predicates in
			let tmp_abstr_uni = size_blah "abs" abstract uni in
			let bad_tmp_abstr_uni = badpart tmp_abstr_uni in
			if nonempty bad_tmp_abstr_uni then (
(*				Printf.printf "uni:\n%s\nbad:\n%s\n%s\n" *)
(*				(Automaton.to_string uni) (Automaton.to_string bad)*)
(*				(String.concat "\n" *)
(*				(List.map (fun (n,p) -> Printf.sprintf "\nPred:%s\n%s" n (Automaton.to_string p))tmp_predicates));*)

				Printf.printf "YYYYY\n"; flush stdout; 
				abstraction_loop (refine actual (bad_tmp_abstr_uni) tmp_predicates tmp_pred_num) (tmp_pred_num+1)
			)
			else tmp_predicates,tmp_pred_num,tmp_abstr_uni
		in
		let predicates,pred_num,abstr_uni =  abstraction_loop predicates pred_num in 
		let abstr_uni = minimize abstr_uni in

      Printf.printf ">>> %d >>>\n" step_no; flush stdout;

      let next = do_atrmc_main_loop
         (trsd_step_on abstr_uni)
         abstr_uni
         bad
         trsd_step_on trsd_step_back
         abstr refine
         predicates
         pred_num (step_no+1) run_no 
      in
      Printf.printf "<<<<<\n"; flush stdout;

      try 
         test_to_continue actual (minimize(trsd_step_back next))

      with Not_real_error last_inter ->
         (* We refine the abstraction and go on in the recursion. *)
         (Printf.printf "~~~~~ Run %d: \n" (run_no+1); flush stdout;
         do_atrmc_main_loop
            actual
            last
            bad
            trsd_step_on trsd_step_back
            abstr refine
            (refine actual last_inter predicates pred_num)
            (pred_num+1) (step_no+1) (run_no+1)
         )
   )
	;;

(* ==================================================================================================== *)

let atrmc_main_loop actual last bad trsd_step_on trsd_step_back abstr refine predicates pred_num =
  try (
    Printf.printf "~~~~~ Run 1: \n"; flush stdout;
    let error_from = (do_atrmc_main_loop actual last bad trsd_step_on trsd_step_back abstr refine predicates pred_num 1 1) in
      Printf.printf "----- Property broken!\n\n"; flush stdout;
      Automaton.print error_from
  ) with Result_OK (fixpoint,predicates) ->
      (Printf.printf "----- Property holds!\n\n"; flush stdout;
(*       Automaton.print fixpoint);*)
       );
       raise (Result_OK (fixpoint,predicates))

(* ==================================================================================================== *)
(* **************************************************************************************************** *)
(* ***** ATRMC - wrappers for the main loop: structure preserving, forward computation,                 *)
(* *****         backward predicate-based labelling (with all states being predicates).                 *)
(* **************************************************************************************************** *)
(* ==================================================================================================== *)
let refinetest predicates newpred =
   let rec do_it preds =
      match preds with
      [] -> ()
      | (_,aut)::rest -> 
         if aut = newpred then failwith"abstraction looping" 
         else do_it rest
   in
(*   Automaton.print newpred;*)
   do_it predicates

let do_atrmc_strpres_fwcomp_bwcoll_allstpred init tr invtr bad init_preds pred_num =
  let compute_step_on from = (apply_tr_aut tr from) in
  let compute_step_back from = (apply_tr_aut invtr from) in
  let abstr actual preds = (bw_coll_allstpred actual preds) in
  let refine actual last_inter preds preds_number = 
     refinetest preds last_inter;
     (preds @ [((string_of_int preds_number),last_inter)]) in 
  let empty = automaton (Automaton.get_alphabet init) "
		States
		Final States
		Transitions " in  
    (atrmc_main_loop init empty bad compute_step_on compute_step_back abstr refine init_preds pred_num);;

let rec compile_and_number_preds pred_str_list sigma =
  match pred_str_list with
      [] -> (1,[])
    | pred_str::pred_str_list_rest -> 
        match (compile_and_number_preds pred_str_list_rest sigma) with
          (pred_num,pred_list) ->
            (pred_num+1,((string_of_int pred_num),(automaton sigma pred_str))::pred_list);;

let atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tr_str bad_str init_preds_str_list =
  Printf.printf "\n\n== atrmc_strpres_fwcomp_bwcoll_allstpred ==\n"; flush stdout;
  Printf.printf "\nCompiling...\n"; flush stdout;
  let sigma = (alphabet sigma_str) in
  let init = (automaton sigma init_str) in
  let tr = (compile_transducer tr_str) in
  let itr = (inverse_transducer tr_str) in
  let bad = (automaton sigma bad_str) in
  let (pred_num,preds) = (compile_and_number_preds init_preds_str_list sigma) in
    Printf.printf "Computing...\n"; flush stdout;
    let start_time=Sys.time () in
      (do_atrmc_strpres_fwcomp_bwcoll_allstpred init tr itr bad preds pred_num);
      let stop_time=Sys.time () in
        Printf.printf "\nCPU time: %f\n" (stop_time -. start_time); flush stdout;;

(* ==================================================================================================== *)
(* **************************************************************************************************** *)
(* ***** ATRMC - wrappers for the main loop: structure preserving, forward computation,                 *)
(* *****         backward predicate-based labelling (with only the initial states being predicates).    *)
(* **************************************************************************************************** *)
(* ==================================================================================================== *)

let do_atrmc_strpres_fwcomp_bwcoll init tr invtr bad init_preds pred_num =
  let compute_step_on from = (apply_tr_aut tr from) in
  let compute_step_back from = (apply_tr_aut invtr from) in
  let abstr actual preds = (bw_coll actual preds) in
  let refine actual last_inter preds preds_number = 
     refinetest preds last_inter;
     (preds @ [((string_of_int preds_number),last_inter)]) in 
  let empty = automaton (Automaton.get_alphabet init) "
		States
		Final States
		Transitions " in  
    (atrmc_main_loop init empty bad compute_step_on compute_step_back abstr refine init_preds pred_num);;

let atrmc_strpres_fwcomp_bwcoll sigma_str init_str tr_str bad_str init_preds_str_list =
  Printf.printf "\n\n== atrmc_strpres_fwcomp_bwcoll ==\n"; flush stdout;
  Printf.printf "\nCompiling...\n"; flush stdout;
  let sigma = (alphabet sigma_str) in
  let init = (automaton sigma init_str) in
  let tr = (compile_transducer tr_str) in
  let itr = (inverse_transducer tr_str) in
  let bad = (automaton sigma bad_str) in
  let (pred_num,preds) = (compile_and_number_preds init_preds_str_list sigma) in
    Printf.printf "Computing...\n"; flush stdout;
    let start_time=Sys.time () in
      (do_atrmc_strpres_fwcomp_bwcoll init tr itr bad preds pred_num);
      let stop_time=Sys.time () in
        Printf.printf "\nCPU time: %f\n" (stop_time -. start_time); flush stdout;;

(* ==================================================================================================== *)
(* **************************************************************************************************** *)
(* ***** ATRMC - wrappers for the main loop: structure preserving, backward computation,                *)
(* *****         backward predicate-based labelling (with all states being predicates).                 *)
(* **************************************************************************************************** *)
(* ==================================================================================================== *)

let do_atrmc_strpres_bwcomp_bwcoll_allstpred init tr invtr bad init_preds pred_num =
  let compute_step_on from = (apply_tr_aut invtr from) in
  let compute_step_back from = (apply_tr_aut tr from) in
  let abstr actual preds = (bw_coll_allstpred actual preds) in
  let refine actual last_inter preds preds_number = 
     refinetest preds last_inter;
     (preds @ [((string_of_int preds_number),last_inter)]) in 
  let empty = automaton (Automaton.get_alphabet init) "
		States
		Final States
		Transitions " in  
    (atrmc_main_loop bad empty init compute_step_on compute_step_back abstr refine init_preds pred_num);;

let atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tr_str bad_str init_preds_str_list =
  Printf.printf "\n\n== atrmc_strpres_bwcomp_bwcoll_allstpred ==\n"; flush stdout;
  Printf.printf "\nCompiling...\n"; flush stdout;
  let sigma = (alphabet sigma_str) in
  let init = (automaton sigma init_str) in
  let tr = (compile_transducer tr_str) in
  let itr = (inverse_transducer tr_str) in
  let bad = (automaton sigma bad_str) in
  let (pred_num,preds) = (compile_and_number_preds init_preds_str_list sigma) in
    Printf.printf "Computing...\n"; flush stdout;
    let start_time=Sys.time () in
      (do_atrmc_strpres_bwcomp_bwcoll_allstpred init tr itr bad preds pred_num);
      let stop_time=Sys.time () in
        Printf.printf "\nCPU time: %f\n" (stop_time -. start_time); flush stdout;;

(* ==================================================================================================== *)
(* **************************************************************************************************** *)
(* ***** ATRMC - wrappers for the main loop: structure preserving, backward computation,                *)
(* *****         backward predicate-based labelling (with only the initial states being predicates).    *)
(* **************************************************************************************************** *)
(* ==================================================================================================== *)

let do_atrmc_strpres_bwcomp_bwcoll init tr invtr bad init_preds pred_num =
  let compute_step_on from = (apply_tr_aut invtr from) in
  let compute_step_back from = (apply_tr_aut tr from) in
  let abstr actual preds = (bw_coll actual preds) in
  let refine actual last_inter preds preds_number = 
     refinetest preds last_inter;
     (preds @ [((string_of_int preds_number),last_inter)]) in 
  let empty = automaton (Automaton.get_alphabet init) "
		States
		Final States
		Transitions " in  
    (atrmc_main_loop bad empty init compute_step_on compute_step_back abstr refine init_preds pred_num);;

let atrmc_strpres_bwcomp_bwcoll sigma_str init_str tr_str bad_str init_preds_str_list =
  Printf.printf "\n\n== atrmc_strpres_bwcomp_bwcoll_allstpred ==\n"; flush stdout;
  Printf.printf "\nCompiling...\n"; flush stdout;
  let sigma = (alphabet sigma_str) in
  let init = (automaton sigma init_str) in
  let tr = (compile_transducer tr_str) in
  let itr = (inverse_transducer tr_str) in
  let bad = (automaton sigma bad_str) in
  let (pred_num,preds) = (compile_and_number_preds init_preds_str_list sigma) in
    Printf.printf "Computing...\n"; flush stdout;
    let start_time=Sys.time () in
      (do_atrmc_strpres_bwcomp_bwcoll init tr itr bad preds pred_num);
      let stop_time=Sys.time () in
        Printf.printf "\nCPU time: %f\n" (stop_time -. start_time); flush stdout;;
