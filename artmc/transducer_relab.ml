open Taml

let rec relab_one_aut_rule rule transd_rules =
	if (transd_rules = []) then Rewrite.empty
	else
	match transd_rules with (a,b)::rest ->
		if ((Term.top_symbol(Rewrite.lhs rule)) = Symbol.of_string(a)) then
			Rewrite.add
				(Rewrite.new_rule
					(Common.Fsym 
						(Symbol.of_string b,
						Term.list_arguments(Rewrite.lhs rule)))
					(Rewrite.rhs rule)
				)
				(relab_one_aut_rule rule rest)
		else
			(relab_one_aut_rule rule rest);;
				

let rec relab_all_aut_rules rules transd_rules =
	if (Rewrite.is_empty rules) then Rewrite.empty
	else
	Rewrite.union 
		(relab_one_aut_rule 
			(Rewrite.first rules)
			transd_rules)
		(relab_all_aut_rules 
			(Rewrite.remainder rules)
			transd_rules) ;;

let relab_relab automat relab_transducer =
	match relab_transducer with (_,alpha,rules) ->
		Automaton.make_automaton
			alpha
			(Automaton.get_state_ops automat)
			(Automaton.get_states automat)
			(Automaton.get_final_states automat)
			Rewrite.empty 
			(relab_all_aut_rules 
				(Automaton.get_transitions automat) 
				rules);;
	

let rec relab_reverse_rules relab_rules =
	if (relab_rules=[]) then []
	else
	match relab_rules with (a,b)::rest ->
		(b,a) :: relab_reverse_rules rest ;;	
	

let relab_reverse automat relab_transducer =
	match relab_transducer with (alpha_1,alpha_2,rules) ->
		relab_relab 
			automat 
			(alpha_2,alpha_1,(relab_reverse_rules rules)) ;;

(*------------------------------------------------------------

let pravidla_relab=[ ("nn","ttt");
		     ("nn","nn");
		     ("n","n");
		     ("t","z");
		     ("t","t")];;

let sigma = alphabet "n:0 t:0 nn:2 tt:2";;

let vysl_abec = alphabet "n:0 t:0 z:0 nn:2 ttt:2";;

let relab_sys = (sigma, vysl_abec, pravidla_relab);;*)
