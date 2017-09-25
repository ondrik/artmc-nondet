(* 
V taml-u s podporou prace s retezci zadejte: 

#use "/usr/local/groups/verifikace/tree-transducer-0.1/transducer_main.ml";;
*)

(*#use
 * "/usr/local/groups/verifikace/tree-transducer-0.1/transducer_hom-v2.ml";;*)
(*#use
 * "/usr/local/groups/verifikace/tree-transducer-0.1/transducer_relab.ml";;*)
open Taml
open Transducer_hom_v2
open Transducer_relab

(* Spusteni transduceru na automat *)
let run_transducer transducer automat =
	match transducer with (relab, aut, hom) ->
	   Automaton.simplify(Automaton.determinise(
		hom_run_transducer
			(Automaton.simplify 
				(Automaton.inter aut (relab_relab (Automaton.simplify automat) relab)))
			hom
		));;


(* Spusteni transduceru na automat + union vysledku s puvodnim automatem *)
let run_transducer_u transducer automat =
	Automaton.simplify(
		Automaton.union 
			automat 
			(run_transducer transducer automat)
			);;

(* Spusteni zpetneho prepisu na automat *)
let run_transducer_reverse transducer automat =
	match transducer with (relab, aut, hom) ->
	   Automaton.simplify(Automaton.determinise(
		relab_reverse
			(Automaton.simplify 
				(Automaton.inter 
					aut 
					(hom_run_transducer_reverse (Automaton.simplify automat) hom)))
			relab
		));;
