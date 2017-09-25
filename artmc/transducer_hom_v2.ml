(* -----------------------------------------
   Funkce pro zamenu promennych v pravidlech 
   ----------------------------------------- *)

open Taml

(* Starsi verze
 !!! nezamenuje promennou, za kterou bezprostredne nasleduje konec stringu - dodelat !!!
let change_vars_in_rules origvar newvar rules= 
	List.map (Str.global_replace (Str.regexp 
		(String.concat origvar ["\\([ \>\(\,]\\)";"\\([ \,\-\)]\\)"])) 
		(String.concat newvar ["\\1";"\\2"])) rules ;;*)

(* Prida mezery na zacatek a konec retezce *)
let add_spaces str1 =
	Str.global_replace 
		(Str.regexp "^ *\\(.*\\) *") " \\1 " str1;;

(* zameni jednu promennou za druhou ve vsech pravidlech *)
let change_vars_in_rules origvar newvar rules= 
	List.map (Str.global_replace (Str.regexp 
		(String.concat origvar ["\\([ \>\(\,]\\)";"\\([ \,\-\)]\\)"])) 
		(String.concat newvar ["\\1";"\\2"])) 
			(List.map add_spaces rules) ;;
(* zameni n-tou polozku z listu_1 za n-tou polozku z listu_2 (pro vsechna n) *)
let rec rename_vars list_1 list_2 rules =
	if (list_1 = []) then rules
	else
	match list_1 with a::b ->
		match list_2 with c::d ->
			rename_vars b d (change_vars_in_rules a c rules);;

(* ---------------------------------------------
   Nasledujici funkce je takovy podfuk. 
   Vysledny automat neni 100% timbuk kompatibilni a ja jsem nenasel, kde je problem.
   Resenim (ne moc elegantnim) je nasledujici funkce
   --------------------------------------------- *)

let reparse_automaton automat alphabet =
	Automaton.parse 
		alphabet
		(Specification.lexer (Stream.of_string(Automaton.to_string automat)));;
	

(* ---------------------------------------------
     Tady zacina implementace prepisu "tam"
   ---------------------------------------------*)

let rename_final_var aut_rule rules = 
	List.map (Str.global_replace (Str.regexp "\> *_final") ( String.concat ""
	 ["> ";(Term.to_string (Rewrite.rhs aut_rule))]) ) rules;; 

(* Slozeni pravidla automatu s pravidlem transduceru*)
let compose_one_rule_with_one_rule aut_rule transd_rule =
	match transd_rule with (x::a,_,b) ->
		rename_vars a (List.map Term.to_string (Term.list_arguments (Rewrite.lhs aut_rule))) 
			 (rename_final_var aut_rule b) ;;



(* Slozeni pravidla automatu se vsemi pravidly transduceru*)
let rec transduce_one_aut_rule aut_rule transd_rules =
	match transd_rules with [] -> [] |
	(a1::a2,b,c)::rest ->
		if (a1 = (Symbol.to_string(Term.top_symbol(Rewrite.lhs aut_rule)))) then
			(compose_one_rule_with_one_rule aut_rule (a1::a2,b,c)) @ 
				transduce_one_aut_rule aut_rule rest
		else transduce_one_aut_rule aut_rule rest;;
		
(* Slozeni vsech pravidel automatu s pravidly transdiceru *)
let rec transduce_aut_rules all_aut_rules transd_rules =
	if (Rewrite.is_empty all_aut_rules) then []
	else (transduce_one_aut_rule (Rewrite.first all_aut_rules) transd_rules) 
		@ (transduce_aut_rules (Rewrite.remainder all_aut_rules) transd_rules);;
	

(* prevede list pravidel (v retezcich) na variable_set 
  - je treba zadat abecedu a promenne, nad kterymi jsou pravidla tvorena *)
let rec transform_list_to_new_rules alpha variables list_of_rules =
	match list_of_rules with [] -> Rewrite.empty |
	rule :: rest ->
		Rewrite.add 
			(Rewrite.new_rule
			    (Term.parse 
			        alpha 
			        variables
			        (Specification.lexer (Stream.of_string
				    (Str.replace_first (Str.regexp "->.*$") "" rule )
				))
			    )
			    (Common.Special (Common.Const(Symbol.of_string 
				    (Str.replace_first (Str.regexp "^.*->") "" rule )
			    )))
			)
			(transform_list_to_new_rules alpha variables rest);;

(* Zaloha starsi verze
let rec transform_list_to_new_rules alpha variables list_of_rules =
	if (list_of_rules = []) then Rewrite.empty
	else
	match list_of_rules with rule :: rest ->
		Rewrite.union (Rewrite.parse alpha variables 
			(Specification.lexer (Stream.of_string	rule))) 
			(transform_list_to_new_rules alpha variables rest);;*)

let vars_to_transform aut n_states =
	Variable_set.parse (Specification.lexer (Stream.of_string
		(State_set.to_string (State_set.union n_states 
		(Automaton.get_states aut)))));;

let create_new_transitions automat transducer =
	match transducer with (_, abec, new_states, _, rules) ->
		transform_list_to_new_rules 
			abec 
			(vars_to_transform automat new_states)
			(transduce_aut_rules (Automaton.get_transitions automat) rules);;

	
let hom_run_transducer_low_level automat transducer =
	match transducer with (_, abec, new_states, variab, rules) ->
		Automaton.make_automaton 
			abec 
			(State_set.parse_ops (Specification.lexer (Stream.of_string(State_set.to_string 
				(State_set.union (Automaton.get_states automat) new_states)))))
			(State_set.union (Automaton.get_states automat) new_states)
			(Automaton.get_final_states automat)
			Rewrite.empty
			(create_new_transitions automat transducer);;
	
(* Myslim si, ze by mela stacit funkce hom_run_transducer_low_level, ale timbuk si to nemysli
   Nejsem to schopen najit, a proto pouziji takovouto hnusarnu *)
let hom_run_transducer automat transducer =
	match transducer with (_,abec,_,_,_) ->
		reparse_automaton 
			(hom_run_transducer_low_level automat transducer)
			abec;;
				
		


(* -----------------------------------------
    Pomocne funkce pro zpetny prepis
   ----------------------------------------- *)
   
(* Nasledujici funkce  dostane jako parametry automat list koncovych stavu a term 
  vraci podmnozinu listu stavu, do kterych se automat dostane po zpracovani termu *)
let rec is_term_accepted_by_state_set automat final_states term =
	if (final_states = []) then []
	else
	match final_states with a::b ->
		if (Automaton.run term a automat) then 
			a :: (is_term_accepted_by_state_set automat b term)
		else (is_term_accepted_by_state_set automat b term)
	
(* Zjisti, jestli je term akceptovany automatem *)
let is_term_accepted automat term =
	if ((is_term_accepted_by_state_set 
		automat
		(State_set.to_list (Automaton.get_final_states automat))
		term) = []) then false
	else true;;
	

(* Funkce vytvori vsechny variace s opakovanim delky n *)
let rec variace_low_level seznam_prvnich seznam_kandidatu seznam delka =
	if (delka = 0) then [seznam_prvnich]
	else
	if (seznam_kandidatu = []) then []
	else 
	match seznam_kandidatu with a::b ->
		(variace_low_level (a::seznam_prvnich) seznam seznam (delka-1)) @
		(variace_low_level seznam_prvnich b seznam delka);;

let variace seznam delka =
	variace_low_level [] seznam seznam delka;;
		
(* Funkce je volana z funkce "extend_automaton" 
   Vezme abecedu a kazdy symbol zmeni na _symbol *)
let states_alphabet_to_alphabet states =
	Alphabet.parse(Specification.lexer (Stream.of_string
		(Str.global_replace 
			(Str.regexp " \\([^ ]*:[0-9]*\\)") 
			" _\\1" 
			(add_spaces (Alphabet.to_string states)))
		));;

let rec transform_state_list_to_string_list state_list =
	if (state_list=[]) then []
	else
	match state_list with (Common.Const a)::b ->
		(Symbol.to_string a) :: (transform_state_list_to_string_list b);;
	

(* funkce dostane term ve forme retezce a vrati top symbol ve forme retezce *)
(*Asi nebude treba !!!! *)

(*
let get_top_symbol_from_term_in_string str =
	Str.replace_first 
		(Str.regexp "^ *\\([^( ]*\\).*$")
		"\\1"
		str;;*)

(* Create set of new rules for extended automaton *)
let rec extend_automaton_create_new_rules state_set =
	match state_set with [] -> Rewrite.empty |
	(Common.Const a)::b ->
		Rewrite.add
			(Rewrite.new_rule 
				(Common.Const (Symbol.of_string (String.concat 
					"" 
					["_"; (Symbol.to_string a)] )))
				(Common.Special (Common.Const a)) )
			(extend_automaton_create_new_rules b);;
	
	
(* Adding rules "_x -> x" for every state "x" of tree automaton *)
let extend_automaton automat =
	Automaton.make_automaton
		(Alphabet.union 
			(Automaton.get_alphabet automat) 
			(states_alphabet_to_alphabet
				(Automaton.get_state_ops automat)) )
		(Automaton.get_state_ops automat)
		(Automaton.get_states automat)
		(Automaton.get_final_states automat)
		(Automaton.get_prior automat)
		(Rewrite.union 
			(Automaton.get_transitions automat)
			(extend_automaton_create_new_rules 
				(State_set.to_list(Automaton.get_states automat))));;


(* Functions for creation (and managing) list of possible variations, which are needed 
   during reverse transducion.
   When is variations created "on-the-fly" during reverse transducion, many of them are created more 
   then one times and the complexity of transducion is very high. 
   So we create variations one times on the begining of transducion *)


let rec find_necessary_variations rules part_results=
	match rules with [] -> part_results |
	(a,b,c)::rest ->
  	   let length=(List.length a) in
		if (length =1) then
			find_necessary_variations rest part_results
		else
		if (List.mem (length-1) part_results) then
			find_necessary_variations rest part_results
		else
			find_necessary_variations rest ((length-1)::part_results);;
	
let rec create_necc_variations aut_state_list numlist part_results =
	match numlist with [] -> part_results |
	a::rest ->
		create_necc_variations
			aut_state_list
			rest
			((a,(variace aut_state_list a))::part_results);;


let create_necessary_variations rules verify_aut=
	create_necc_variations
		(transform_state_list_to_string_list
			(State_set.to_list(Automaton.get_states verify_aut)))
		(find_necessary_variations rules [])
		[];;
		

(* get necessary variation from variation list prepared by function create_necessary_variations 
   if variation is nou found then exception "Variation_not_found" is raised*)
exception Variation_not_found;;

let rec get_variation variation_list number=
	match variation_list with [] ->
		raise Variation_not_found |
	(a,b)::rest ->
		if (a=number) then b
		else get_variation rest number;;
			

(* -----------------------------------------------
     Reverse transducion implementation
   ----------------------------------------------- *)

(* Nasledujici funkce vytvari pravidla typu term -> stav pro vsechny stavy v state_set*) 
let rec hom_back_create_rules term state_set =
	match state_set with [] -> [] |
	(Common.Const a)::b ->
		(String.concat " -> " [term;(Symbol.to_string a)]) 
		:: (hom_back_create_rules term b);;
		
		
(* Zpetny prepis slozitejsich pravidel (alespon s jednou promennou) *)
let rec hom_back_test_if_rule_can_exist transd_rule verify_aut verify_aut_alpha variations =
	match variations with [] -> [] |
	var::rest ->
		match transd_rule with (a1::a2,b,c) ->
			(hom_back_create_rules 
			   (String.concat "" [a1;"(";(String.concat "," var);")"])
			   (is_term_accepted_by_state_set
				verify_aut
				(State_set.to_list(Automaton.get_states verify_aut))
				(Term.parse
					verify_aut_alpha
					Variable_set.empty
					(Specification.lexer (Stream.of_string
					    (match (rename_vars 
						a2 
						(List.map (Str.replace_first (Str.regexp "^") "_") var) 
						[b])
					     with xx::_ -> xx) 
				))
			   ))
			) @ (hom_back_test_if_rule_can_exist 
				transd_rule 
				verify_aut 
				verify_aut_alpha
				rest);;
					
		

(* In this function is reverse transducion realized *)
let rec hom_back_transduce trans_rules verify_aut verif_aut_alpha variation_list=
	match trans_rules with [] -> [] |
	(a,b,c)::rest ->
		if ((List.length a) = 1) then
		    (hom_back_create_rules 
			(match a with x::_ -> x)
			(is_term_accepted_by_state_set 
				verify_aut
				(State_set.to_list(Automaton.get_states verify_aut))
				(Term.parse
					verif_aut_alpha
					Variable_set.empty
					(Specification.lexer (Stream.of_string b))))) @
			(hom_back_transduce rest verify_aut verif_aut_alpha variation_list)
		else
			(hom_back_test_if_rule_can_exist 
				(a,b,c) 
				verify_aut
				verif_aut_alpha
				(*(variace 
					(transform_state_list_to_string_list
						(State_set.to_list(Automaton.get_states verify_aut)))
					((List.length a)-1))*)
				(get_variation variation_list ((List.length a)-1))
			) @	 
			(hom_back_transduce rest verify_aut verif_aut_alpha variation_list);;			


(* Funkce zavola vytvoreni pravidel pri zpetnem prepisu a nasledne je predela ze seznamu
   do struktury pouzite v timbuku *)
let hom_back_create_new_transitions automat transducer =
   let ext_aut=extend_automaton automat in
	match transducer with (abec, _, _, _, rules) ->
		transform_list_to_new_rules 
			abec 
			(Variable_set.parse (Specification.lexer (Stream.of_string
				(State_set.to_string (Automaton.get_states automat)))))
			(hom_back_transduce 
				rules 
				ext_aut
				(Automaton.get_alphabet ext_aut)
				(create_necessary_variations rules ext_aut)
				);;
	

(* Vytvoreni vysledneho automatu pri zpetnem prepisu *)
let hom_run_transducer_reverse_lowlevel automat transducer =
	match transducer with (abec, _, _, _, rules) ->
		Automaton.make_automaton 
			abec 
			(Automaton.get_state_ops automat)
			(Automaton.get_states automat)
			(Automaton.get_final_states automat)
			Rewrite.empty
			(hom_back_create_new_transitions automat transducer);;

(* Myslim si, ze by mela stacit funkce hom_run_transducer_reverse_lowlevel, ale timbuk si to nemysli
   Nejsem to schopen najit, a proto pouziji takovouto hnusarnu *)
let hom_run_transducer_reverse automat transducer =
	match transducer with (alpha,_,_,_,_) ->
	reparse_automaton
		(hom_run_transducer_reverse_lowlevel automat transducer)
		alpha;;

(* --------------------------------------------
    Funkce pro parsovani transduceru 
   -------------------------------------------- *)

(* Parsuje pravou stranu pravidla transduceru a zapisuje sablony pravidel pro vysledny automat *)
let rec parse_term termlist orig_state prefix number=
   let state = if (orig_state="_final") then prefix else orig_state in
   let nextstate = if (orig_state="_final") then "_final" else (orig_state^(string_of_int number)) in
	match termlist with [] -> ("",[]) |
	term::rest ->
	   match (parse_term rest state prefix (number+1)) with (a,b) ->
		if (Term.is_constant term) then 
			((String.concat "," [nextstate;a]),
			[String.concat " -> " 
				[(Term.to_string term);(nextstate)]] @ b)
		else if (Term.is_variable term) then 
			(String.concat "," [(Term.to_string term);a],b)
		else
		match (parse_term 
			(Term.list_arguments term) 
			(state^"_"^(string_of_int number)) 
			prefix
			1) 
		with (subst,vysledky) ->
			(* bude se delat toto :*)
			((String.concat "," [nextstate;a]),
			[(String.concat "" ([(Symbol.to_string (Term.top_symbol term));"("; 
				subst; ") -> ";nextstate]))] @ vysledky @ b);;


(* z sablon pravidel vygeneruje mnozinu novych stavu *)
let rec parse_add_new_states list_of_templates orig_state_set =
	match list_of_templates with [] -> orig_state_set |
	rule::rest ->
		(* nasledujici sekce je zde proto, ze stav "_final" neni realnym stavem,
		a proto ho nezaradim do vysledku *)
		try
		if ((Str.search_forward (Str.regexp "-> *_final") rule 0)>(-1)) then
			(parse_add_new_states rest orig_state_set)
		else (parse_add_new_states rest orig_state_set)
		with Not_found ->
		State_set.add
		(Common.Const(Symbol.of_string(
			Str.replace_first (Str.regexp "^.*-> *") "" rule)))
		(parse_add_new_states rest orig_state_set);;

(* prevede string na list "gg,ff,dd" -> ["gg";"ff";"dd"] *)
let rec parse_list_of_comma_string in_str =
	try
	if ((Str.search_forward (Str.regexp "^[^,]*$") in_str 0)>(-1)) then [in_str] else [in_str]
	with Not_found ->
	(Str.replace_first (Str.regexp "^\\([^,]*\\),.*$") "\\1" in_str) ::
	(parse_list_of_comma_string (Str.replace_first (Str.regexp "^[^,]*,") "" in_str));;

(* Vytvori levou stranu interniho zapisu pravidla *)
let parse_create_lhs_list lhs =
	try
	if ((Str.search_forward (Str.regexp "^[^()]+$") lhs 0)>(-1)) then [lhs] else [lhs]
	with Not_found ->
	(Str.replace_first (Str.regexp "^\\([^(]*\\)(.*$") "\\1" lhs) ::
		(parse_list_of_comma_string 
			(Str.replace_first (Str.regexp "^.*(\\(.*\\)).*$") "\\1" lhs));;
	
(* Prevede pravidlo z liskeho tvaru do interniho tvaru *)
let parse_create_rule in_rule alpha varset state_prefix=
	let lhs = (Str.replace_first (Str.regexp " *->.*$") "" in_rule) in
	let rhs = (Str.replace_first (Str.regexp "^.*-> *") "" in_rule) in
	match parse_term 
		[(Term.parse alpha varset (Specification.lexer (Stream.of_string rhs)))]
		"_final" state_prefix 1 with (_,rules) ->
	(parse_create_lhs_list lhs,rhs, 
		(List.map (Str.global_replace (Str.regexp(",)")) ")") rules));;

(* Prevadi pravidla do tvaru, ve kterem se interne pouzivaji *)
let rec parse_create_transd_rules in_rules alpha varset number=
	match in_rules with [] -> [] |
	current::rest ->
		(parse_create_rule current alpha varset ("xxx_"^(string_of_int number))) 
			:: (parse_create_transd_rules rest alpha varset (number+1));;

(* Vygeneruje sadu novych stavu pro automat na zaklade nove vytvorenych pravidel *)
let rec parse_get_new_states_form_new_rules rules =
	match rules with [] -> State_set.empty |
	(_,_,rule_list)::rest ->
		parse_add_new_states rule_list 
			(parse_get_new_states_form_new_rules rest);;

(* z pravidel, vstuni abecedy, vystupni abecedy a sady promennych vytvori typ, ktery 
   je pouzivan pro reprezentaci transduceru *)
let hom_parse_transducer in_transd in_alpha out_alpha varset=
	let rules= (parse_create_transd_rules in_transd out_alpha varset 1) in
	(in_alpha, out_alpha, parse_get_new_states_form_new_rules rules, varset, rules);;
	



