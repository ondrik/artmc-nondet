(* Timbuk - Tree Automata completion and Reachability testing 
   Copyright (C) 2000-2004 Thomas Genet and Valérie Viet Triem Tong

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU Library General Public License version 2, as
   published by the Free Software Foundation.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

   See the GNU Library General Public License version 2 for more details
   (enclosed in the file LGPL).


   Version 2.0. Last modification 21/01/04
*)

(* Timbuk - Tree Automata completion and Reachability testing 
   Copyright (C) 2000-2004 Thomas Genet and Valérie Viet Triem Tong

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU Library General Public License version 2, as
   published by the Free Software Foundation.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

   See the GNU Library General Public License version 2 for more details
   (enclosed in the file LGPL).


   Version 2.0. Last modification 21/01/04
*)

(* Now the completion can be of two kind:

     dynamic one: 
     
     critical pairs are computed one by one, new transitions are computed and normalised
     one by one. This permits to have an interactive control upon the approximation and to use a mix of
     different normalisation tools: prior, norm rules, new states, merging of states or interactions with the
     user to normalise transitions by hand or interactively add some normalisation rules.

     Linearity checks are as usual: f(x, x, x) will not match f(q1, q2, q3) and then we check that
     intersection between q1, q2 and q3 is empty!

     
     purely static one: 
     
     The whole approximation and completion mechanism is statically pre-computed. The approximation rules 
     given either by prior or norm rules should be complete (cover all possible normalisation cases) when 
     starting the completion. Merging is still possible but no other tools (like interactively giving new
     states, or automatic new states, ...) can be used. Interactive addition  of normalisation rules is not 
     possible, either. 


*) 

open Common
IFDEF TABI THEN open Visu END
IFDEF TABI THEN open Specifs END

module Completion    
  (Variable : PRINTABLE_TYPE)
  (Symbol : PRINTABLE_TYPE)
  (Alphabet: ALPHABET_TYPE with type symbol=Symbol.t)
  (Variable_set: VARIABLE_SET_TYPE with type variable= Variable.t)
  (Term: TERM_TYPE with type alphabet= Alphabet.t and type symbol= Alphabet.symbol
		   and type variable= Variable.t
		   and type variable_set= Variable_set.t)
  (TRS: TRS_TYPE with type alphabet= Alphabet.t and type term= Term.t)
  (State_set: STATE_SET_TYPE with type state= Term.t
			     and type alphabet= Alphabet.t
			     and type symbol= Alphabet.symbol)
  (Automaton: AUTOMATA_TYPE with type substitution= Term.substitution
			    and type symbol= Alphabet.symbol
			    and type state= State_set.state
			    and type state_set= State_set.t 
			    and type alphabet= Alphabet.t 
			    and type term= Term.term 
			    and type transition_table= TRS.t 
			    and type rule= TRS.rule)
  (Spec: AUTOMATON_SAVING_TYPE with type automaton= Automaton.t
			       and type alphabet= Alphabet.t
			       and type variable_set= Variable_set.t
			       and type trs= TRS.t)
  (Gamma: GAMMA_TYPE with type transition_table= TRS.t 
		     and type gamma_content= Spec.gamma_content
		     and type alphabet= Alphabet.t
		     and type symbol= Alphabet.symbol
		     and type variable= Variable.t
		     and type state= State_set.state
		     and type transition= TRS.rule
					      and type variable_set= Term.variable_set
  					      and type substitution= Term.substitution
					      and type sol_filt= Automaton.sol_filt
					      and type ('a, 'b) folder= ('a, 'b) Automaton.folder
					      and type state_set= State_set.t)=

struct
  
  module State_type= Term
  module Transition= TRS

  let gamma= Gamma.gamma

  type gamma_content = Gamma.gamma_content
  type var_link = Gamma.var_link
  type automaton = Automaton.t
  type alphabet = Alphabet.t	
  type symbol = Symbol.t
  type state_set = State_set.t
  type state = State_type.t
  type transition_table = Transition.t
  type transition = Transition.rule

  type term = Term.term
  type variable = Variable.t 
  type substitution = Automaton.substitution
  type ('a, 'b) folder = ('a,'b) Automaton.folder
  type special_subst =S of substitution list | Not_valid
  type labelled_substitution = (state*substitution list) list
  type sol_filt= Automaton.sol_filt

  exception Bad_product

  (* function symbol used to encode variables in the term automaton of left and right hand side
     of rules... *)

  let var_symb = Symbol.of_string("##Var##") 

  (* function symbol used for representing product states *)

  let default_prod_sym= State_set.default_prod_symbol
			
  (* The flag for forced/not forced static completion *)

  let is_forced= ref false

  (* some counters for new states and new variables used for term rewriting system compilation into 
     tree automata *)
			  
  let comp_state = ref 0

  (* two variables 'x' and 'y' for translating a set [l] of [prior rules] into a [norm_rule]:
     [x -> y] -> [l] *)

  let patlhs_prior= Variable.of_string "###patlhs###"
  let patrhs_prior= Variable.of_string "###patrhs###"
  let patforce= Variable.of_string "###patforce###"
  let stateforce= Automaton.make_state (Symbol.of_string "#qstatic#")
  let pat_prior= TRS.new_rule (Var patlhs_prior) (Var patrhs_prior)
  let force_rule= TRS.new_rule (Var patforce) (Special stateforce)
		   
  (*  channels for user interaction *)
		   
  (* in and out channels are the same as those used in Gamma *)

  let in_chan= ref !Gamma.in_chan
  let out_chan= ref !Gamma.out_chan


  (* a flag for user interruption (Ctrl-C) *)

  let user_interrupt= ref false


  (* a reference on the current automaton to be completed, used to give the current
     state of the completion when the completion is interrupted thanks to a Ctrl-C *)

  let current_automaton= ref (Automaton.make_automaton 
				Alphabet.new_alphabet
				Alphabet.new_alphabet
				State_set.empty
				State_set.empty
				Transition.empty
				Transition.empty)
  let hsh_left_new=ref (Hashtbl.create (3000))	   
		     (*  let hsh_right_new=ref (Hashtbl.create (3000))	 *)
  let hsh_left_all = ref (Hashtbl.create (3500))  
		       (*  let hsh_right_all = ref (Hashtbl.create (3500)) 
			   let exist_subst=ref[]*)

  (* List of states that have to be locally deterministic in the tree automaton (due to matching of
      non linear variables on them. For checking of so-called linearity condition *) 
		       
  let locally_deterministic_states = ref []
					 

  let hash_tabl_print hsh =
    Hashtbl.iter ( fun a -> fun b -> print_string (" \n");print_string(Term.to_string a); print_string (" \nassocie a \n"); List.iter  (fun x -> print_string(TRS.rule_to_string x)) b ) hsh

  let hashtable_make list_trans =
    let rec aux list acc =
      match
	list
      with 
	  [] -> acc
	| rl::llist -> let l=(try Hashtbl.find acc (Automaton.rhs rl) with Not_found -> []) in Hashtbl.add  acc (Automaton.rhs rl) ([rl]@l); aux llist acc
    in aux list_trans  (Hashtbl.create (List.length list_trans))

	 
  (* modify a given hashtable hsh with a transition list*)

  let hashtable_modif hsh list_trans: (TRS.term, Automaton.rule list) Hashtbl.t =
    let rec aux list acc =
      match
	list
      with 
	  [] -> acc
	| rl::llist -> (let l=(try Hashtbl.find acc (Automaton.rhs rl) with
				   Not_found -> []) in Hashtbl.add  acc (Automaton.rhs rl)
							 (Common.clean ([ rl]@l)); aux llist acc)
    in aux list_trans hsh			   


  (* automaton conversion for Tabi *)

  IFDEF TABI THEN
let rec convert_config (t: term): Specifs.simple_term=
  (match t with 	  
  | Common.Special(t) -> (State (Term.to_string t))
  | Common.Fsym(f, largs) -> (Node ((Symbol.to_string f), (convert_l_config largs)))
  | Common.Const(a) -> (Node ((Symbol.to_string a), []))
  | _ -> failwith "No constants nor variables in configurations!")
and convert_l_config (lt: term list): Specifs.simple_term list= List.map convert_config lt
  END

  IFDEF TABI THEN
let convert_transition (trans: TRS.rule): Specifs.transition=
  ((convert_config (TRS.lhs trans)),(convert_config (TRS.rhs trans)))
  END
  
  IFDEF TABI THEN 
let rec convert_state_set (sts: State_set.t): string list=
  if State_set.is_empty sts then []
  else 
    let first= State_set.first sts in
    let rem= State_set.remainder sts in
    (Term.to_string first)::(convert_state_set rem)
  END
			
  IFDEF TABI THEN
let convert_automaton (aut: automaton): Specifs.automaton=
  {q= convert_state_set (Automaton.get_states aut);
   f= convert_state_set (Automaton.get_final_states aut);
   t= List.map convert_transition (TRS.to_list (Automaton.get_transitions aut))}
  END




  (*pretty printing for substitution *)
  let string_of_substitution_list l =
    let rec string_of_subst (l:substitution list) i=
      let rec aux (s:substitution)= 
	match
	  s
	with
	    [] -> "" 
	  | (x,t)::ss -> ((Variable.to_string x)^" <- "^(Term.to_string t)^(", ")^( aux ss)) 
      in 
	match
	  l
	with
	    [] -> ""
	  | s::ll ->  "solution "^(string_of_int(i))^": "^ 
	      (if s=[] then "Empty substitution" else (aux s))^("\n")^(string_of_subst ll (i+1))
    in string_of_subst l 0


  (*pretty printing for labelled substitution *)

  let rec labelled_substitution_to_string (l: (state * substitution list) list) : string=
    let string_of_label q=
      match
	q
      with 
	  Fsym(_,[q1;q2]) ->   ("Occurence in state "^(Term.to_string q2)^"! \n")
	|  Special(Fsym(_,[q1;q2])) ->   ("Occurence in state "^(Term.to_string q2)^"! \n")
	|_ ->  failwith " not a substitution "

    in 
    let rec string_of_subst (l:substitution list) i=
      let rec aux (s:substitution)= 
	match
	  s
	with
	    [] -> "" 
	  | (x,t)::ss -> ((Variable.to_string x)^" <- "^(Term.to_string t)^(if ss=[] then "" else ", ")^( aux ss)) 
      in 
	match
	  l
	with
	    [] -> ""
	  | s::ll ->  "solution "^(string_of_int(i))^": "^(if s=[] then "Empty substitution" else (aux s))^("\n")^(string_of_subst ll (i+1))

    in
      match
	l 
      with
	  [] -> ""
	| (q,s)::ll -> 
	    (if s=[] then (labelled_substitution_to_string ll)
	     else ((string_of_label  q)^(string_of_subst  s 1)^"\n\n"))^(labelled_substitution_to_string ll)

	    

  (*s Matching compilation *)

  (* Make an alphabet of one symbol *)

  let make_elt_alphabet s i = Alphabet.add_symbol s i Alphabet.new_alphabet

  (* get list of subterm of a term  *)	  
  let rec set_of_sub_term (t:term) =
    let aux t =
      match
	t
      with
	  Const(a) -> [t]
	| Var(x) -> [t]
	| Fsym(f,l) ->[t]@(flat_map set_of_sub_term l)
	| Special(_) -> [t]
    in ((aux t))


  (* Construction of {\em variable states} from variables *)

  let make_special_state_from_variable x :state = Fsym(var_symb,[Var(x)])


  (* new states used for normalisation of terms *)
						    
  let make_new_state () :state=
    begin      
      comp_state:=!comp_state+1;
      Const(Symbol.of_string("##q"^string_of_int(!comp_state)));
    end


  let is_generated_state (q: state): bool=
    match q with
	Const(s) -> "##q"=(String.sub (Symbol.to_string s) 0 3)
      | _ -> false

  (* associate a list of new state to a list of term *)    
  let rec make_abstraction_table l =    
    let rec aux (l:term list) =
      match
	l
      with
	  [] -> []
	| t'::l' -> 
	    match 
	      t'
	    with
	      | Var(x) -> [(t',(make_special_state_from_variable x))]@(aux l')
	      | Const(_) -> [(t',make_new_state())]@(aux l')
	      | Fsym(_) -> [(t',make_new_state())]@(aux l')
	      | Special(_) -> [(t', t')]@(aux l')  
		  (* Special terms (states) are abstracted by themselves *)
    in aux l


  (* Construction of a new transition *)	 
  let new_trans (f:Automaton.symbol) (l: state list) (q:state)  = Automaton.new_trans f l q


  (* Construction of transition table of a term-automata *)

  let make_transition_table (l: (term * state) list) :transition_table =
    let list_assoc = ref l in 
    let find_and_delete x =
      match 
	x 
      with 
	  Var(_) -> List.assoc x !list_assoc 
	| _ -> let res = List.assoc x !list_assoc in list_assoc := List.remove_assoc x !list_assoc;res in 

    let rec aux l  =
      match 
	l  
      with 
	  [] -> [] 
	|(t,q)::ll ->  
	   match 
	     t 
	   with 
	       Var(x) -> (aux ll) 
	     | Const (a) ->  [new_trans (Symbol.of_string (Term.to_string t)) [] q]@(aux ll ) 
	     | Fsym(f,list) -> [new_trans f (flat_map (fun x -> [find_and_delete x ]) list) q]@(aux ll)
	     | Special(_) -> (aux ll)
    in Transition.list_to_trs (aux l)  
	 

  (*create an automaton whose langage is empty *)
	 
  let term_automaton_empty = Automaton.make_automaton Alphabet.new_alphabet Alphabet.new_alphabet State_set.empty  State_set.empty  (Transition.list_to_trs []) (Transition.list_to_trs [])


  (* Is a state final in a term automaton (lhs or rhs), i.e. on wether q contains the 
     substring "rule" *)

  let is_final_label s =  (Gamma.variable_top_state_string= String.sub(Symbol.to_string s) 0 (String.length Gamma.variable_top_state_string))


  let is_final_state q =
    match
      q
    with
	Special (Fsym(_, [Fsym (s,[]);_])) ->( try is_final_label s with Invalid_argument "String.sub" -> false)
      | Fsym(_, [Fsym (_,[Var(s)]);_]) -> ( try is_final_label (Symbol.of_string (Variable.to_string s)) with Invalid_argument "String.sub" -> false)
      | Fsym(_, [Fsym (s,[]);_]) -> ( try is_final_label s with Invalid_argument "String.sub" -> false)
      | _ -> false


  (* is an intersection state corresponding to a variable association *)

  let is_var_state q =
    match
      q
    with
      | Fsym(_, [Fsym (_,[Var(s)]);_]) -> true
      | _ -> false 


  (* give the set of states that contain a list of transitions*)

  let list_states_of_transitions trs = 
    let rec aux l acc= 
      match l with
	  [] -> acc
	| t::rem -> 
	    (aux rem  ((Automaton.rhs t)::(Automaton.list_state t))@acc)
    in
      (aux (Transition.to_list trs) [])


  (* Specific automaton intersection for [term automaton] inter [usual automaton].
     BE-CAREFUL: For efficiency reasons, the state set field is not computed...
     but the final state set is. *)

  let intersection term_automaton usual_automaton =
    let at=  Automaton.inter term_automaton usual_automaton in 
    let list_states= list_states_of_transitions (Automaton.get_transitions at) in 
    let final_states= Common.my_find_all is_final_state list_states in
      Automaton.make_automaton  
	(Automaton.get_alphabet at)
	(Automaton.get_state_ops  at)
	(State_set.empty)
	(State_set.list_to_set final_states)
	(Automaton.get_prior at)
	(Automaton.get_transitions at)


  (* Sorting transitions by state into a folder *)

  let transition_by_state = Automaton.transitions_by_state

  let folder_assoc_lhs q delta =   
    try Common.my_map (fun x -> Automaton.lhs x) (Automaton.folder_assoc q delta)
    with Not_found -> []


  (*give the list of left/right hand side terms of a rewriting system*)
	
  let list_term_lhs rws =((Common.my_map (Transition.lhs) (Transition.to_list rws)))  
  let list_term_rhs rws = ((Common.my_map (Transition.rhs) (Transition.to_list rws)))


  (* translate a left or right member of a rewriting system into a term automaton *)

  let translate_one_term_into_automaton t i alphabet =
    let abstract = 
      match 
	t
      with 
	  Var(x) ->  [(t,(make_special_state_from_variable x))]
	|  Const(a) -> [(t,Fsym(Symbol.of_string(Gamma.variable_top_state_string^string_of_int(i)),[]))]
	| Fsym(f,l) ->  (
	    let set_subterm = Common.flat_map set_of_sub_term l in
	      [(t,Fsym(Symbol.of_string(Gamma.variable_top_state_string^string_of_int(i)),[]))]@(make_abstraction_table set_subterm))
	| _ -> failwith  "error in translate_one_term_into_automaton -- term should not be Special"
    in 
    let transition=  make_transition_table abstract
    and states=(State_set.list_to_set (snd (List.split abstract)))
    and final_states =(State_set.list_to_set  (List.find_all
						 is_final_state (snd(List.split abstract))))
    in 
      Automaton.make_automaton
	alphabet
	(make_elt_alphabet var_symb 1)
	states
	final_states
	(make_transition_table [])
	transition 


  let translater alphabet list_term =
    let rec aux alphabet list_term i=
      match
	list_term
      with 
	  []-> term_automaton_empty
	| t::tail ->  Automaton.make_fast_union
	    (translate_one_term_into_automaton t i alphabet ) (aux  alphabet tail (i+1))
    in aux alphabet list_term 1

  let translate_lhs (rws:TRS.ruleSystem) (alphabet: alphabet)= 
    let res =     translater   alphabet ( list_term_lhs rws)  in res

  let translate_rhs (rws:TRS.ruleSystem) (alphabet: alphabet)=
    translater  alphabet ( list_term_rhs rws)
      
  (* Cleaning of labelled substitutions: retrieves subtitutions mapping a variable to distinct values *)

  let rec clean_labelled_substitution l =
    let rec clean_subst s acc=
      match
	s
      with
	  [] -> acc 
	| (x,q)::ss -> 
	    try  
	      let q'= List.assoc x acc 
	      in 
		if q=q' 
		then clean_subst ss acc 
		else []
	    with 
		Not_found -> clean_subst ss ((x,q)::acc)
    in 
    let rec clean l =
      match
	l
      with
	  [] -> [] 
	| s::ll -> 
	    if s= [] then []::(clean ll)
	    else 
	      let res= clean_subst s [] in
		match res with
		    []-> (clean ll)
		  |_ -> (clean_subst s [])::(clean ll)
    in 
      match
	l
      with
	  [] -> [] 
	| (q,ls)::ll -> (q,(Common.clean (clean ls)))::(clean_labelled_substitution ll)

  (* make a folder (sorted by_state) with the set of transition  of an automaton *)

  let make_delta_folder at = Automaton.transitions_by_state (Transition.to_list (Automaton.get_transitions at))

			       
  (* from a config in the form f((x,q1), (q2,q3), (y,q4) ) give the part which defined a substitution 
     ie x <- q1, y <- q4 (the result is a substitution) *) 
			       
  let get_substitution_part (c:('a, 'b) Common.term_const) :substitution =
    let rec aux l acc= 
      match 
	l
      with
	  [] -> acc
	| q::ll ->	  
	    match 
	      q
	    with
		
		Special(Fsym(_, [Fsym(_, [Var(y)]); state])) -> aux ll ([(y, Special(state))]@acc)

	      | Special(Fsym(_,[q1;q2])) -> (aux ll acc)

	      | _ -> failwith "not an intersection automata"
    in
      match
	c
      with
	  Fsym(f,l) -> aux l [] 
	| _ -> [] 



  (* from a config in the form f((x,q1), (q2,q3), (y,q4) ) give the part which doesn't 
     defined a substitution ie  (q2,q3) *)

  let get_non_substitution_part (c:('a, 'b) Common.term_const) =  
    let rec aux l acc =
      match 
	l 
      with 
	  [] -> acc
	| q::ll ->   
	    match    
	      q 
	    with 	      
		Special(Fsym(_,[Fsym(_,[Var(_)]);_])) ->  (aux ll acc)

	      | Special(Fsym(_,[q1;q2])) -> (aux ll (acc@[q]))
	      | _ -> failwith "not an intersection automata"

    in   
      match
	c
      with
	  Fsym(f,l) -> aux l []
	| _ -> [] 


  (* Lists configurations leading to state [q] *) 

  let get_config_list q df =
    match  
      q
    with 
	Special(q') ->  (folder_assoc_lhs q' df) 
      | _ ->  (folder_assoc_lhs q df) 



  (* fonction which clean a substitution list: we keep only valid subst that are not mapping a variable
     to 2 distinct values and suppresses multiple occurrences of a substitution in the list *)

  let clean_lsubst l=
    let rec aux l acc =
      match 
	l
      with
	  [] -> acc
	| s::rem -> 
	    let subst_checked= Automaton.check_subst [s] in
	      if subst_checked=[] 
	      then aux rem acc
	      else 
		aux rem (subst_checked@acc)
    in aux l []



  (* Mixing of partial substitution (every possible composition is produced) *)

  let rec mixe_return list_of_list  =
    match 
      list_of_list 
    with 
      |list1::list2:: tail -> 
	 let rec distribute list return =
	   match list with
	     | h :: t -> distribute t ((Common.my_map (fun l -> h @ l) list2) @ return)
	     | [] -> return
	 in
	 let new_list2 = distribute list1 [] in
	   mixe_return (new_list2 :: tail)
      | list :: [] -> list
      | [] -> [[]]  
	  

  let rec partition (lsubst: (term * (substitution list)) list) (ok: substitution list) (bad: (state list) list):
    ((substitution list) * ((state list) list))=
    match lsubst with
	[] -> (ok, bad)
      | (config, subl)::rem ->
	  let cleant= (Common.clean (clean_lsubst subl)) in
	    if cleant=[] then partition rem ok ((Term.list_special config)::bad)
	    else partition rem (cleant@ok) bad

	  
  let rec distrib (subst:substitution) subst_list=
    Common.my_map (fun x -> subst@x) subst_list

  let subst_by_state=ref (Hashtbl.create (3000))


  (* Verify the coherence of a substitution: a variable must not be mapped 
     to distinct terms. This is a modified version of the [coherent] function of the [Term] module
     that stores the found inconsistencies in the substitutions in order to check the linearity condition
     latter on the completed tree automata *)

  (* adding of s1 =/= s2 to a list of locally deterministic states *)
  let add_locally_det (s1: state) (s2: state) (assoc: (state * (state list)) list): ((state * (state list)) list)=
    let v1= (try List.assoc s1 assoc with Not_found -> []) in
      if List.mem s2 v1 then assoc
      else 
	let v2= (try List.assoc s2 assoc with Not_found -> []) in
	  if List.mem s1 v2 then assoc
	  else 
	    match v1, v2 with 
		[],[] -> (s1, [s2])::assoc
	      | [],_::_ -> (s2, (s1::v2))::(List.remove_assoc s2 assoc)
	      | _, _ ->  (s1, (s2::v1))::(List.remove_assoc s1 assoc)


  let rec coherent (list: (variable * state) list) = 
    match list with
	[] -> []
      | (a_var,elt)::l -> try (let value= List.assoc a_var l in
				 if value = elt
				 then (coherent l)
				 else 
				   begin
				     locally_deterministic_states:= 
				       add_locally_det (Automaton.state_label value) 
					 (Automaton.state_label elt) !locally_deterministic_states;
				     (* For verifying linearity conditions on all occurrences 
					of non linear variables (and not only the first one) : 
					call again coherent on the remaining list, in order to complete
					the check on remaining variables 

					coherent l; *)
				     raise (Term.Terms_do_not_match (("Non linear variable "^(Variable.to_string a_var)^" mapped to distinct terms","")))
				   end)
	with Not_found -> (a_var,elt)::(coherent l)
	    


  (* Production of every substitution for a given state in a hash table of transitions *)

  let get_subst (q:state) hash_df: substitution list=
    
    let term_list_recognized_by q (* liste de termes *)=  
      try Common.my_map Automaton.lhs (Hashtbl.find hash_df q) with Not_found -> []   
    in 
    let subst_defined_by config (* list de substitution ([(x,q1);(y,q2)])*)= get_substitution_part config
    and leaving_states_in config (*liste d'etats *)=  get_non_substitution_part config 
    in  
    let rec aux (q:state)  (constr: substitution)=
      let qq= (match q with Special(y) -> y | _ -> q) in
      let subst_list_defined_by_leaving_states config (constr: substitution)= 
	let rec cut_empty_subst_branches l res_substs constr=
	  match l with
	      [] -> res_substs
	    | q::rem ->
		let lsubst= aux q constr in
		  if lsubst=[]    (* if one of the partial substitution list is empty there is no solution *)
		  then [[]]       (* the no-solution substitution of mixe_return! @&!&@ *)
		    
		  (* otherwise the substitution is conserved and added to the list *)
		    
		  else (cut_empty_subst_branches rem (lsubst::res_substs) constr)
		    
	in
	let part_subst= (subst_defined_by config) in
	let new_constr= (try (Term.coherent (part_subst @ constr))
			 with Term.Terms_do_not_match(_) -> []) in

	  if (new_constr=[]) && (not(constr=[]) or (not(part_subst=[]))) 
	  then [[]]
	  else cut_empty_subst_branches (leaving_states_in config) [] new_constr
	    
      in
      let subst= try (Hashtbl.find !subst_by_state qq) 
      with 
	  (* if the substitution has not been already computed, we do it *)
	  Not_found -> 
	    let new_subst= Common.my_map 
			     (fun config -> (config, (distrib  
						 (subst_defined_by config ) 
						 ( mixe_return 
						     (subst_list_defined_by_leaving_states config
							constr)))))
			     (  term_list_recognized_by qq) in
	    let (ok, bad)= partition new_subst [] [] in

	    let _= Hashtbl.add !subst_by_state qq ok in
	      subst_by_state:=!subst_by_state ;
		ok
      in subst
    in
      aux q []


  (* Given a set of new intersection transitions (epsilon), find useful transitions in an old automaton (last)
      necessary to produce complete substitutions *) 

  let find_useful_transition  at_old at_new hsh_all hsh_new= 
    let vu=ref [] and list_states=ref [] in 
    let new_transition= TRS.to_list(Automaton.get_transitions at_new) in
    let  all_transition= new_transition@(TRS.to_list(Automaton.get_transitions at_old)) 
    in  
    let appearing_in tr = (* we get rid of special*)
      Common.my_map (fun x -> 
		  match 
		    x 
		  with 
		      Special y -> y 
		    | _ ->x) (get_non_substitution_part (Automaton.lhs tr))
    in
    let right_member tr = 
      (fun x -> 
	 match 
	   x 
	 with 
	     Special y -> y 
	   | _ ->x) 
      (Automaton.rhs tr) (* no special*)
    in 
    let trans_that_leads_to q hsh_all  = (* q is not special*) 
      try  (Hashtbl.find
	      (hsh_all) (q)) with Not_found -> []
    in
    let trans_where_appear q all_trans= (* special*)
      try Common.my_find_all
	(fun tr -> List.mem (q) (appearing_in tr))
	all_trans with Not_found -> []
    in
    let deja_vu tr = List.mem tr !vu 
    in 
    let rec get_useful_transition list_tr all_trans hsh_result hsh_all
      hsh_new=
      match 
	list_tr
      with 
	  [] -> hsh_result
	| tr::llist -> (
	    list_states:=(Automaton.rhs tr)::(!list_states);
	    if deja_vu tr 
	    then  get_useful_transition llist all_trans hsh_result hsh_all hsh_new 
	    else (
	      vu:= tr::(!vu);
	      let more_transition=(trans_where_appear (right_member
							 tr) all_trans)@(Common.flat_map (fun q ->
											    trans_that_leads_to q hsh_all)
									   (appearing_in tr))          in
	       
		get_useful_transition 
		  (llist@more_transition)
		  all_trans
		  (hashtable_modif hsh_result ([tr])) hsh_all hsh_new))
    in 
    let rec finish new_trans acc hsh_all hsh_new=
      match
	new_trans
      with
	  [] -> acc
	| tr::list -> (finish list (get_useful_transition [tr]
				      all_transition acc hsh_all hsh_new) hsh_all hsh_new )
    in 
    let result = finish new_transition hsh_new hsh_all hsh_new
    in  
      (result,Common.clean (!list_states))
      


  let find_new_substitutions  hsh new_states =
    let useful_final_states =
      Common.clean (Common.my_find_all is_final_state(new_states ))    
    in 
      Hashtbl.clear !subst_by_state ;
      subst_by_state:=!subst_by_state  ;
      let rec  aux (lq:state list) hsh acc =
	match
	  lq
	with 
	    [] -> acc
	  | x::llq-> (
	      let res= (x,(get_subst x hsh)) in 
		aux llq hsh (res::acc)      )
      in 

	( clean_labelled_substitution (aux useful_final_states hsh []))


  (* find only new transition from automaton intersection between left
     member of a rewriting system and last automaton, automaton intersection
     between left member of a rewring system and new automaton, automaton
     intersection between right member of a rewring system and the whole
     automaton *)

  let rec length l=
    let rec aux l acc=
      match
	l
      with 
	  [] -> acc
	|(q,ll)::tail->aux tail (List.length ll+acc)
    in aux l 0


  let sort_and_add list_exist list_new=
    let rec add q l list_exist acc =
      match
	list_exist 
      with 
	  [] -> acc@[(q,l)]
	| (q',l')::tail -> 
	    if q=q' 
	    then (acc@[(q,l@l')]@tail)
	    else add q l tail (acc@[(q',l')])
    in 
    let rec aux list_exist list_new =
      
      match
	list_new 
      with 
	  [] -> list_exist
	| (q,l)::tail -> aux (add q l list_exist []) tail 
    in aux list_exist list_new

  let rec length l=
    let rec aux l acc=
      match
	l
      with 
	  [] -> acc
	|(q,ll)::tail->aux tail (List.length ll+acc)
    in aux l 0



  let new_subst at_lhs_x_old at_lhs_x_new = 
    (* List of (intersection states lists) representing invalid variable associations, is initialized *)
    (* This list is updated by get_substs *)

    let new_trans_left= (TRS.to_list(Automaton.get_transitions at_lhs_x_new)) in
      (Hashtbl.clear !hsh_left_new);                                (* updating of hsh_* *)
      hsh_left_new:=hashtable_modif !hsh_left_new new_trans_left ;
      hsh_left_all:= hashtable_modif !hsh_left_all new_trans_left; 
      let (hsh_useful_transition_left,list_states_left) = find_useful_transition
							    at_lhs_x_old at_lhs_x_new !hsh_left_all  !hsh_left_new in   

      let new_subst_left=  find_new_substitutions hsh_useful_transition_left list_states_left in 
	new_subst_left


  (*s Completion mechanism *)

  (* Now the completion can be of two kind:

     dynamic one: 
     
     critical pairs are computed one by one, new transitions are computed and normalised
     one by one. This permits to have an interactive control upon the approximation and to use a mix of
     different normalisation tools: prior, norm rules, new states, merging of states or interactions with the
     user to normalise transitions by hand or interactively add some normalisation rules.

     
     purely static one: 
     
     The whole approximation and completion mechanism is statically pre-computed. The approximation rules 
     given either by prior or norm rules should be complete (cover all possible normalisation cases) when 
     starting the completion. Merging is still possible but no other tools (like interactively giving new
     states, or automatic new states, ...) can be used. Interactive addition  of normalisation rules is not 
     possible, either. *) 


  (* In a [dynamic_completion_state], we find the 
     - trs: current TRS (or part of it) used for
     completion, 
     - states: the completed set of states (with their description)
     - state_ops: the completed set of state_ops, 
     - delta: the current delta (folder of transitions categorized by symbol and then by state), 
     - g_content: which is the dynamic approximation information used by gamma,

     - index: the last natural used to label new states.
  *)

  type dynamic_completion_state = 
      {trs: TRS.t; 
       last: automaton; 
       epsilon: automaton; 
       alhs: automaton; 
       alhs_x_last: automaton; 
       alhs_x_epsilon:automaton; 
       index: int;
       g_content: gamma_content;
       step: int}


  (* In case of static completion, intersection automata for non-linked variables can be replaced by dependance 
     trees between the states *)

  (* dependances trees used to represent dependencies between transitions:
     e.g. transitions [f(q1,q2,q3)-> q4, g(q4) -> q0] are represented by a tree where
     nodes q1, q2, q3 have directed edges towards q4 and q4 have a directed edge towards q0 which is a leaf.
     The father relation is the only one represented in the [dep_tree] structure.

     Those trees are used for finding new substitutions in an intersection automaton between
     a lhs and the automaton to complete *)

  type dep_tree= (state * (state list)) list
		   
  let rec dep_tree_union (g1: dep_tree) (g2: dep_tree)=
    match g1 with
	[] -> g2
      | (q1, lsucc)::rem ->
	  let lg2= try (List.assoc q1 g2) with Not_found -> [] in
	    (q1, (Common.union lg2 lsucc))::(dep_tree_union rem (List.remove_assoc q1 g2))

  (* Construct the dep_tree containing all the edges of [g1] not occurring in [g2] *)

  let rec dep_tree_difference (g1: dep_tree) (g2: dep_tree)=
    match g1 with
	[] -> []
      | (q1, lsucc)::rem ->
	  let lg2= try (List.assoc q1 g2) with Not_found -> [] in
	    if lg2 = [] 
	    then (q1, lsucc)::(dep_tree_difference rem g2)
	    else 
	      let filt= List.filter (function q -> not (List.mem q lg2)) lsucc in
		if filt= [] then (dep_tree_difference rem g2)
		else (q1, filt)::(dep_tree_difference rem g2)
		  


  let make_dep_tree (a: automaton)= 
    let rec add_all_states (g: dep_tree) (ls: state list) (son: state) (finished: dep_tree)=
      match g with
	  [] -> (Common.my_map (function x -> (x,[son])) ls)@finished   (* remaining states of ls are to be added *)
	| (s1, otherls)::rem ->
	    let not_s1= List.filter (function x -> not (State_type.equal x s1)) ls in
	      if not_s1=ls 
	      then (add_all_states rem ls son ((s1, otherls)::finished))
	      else (add_all_states rem not_s1 son ((s1, (Common.union [son] otherls))::finished))
    in
    let rec all_trans_aux (l: transition list) (gdone: dep_tree)=
      match l with
	  [] -> gdone
	| t::rem ->
	    let fathers= Common.clean(Automaton.list_state t) in
	    let son= Automaton.rhs t in
	      all_trans_aux rem (add_all_states gdone fathers son [])
    in all_trans_aux (Transition.to_list (Automaton.get_transitions a)) []


  (* When completing the i+1-th completion step:
     A static rule is a precompiled version of a rewrite rule (one rule may be compiled into several
     static rules. [salhs] is the automaton recognising the lhs of the rule. [inter_last] is the dependence 
     tree corresponding to the intersection between the [alhs] and the [slast] automaton corresponding to the 
     i-1 completion step. [inter_epsilon] is the intersection between the [alhs] and the transitions of 
     [sepsilon] (to add to [slast] to get the i-th completion step automaton). [rhsdat] is the 
     statically compiled data for the rhs of
     the rule *)


  type linked_var_match= {linked_inter_last: automaton; linked_inter_epsilon: automaton; delstate: state list}

  type static_rule= {salhs: automaton; inter_last: automaton; inter_epsilon: automaton; 
		     non_lin_vars: variable list;
		     last_dep_tree: dep_tree;
		     rhsdat: Gamma.rhs_data} 
		      
  type static_completion_state = 
      { strs: TRS.t;
	sg_content: gamma_content; 
	slast: automaton; 
	sepsilon: automaton; 
	static_rules: static_rule list;
	new_state: int;
        sstep: int}


  type completion_state= Dyn of dynamic_completion_state | Static of static_completion_state

  let get_alphabet (cs: completion_state)= 
    match cs with 
	Dyn(csd) -> Automaton.get_alphabet csd.epsilon
      | Static(css) -> Automaton.get_alphabet css.sepsilon

  let get_state_ops (cs: completion_state)=
    match cs with 
	Dyn(csd) -> (Automaton.get_state_ops csd.epsilon)
      | Static(css) -> (Automaton.get_state_ops css.sepsilon)


  let get_all_trans (cs: completion_state) = 
    match cs with 
	Dyn(csd) -> Transition.union_fast (Automaton.get_transitions csd.last) (Automaton.get_transitions csd.epsilon)
      | Static(css) -> Transition.union_fast (Automaton.get_transitions css.slast) (Automaton.get_transitions css.sepsilon)


  let get_automaton_from_completion_step (cs: completion_state)=
    match cs with
	Dyn(csd) -> Automaton.modify_prior (Automaton.make_fast_union csd.last csd.epsilon) (Gamma.get_prior csd.g_content)
      | Static(css) -> Automaton.make_fast_union css.slast css.sepsilon   (* no prior trans for static norm ? *)


  let get_new_trans (cs: completion_state)= 
    match cs with
	Dyn(csd) -> (Automaton.get_transitions csd.epsilon)
      | Static(css) -> (Automaton.get_transitions css.sepsilon)


  let get_step_number (cs: completion_state)= 
    match cs with
	Dyn(csd) -> csd.step
      | Static(css) -> css.sstep


  let get_gamma (cs: completion_state)= 
    match cs with
	Dyn(csd) -> csd.g_content
      | Static(css) -> css.sg_content


  let empty_automaton= Automaton.make_automaton Alphabet.new_alphabet Alphabet.new_alphabet State_set.empty
			 State_set.empty Transition.empty Transition.empty


  (* Construction of a completion state *)

  (* a dynamic one *)

  let make_dynamic_completion_state trs aut gamma_content i s: dynamic_completion_state=
    let alpha= Automaton.get_alphabet aut in
    let alhs= translate_lhs trs (Automaton.get_alphabet aut) in
    let alhs_x_aut= intersection alhs aut in
      hsh_left_all:= hashtable_make (TRS.to_list(Automaton.get_transitions alhs_x_aut));
      (*    hsh_right_all:= hashtable_make (TRS.to_list(Automaton.get_transitions arhs));*)
      {trs= trs; 
       last= empty_automaton; 
       epsilon= aut; 
       alhs= alhs; 
       alhs_x_last= empty_automaton;   (* since initially last is empty *)
       alhs_x_epsilon= intersection alhs aut; 
       index=i;
       g_content= Gamma.add_prior_to_gamma (Automaton.get_prior aut) gamma_content;
       step=s}


  (* Static completion States *)

  (* Simplifying an intersection tree automaton with regards to a set of variables *)

      
  (* Simplifying an intersection tree automaton for matching, w.r.t. a list of variables [lvar]:
     We reduce the transitions [lt] to parts concerning this list of variables. [delstate] represents 
     the states that are already known not to be related to the variables of [lvar] and that can thus
     directly be deleted in [lt].  *) 
      
  (* states are not special ! *)


  (* Filters a list of states w.r.t. a delstate list *)

  let rec clear_state (lterm: term list) (delstate: state list) (lvar: variable list) =
    match lterm with
	[] -> []
      | t::rem -> 
	  match t with
	      Fsym(f, [Fsym(g, [Var(y)]); state]) -> 
		if List.mem y lvar 
		then (Fsym(f, [Fsym(g, [Var(y)]); state]))::(clear_state rem delstate lvar)
		else (clear_state rem delstate lvar)
	    | q -> 
		if List.mem q delstate 
		then (clear_state rem delstate lvar)
		else q::(clear_state rem delstate lvar)


  (* auxiliary function for the next simplify function *)

  let rec simp_aux (lt: transition list) (passed: transition list)(delstate: state list) 
    (touched: bool) (lvar: variable list) :(transition list * state list)=
    match lt with 
	[] -> 
	  if touched then (simp_aux passed [] delstate false lvar)
	  else (passed, delstate)
      | t::rem -> 
	  let lhs_states= Automaton.list_state t in
	  let rhs_state= Automaton.rhs t in
	  let f= Automaton.top_symbol t in
	  let rhs_into_delstate= List.mem rhs_state delstate in
	    if rhs_into_delstate
	    then simp_aux rem passed delstate touched lvar
	    else 
	      let res= clear_state lhs_states delstate lvar in
		if res= [] 
		then simp_aux rem passed (Common.add rhs_state delstate) (touched or(not rhs_into_delstate)) lvar
		else simp_aux rem ((Automaton.new_trans f res rhs_state)::passed) delstate touched lvar
		  

  let simplify (a: automaton) (lvar: variable list) 
    (delstate: state list): (automaton * state list)=
    let (new_trans, dels)= simp_aux (Transition.to_list (Automaton.get_transitions a)) [] delstate false lvar in
      (Automaton.modify_transitions a (Transition.list_to_trs new_trans), dels)


  (* splitting the two intersection automaton into several simplified automata, according
     to the linked variable partition *) 

  let rec split (inter_last: automaton) (inter_epsilon: automaton) (var_lin: var_link)=
    match var_lin with 
	[] -> []
      | lvar::rem ->
	  let (inter_last_lvar, dels1)= simplify inter_last lvar [] in
	  let (inter_epsilon_lvar, dels2)= simplify inter_epsilon lvar dels1 in
	    {linked_inter_last= inter_last_lvar; linked_inter_epsilon= inter_epsilon_lvar; 
	     delstate= dels2}::(split inter_last inter_epsilon rem)



  (* retrieve non useful (not linked to final states) and non acessible states in intersection automata *)
      
  let static_clean (last: automaton) (epsilon: automaton): (automaton * automaton)=
    let epsilon_list= (Transition.to_list (Automaton.get_transitions epsilon)) in
    let last_list= (Transition.to_list (Automaton.get_transitions last)) in
    let new_final_states= (State_set.union 
			     (Automaton.get_final_states epsilon)
			     (Automaton.get_final_states last)) in
    let union= Common.union last_list epsilon_list in      
      
      
    (* utility cleaning *)
      
    let rec util_aux (trans_in: transition list) (trans_temp: transition list)
      (trans_out: transition list) (set: state list) (new_addition: bool): transition list= 
      match trans_in with
	  [] -> 
	    if not new_addition then trans_out
	    else util_aux trans_temp [] trans_out set false
	| first_trans::rem -> 
	    let l_args = Automaton.list_state first_trans in
	    let right_state = Automaton.rhs first_trans in
	      if List.mem right_state set
	      then util_aux rem trans_temp (first_trans::trans_out) (Common.union l_args set) true
	      else util_aux rem (first_trans::trans_temp) trans_out set new_addition
    in
      
    (* accessibility cleaning modified *)
      
    let rec acc_aux (trans_in: transition list) (trans_temp: transition list) 
      (trans_out:transition list) (set: state list) (new_addition: bool)= 
      match trans_in with
	  [] -> 
	    if not new_addition then trans_out
	    else acc_aux
	      trans_temp
	      []
	      trans_out
	      set
	      false
	| first_trans::rem -> 
	    let l_args = Automaton.list_state first_trans in
	    let right_state = Automaton.rhs first_trans in
	      if List.for_all (function s -> (List.mem s set) or (is_var_state s)) l_args
	      then acc_aux rem trans_temp (first_trans::trans_out) (Common.add right_state set) true
	      else acc_aux rem (first_trans::trans_temp) trans_out set new_addition
    in
      
    let new_union = util_aux (acc_aux union [] [] [] false) [] [] 
		      (State_set.to_list new_final_states) false in
      
    (* accessibility cleaning alone is not enough since it does not suppress partial runs in the 
       automaton, for instance: f((x, q1)) -> (q0, q1) is clean w.r.t. accessibility even if
       (q0,q1) is not a final state *)
      
    let (new_epsilon_trans, new_last_trans)= 
      List.partition (function t -> (List.mem t epsilon_list)) new_union in
    let last_retrieved= List.filter (function t -> not (List.mem t new_union)) last_list in
    let epsilon_retrieved= List.filter (function t -> not (List.mem t new_union)) epsilon_list in      
      ( (Automaton.modify_final 
	   (Automaton.modify_transitions last 
	      (Transition.list_to_trs new_last_trans))
	   new_final_states),
	(Automaton.modify_final
	   (Automaton.modify_transitions epsilon
	      (Transition.list_to_trs new_epsilon_trans))
	   new_final_states))
      


  (* retrieve every non satisfiable transition in the intersection automaton *)
	    
  (* the matching tree automaton has to be cleant w.r.t. the constraints on the states:
     where transitions including a state (qx, qa) s.t. the constraint of the [static_rule] 
     contains (qx =/= qa) are all discarded! *)

  let is_not_var_or_var_but_sat  (c: sol_filt) (s: state): bool=
    match s with
	Fsym(_, [s1; s2]) ->
	  (match s1 with   
	       Fsym(s,[x]) ->  
		 if (Symbol.equal s var_symb) then
		   (* it is a variable *)
		   not ((Gamma.eq_solve (Automaton.And ((Automaton.S (x, (Special(s2)))), c)))=Automaton.Bottom)
		 else true
	     | _ -> true  (* it is not a variable *))
      | _ -> failwith "The transitions are not valid cartesian product!!"
	  
  let rec clean_unsat_trans (lt: transition list) (c: sol_filt): transition list=
    match lt with
	[] -> []
      | t::rem -> 
	  (* we check states of the transition and its rhs *)
	  let largs= Automaton.list_state t in
	  let to_be_checked= (Automaton.rhs t)::largs in
	    if (List.for_all (is_not_var_or_var_but_sat c) to_be_checked)
	    then t::(clean_unsat_trans rem c)
	    else clean_unsat_trans rem c


  (* Checking the linearity condition on [norm_rules] applying on non linear variables 
     automaton [a] has to be already cleant (variable assignation has to be possible w.r.t 
     automaton structure) *)

  let norm_rules_non_lin (vars: variable list) (const: sol_filt) (a: automaton): unit=
    let rec filter (var: variable) (q:state) (l: state list): (state list)=
      match l with 
	  [] -> []
	| Fsym (_, [Fsym (_, [Var z]); qsubst])::rem -> 
	    if z=var && (not (q = qsubst) )
	    then Common.add qsubst (filter var q rem)
	    else (filter var q rem)
	| _::rem -> (filter var q rem)
    in

    let rec tag_states (l: (variable * state) list): unit=
      match l with
	  [] -> ()
	| (var,Special(state))::rem -> 
	    let all_compared_states= 
	      filter var state 
		(List.flatten (Common.my_map Automaton.list_state 
				 (TRS.to_list (Automaton.get_transitions a)))) in
	      List.iter (function x -> (locally_deterministic_states := (add_locally_det state x !locally_deterministic_states)))
		all_compared_states;
	      (tag_states rem)
	      
	| _ -> failwith "Non valid Gamma.const_find result!"
    in 
      if vars=[] then ()
      else 
	let res= Gamma.const_find vars const in tag_states res


  let global_norm_rules_non_lin (cs: static_completion_state): unit=
    let global_aut= Automaton.make_fast_union cs.slast cs.sepsilon in
      List.iter 
	(function sr -> 
	   norm_rules_non_lin sr.non_lin_vars (sr.rhsdat).Gamma.const
	     (snd (static_clean empty_automaton (intersection sr.salhs global_aut))))
	cs.static_rules
	



  (* Producing a static rule list from a list of renamed lhs (associated with their int renaming) 
     and a [rhs_table] (also associating a rhs to its int renaming). 
     This function essentially normalises the lhs *)


  let rec associate (lhs_list: transition list) (rhs_table: Gamma.rhs_table) 
    (last: automaton) (epsilon: automaton): static_rule list=
    
    (* The rhs of the transition corresponds to the variable to use for the 
       abstraction of the top of the rule *)
    
    let abstract (t: transition)=
      match ((Transition.lhs t),(Transition.rhs t)) with
	  Const(a), Var(top) -> [((Const a), (make_special_state_from_variable top))]
	| Fsym(f, l), Var(top) -> 
	    let set_subterm = Common.flat_map set_of_sub_term l in
	      [(Fsym(f, l), (make_special_state_from_variable top))]@(make_abstraction_table set_subterm)
	| _ -> failwith "Non valid lhs of transition!!"
    in
      match (lhs_list, rhs_table) with
	  ([], []) -> []
	| ([], _) -> failwith "Incoherent number of lhs and rhs_dat!"
	| (_, []) -> failwith "Incoherent number of lhs and rhs_dat!"
	    
	| (trans::rem_lhs, rhsd::rem_rhs) ->  
	    let all_linked_vars= rhsd.Gamma.linked_vars in
	    let all_non_linked_vars= rhsd.Gamma.non_linked_vars in
	      try(
		let abs= abstract trans in
		let trans_for_lhs= make_transition_table abs in
		let autom_for_lhs= Automaton.make_automaton  
				     Alphabet.new_alphabet    (* no use of alphabet for this automaton! *) 
				     (make_elt_alphabet var_symb 1)
				     (State_set.list_to_set (snd (List.split abs)))
				     (State_set.list_to_set [(match (Transition.rhs trans) with Var(y) -> (make_special_state_from_variable y)| _ -> failwith "associate: Non valid rhs!")])
				     (make_transition_table [])
				     trans_for_lhs

		in
		let complete_inter_last= intersection autom_for_lhs last in
		let inter_epsilon= intersection autom_for_lhs epsilon in

		let non_lin_vars= Term.list_non_linear_variables (Transition.lhs trans) in

		(* the matching tree automaton has to be cleant w.r.t. the constraints on the states:
		   where transitions including a state (qx, qa) s.t. the constraint of the [static_rule] 
		   contains (qx =/= qa) are all discarded! *)
		  
		let complete_inter_epsilon=  
		  Automaton.modify_transitions inter_epsilon 
		    (Transition.list_to_trs (clean_unsat_trans 
					       (Transition.to_list (Automaton.get_transitions inter_epsilon))
					       rhsd.Gamma.const)) in

		  {salhs= autom_for_lhs;   
		   inter_last= complete_inter_last; (* should be empty *)
		   inter_epsilon= complete_inter_epsilon; (* should not be cleant because some transitions
							     may be used in a later completion step *)
		   non_lin_vars= non_lin_vars;
		   last_dep_tree= [];
		   rhsdat= rhsd}::associate rem_lhs rem_rhs last epsilon
	      )with Not_found -> failwith "Static completion: coherence problem between lhs and rhs list"
		  
		  
  (* a static one *) 
		  
  let make_static_completion_state trs aut gamma_content s (forced:bool): static_completion_state=
    let new_norm_rules=
      (let prior= (Automaton.get_prior aut) in 
	 if Transition.is_empty prior then
	   Gamma.get_norm_rules gamma_content
	 else   (* if there are some prior transitions we add them to norm_rules *)
	   let (translate_prior: Gamma.norm_rule)= Gamma.new_norm_rule pat_prior prior in
	     translate_prior::(Gamma.get_norm_rules gamma_content))
      @  (* if static completion is forced we append a drastic approximation rule [x -> y] -> [z -> qnew0] 
	    to the set of normalization rules *) 
      (if not forced then [] else [(Gamma.new_norm_rule pat_prior (TRS.list_to_trs [force_rule]))])
    in      
    let (lhs_list, rhs_table)= Gamma.static_norm trs new_norm_rules in
    let _= Printf.fprintf !out_chan "%s" "\n\nDONE!\n\n" in
      { strs= trs; sg_content= gamma_content;
	slast= empty_automaton; 
	sepsilon= Automaton.modify_state_ops aut 
		    (Alphabet.union (Automaton.get_state_ops aut) 
		       (Gamma.get_new_states gamma_content)) ;  (* we add all state ops used by the approx *)
	static_rules= associate lhs_list rhs_table empty_automaton aut;
        new_state= 0;
	sstep= s}




  (* Cleaning of term automaton containing special terms in the left-hand side of product states. 
     Those automaton are used to achieve pattern matching with patterns containing symbol, variables 
     AND states *)

  let special_clean (a: automaton): automaton=
    let rec clean_products (ls: state list): state list=
      match ls with 
	  [] -> []
	| Fsym(f,[q1;q2])::rem -> 
	    if (is_generated_state q1) or (is_var_state (Fsym(f,[q1;q2])))
	    then (Fsym(f, [q1;q2]))::(clean_products rem)
	    else 
	      if q1=(Special(q2))
	      then (clean_products rem)
	      else raise Bad_product

	| _ -> failwith ("Completion: special_clean: non valid product state")
	    
    in
    let clean_trans (t: transition): transition=
      Automaton.new_trans (Automaton.top_symbol t) 
	(clean_products (Automaton.list_state t))
	(Automaton.rhs t)
    in
    let rec clean_list (l: transition list) (res: transition list): transition list=
      match l with
	  [] -> res
	| t::rem -> 
	    try (let new_t= clean_trans t in (clean_list rem (new_t::res)))
	    with Bad_product -> (clean_list rem res)
    in
    let new_trans= TRS.list_to_trs (clean_list (TRS.to_list (Automaton.get_transitions a)) []) in
    let new_states= Common.clean (list_states_of_transitions new_trans) in
      Automaton.make_automaton
	(Automaton.get_alphabet a)
	(Automaton.get_state_ops  a)
	(State_set.list_to_set new_states)
	(Automaton.get_final_states a)
	(TRS.empty)
	new_trans

		
  (* suppressing empty epsilon transitions and double occurrences of transitions in a trs
     coming from state-merging *) 
		
  let suppress_empty_trans a=
    let rec aux trans= 
      if Transition.is_empty trans then trans
      else 
	let t= Transition.first trans and lrem= Transition.remainder trans in
	let remainder= aux lrem in
	  if (Term.equal (Transition.lhs t) (Transition.rhs t)) then remainder
	  else Transition.add t remainder
    in Automaton.make_automaton (Automaton.get_alphabet a) (Automaton.get_state_ops a) (Automaton.get_states a) 
	 (Automaton.get_final_states a) (aux (Automaton.get_prior a)) (aux (Automaton.get_transitions a))
	 

    
  (* Build merging rules between some states (special ones!) from equations and an automaton *)

  (* give recognizing states for a term partially instanciated with states and an automaton *)

  let search_solutions (t: term) (a: alphabet) (aut: automaton): state list=
    let rec get_states_with_substs (s: labelled_substitution): state list=
      match s with 
	  [] -> []
	| (Fsym(_,[_;q1]), sub)::rem -> 
	    if sub=[] then get_states_with_substs rem
	    else q1::(get_states_with_substs rem)
	| _ -> failwith "Bad solution structure for right hand side"
    in
    let aut_t= translate_one_term_into_automaton t 0 a in
    let inter_t_aut= intersection aut_t aut in
    let cleant_inter= special_clean inter_t_aut in
    let solutions= new_subst empty_automaton cleant_inter in
      get_states_with_substs solutions

  let merge_from_one_equation (eq: Gamma.equation) (a: alphabet) (aut: automaton): transition list=
    let lhs= (Gamma.eq_lhs eq) in
    let aut_lhs= translate_one_term_into_automaton lhs 0 a in
    let inter_lhs_aut= intersection aut_lhs aut in
    let cleant_inter= special_clean inter_lhs_aut in
    let solutions= new_subst empty_automaton cleant_inter in
    let rhs= Gamma.eq_rhs eq in 
      if Term.is_variable rhs 
      then
	let varl= Term.list_variables lhs in
	let varr= Term.list_variables rhs in
	  if Common.subeq_list varr varl 
	  then (* this is an equation of the form C[x]=x *)
	    let assoc_rhs=
	      List.map (function (q,ls) -> 
			  (q, (List.map (function s -> (Term.apply s rhs)) ls))) solutions in
	      List.flatten (List.map (function (q, lq) -> 
					match q with Fsym(_,[_;q1]) -> (List.map (function q2 -> TRS.new_rule q1 (Automaton.state_label q2)) lq)
					  | _-> failwith "Bad solution structure for left hand side") assoc_rhs)
	  else (* equation of the form C[x1,...xn]=y , where y can be replaced by any state! 
		  For every state q where we found an occurence of the lhs we add a rule q' -> q for every state q'
		  of the automaton *)
	    let all_states= State_set.to_list (Automaton.get_states aut) in
	      List.flatten 
		(List.map (function (q,ls) ->
			     match q with Fsym(_,[_;q1]) -> 
			       (List.map (function q2 -> TRS.new_rule q2 q1) all_states)
			       | _-> failwith "Bad solution structure for left hand side") solutions)

      else (* equation of the form s=t where s and t are not variables *)
	let assoc_rhs=
	  List.map (function (q,ls) -> 
		      (q,(List.flatten (List.map (function s -> search_solutions (Term.apply s rhs) a aut) ls)))) solutions in
	  List.flatten (List.map (function (q, lq) -> 
				    match q with Fsym(_,[_;q1]) -> (List.map (function q2 -> TRS.new_rule q1 q2) lq)
				      | _-> failwith "Bad solution structure for left hand side") assoc_rhs)

  
  (* Build merging epsilon transitions for a given equation list and an automaton *)
  let rec merge_from_equations (eq: Gamma.equation list) (a: alphabet) (aut: automaton): transition list=
    match eq with
	[] -> []
      | e1::rem -> List.append (merge_from_one_equation e1 a aut) (merge_from_equations rem a aut)
    

  (* State merging using the approximation equations *) 

  let final_state_merge (cs: dynamic_completion_state): dynamic_completion_state=
    let equations= Gamma.get_equations (cs.g_content) in
      if equations =[]
      then cs
      else 
	begin
	  let merging_rules= (Automaton.simplify_equivalence_classes (merge_from_equations equations (get_alphabet (Dyn cs)) (get_automaton_from_completion_step (Dyn cs)))) in
	  let trs_from_transitions= TRS.list_to_trs merging_rules in
	    if TRS.is_empty trs_from_transitions 
	    then cs
	    else 
	      let _= Printf.fprintf !out_chan "%s" 
		       ("State merging using approximation equations!\n\n"^
			(TRS.to_string trs_from_transitions)^"\n\n"); flush !out_chan in
		
	      let (new_automaton:Automaton.t)= suppress_empty_trans 
						 ((Automaton.rewrite_state_labels 
						     (get_automaton_from_completion_step (Dyn cs)) trs_from_transitions):Automaton.t) in
		make_dynamic_completion_state cs.trs new_automaton (Gamma.set_prior_in_gamma (Automaton.get_prior new_automaton) cs.g_content) cs.index cs.step
	end


  (* after one step of completion, we take into account each new information and...
     a_lhs etc... *)


  let dyn_modif_after_one_step (cs: dynamic_completion_state) new_trans new_gamma_content (new_state_ops: alphabet) new_i=
    let tmp= Automaton.modify_state_ops (Automaton.make_fast_union cs.last cs.epsilon) new_state_ops in
    let old_trans= Automaton.get_transitions tmp in
    let new_trans_not_covered= 
      (Transition.list_to_trs (Common.my_find_all (function x -> not(Transition.mem x old_trans))
				 (Transition.to_list new_trans))) in

      
    let new_last= Automaton.modify_states tmp 
		    (State_set.union (Automaton.states_of_transitions new_trans_not_covered) (Automaton.get_states tmp)) in
    let new_epsilon= Automaton.modify_transitions new_last new_trans_not_covered in
    let new_cs=
      {trs= cs.trs;last= new_last; epsilon= new_epsilon;
       alhs= cs.alhs; 
       alhs_x_last= Automaton.make_fast_union cs.alhs_x_last cs.alhs_x_epsilon;
       alhs_x_epsilon= intersection cs.alhs new_epsilon;
       
       index= new_i; g_content= new_gamma_content; step= cs.step + 1} in
      final_state_merge new_cs


  (* In the static case, it is nearly the same but gamma_content is not modified (maybe to be implemented?) *)

  (* The static matching is globally updated for every rule by [update_static_matching] and for every set of  
     linked variables of  every rule by[update_linked_vars_matching] *)

  (*
    let rec update_linked_vars_matching (new_inter_epsilon: automaton) (lvl: ((variable list) * linked_var_match) list): ((variable list) * linked_var_match) list=
    match lvl with
    [] -> []
    | (lvar, data)::rem ->
    let (new_inter_epsilon, new_delstates)= simplify new_inter_epsilon lvar data.delstate in
    (lvar, {linked_inter_last= Automaton.make_fast_union data.linked_inter_last data.linked_inter_epsilon;
    linked_inter_epsilon= new_inter_epsilon;
    delstate= new_delstates})::(update_linked_vars_matching new_inter_epsilon rem)
    
    
  (* update the intersection between the left-hand side of the rule and the automaton, given 
    the new transitions *)

  *)

  let rec update_static_matching (new_epsilon: automaton) (lsr1: static_rule list): (static_rule list) =
    match lsr1 with
	[] -> []
      | sr::rem -> 
	  let new_inter_epsilon= (intersection sr.salhs new_epsilon) in
	  let complete_inter_epsilon= 
	    Automaton.modify_transitions new_inter_epsilon 
	      (Transition.list_to_trs (clean_unsat_trans 
					 (Transition.to_list (Automaton.get_transitions new_inter_epsilon))
					 (sr.rhsdat).Gamma.const)) in
	    
	    {salhs= sr.salhs;
	     inter_last= Automaton.make_fast_union sr.inter_last sr.inter_epsilon;
	     inter_epsilon= complete_inter_epsilon;
	     non_lin_vars= sr.non_lin_vars;
	     last_dep_tree= sr.last_dep_tree;
	     rhsdat= sr.rhsdat}::(update_static_matching new_epsilon rem)
	    
	    
  let static_modif_after_one_step (cs: static_completion_state) new_trans 
    (modified_static_rules: static_rule list) (new_i: int)= 
    let tmp= Automaton.make_fast_union cs.slast cs.sepsilon in
    let old_trans= Automaton.get_transitions tmp in
    let new_trans_not_covered= 
      (Transition.list_to_trs (Common.my_find_all (function x -> not(Transition.mem x old_trans))
				 (Transition.to_list new_trans))) in
      
    let new_last= Automaton.modify_states tmp 
		    (State_set.union (Automaton.states_of_transitions new_trans_not_covered) (Automaton.get_states tmp)) in
    let new_epsilon= Automaton.modify_transitions new_last new_trans_not_covered in
      { strs= cs.strs;
	sg_content= cs.sg_content;
	slast= new_last; 
	sepsilon= new_epsilon;
	static_rules= update_static_matching new_epsilon modified_static_rules;
	new_state= new_i; sstep= cs.sstep + 1}


  (* the lexer for adding rules interactively *)	

  let lexer = Genlex.make_lexer [",";"(";")";"->";".";"=";"[";"]";"States";"Top";"Rules"]



  (* parsing of user equations *)

  let rec parse_equation_rules (csd: dynamic_completion_state) (variables: Term.variable_set): dynamic_completion_state= 

    let a= get_alphabet (Dyn csd) in 
    let _= Printf.fprintf !out_chan "%s" ("Current equations are: \n"^(Gamma.equations_to_string (Gamma.get_equations csd.g_content))^"\n\nAlphabet="^(Alphabet.to_string a)^"\nand Variables= "^(Variable_set.to_string variables)^"\n\nType additionnal equations and end by a dot '.': \n"); flush !out_chan in
    let equations_aux alphabet =
      parser
	  [< eq= Gamma.parse_equations alphabet variables ;
	     'Genlex.Kwd "." >] -> eq
    in 
      try (let eq= (equations_aux a (lexer (Stream.of_channel !in_chan))) in
	     {trs= csd.trs; last= csd.last; epsilon=csd.epsilon; alhs= csd.alhs; alhs_x_last= csd.alhs_x_last;
	      alhs_x_epsilon= csd.alhs_x_epsilon; index=csd.index; 
	      g_content= Gamma.set_equations  (Common.clean (List.append eq (Gamma.get_equations csd.g_content)))
			   csd.g_content; step= csd.step}) 
      with 
	| Stream.Error s -> 
	    begin
	      Printf.fprintf !out_chan "%s" ("\n\nSyntax error, try again\n"^s); 
	      flush !out_chan;
	      parse_equation_rules csd variables
	    end
	| Term.Undefined_symbol(f) -> 
	    begin Printf.fprintf !out_chan "%s" ("\n\nError: Symbol "^f^" is undefined, try again\n"); 
	      flush !out_chan;
	      parse_equation_rules csd variables
	    end
	| Term.Badly_formed_term(f) -> 
	    begin
	      Printf.fprintf !out_chan "%s" ("\n\nError: Bad term syntax! "^f^", try again\n"); 
	      flush !out_chan;
	      parse_equation_rules csd variables
	    end
	| _  ->  
	    begin
	      Printf.fprintf !out_chan "%s" ("\n\nSyntax error, try again\n"); 
	      flush !out_chan;
	      parse_equation_rules csd variables
	    end

 


  (* parsing of user additionnal norm rules *)

  let rec parse_norm_aux alpha state_ops variable_set= 
    parser 

      | [< 'Genlex.Kwd "States"; add_state_ops= State_set.parse_ops;
	   (top, bot, sops)= parse_norm_aux alpha (Alphabet.union state_ops add_state_ops) variable_set >] -> 
	  (top, bot, (Alphabet.union sops add_state_ops))
      | [< 'Genlex.Kwd "Rules"; (top,bot,ops)= parse_norm_rules_aux alpha state_ops variable_set >] ->
	  (top, bot, ops)
      | [<'Genlex.Kwd "." >] -> ([], [], Alphabet.new_alphabet)
      | [< >] -> raise (Stream.Error "Keyword 'States' or 'Rules' expected!\n")

  and parse_norm_rules_aux alpha state_ops variable_set= 
    parser
	[< 'Genlex.Kwd "Top"; rule= Gamma.parse_one_rule alpha state_ops variable_set; (top, bot, sops)= 
	     parse_norm_rules_aux alpha state_ops variable_set>] ->  (rule::top, bot, sops)	
      | [< rule= Gamma.parse_one_rule alpha state_ops variable_set; (top, bot, sops)= 
	     parse_norm_rules_aux alpha state_ops variable_set >] ->  (top, rule::bot, sops)
      | [<'Genlex.Kwd "." >] -> ([], [], Alphabet.new_alphabet)



  let rec parse_norm_rules (csd: dynamic_completion_state) (variables: Term.variable_set): dynamic_completion_state= 

    let a= get_alphabet (Dyn csd) in 
    let current_state_ops= Alphabet.union 
			     (Gamma.get_new_states csd.g_content) 
			     (Automaton.get_state_ops (get_automaton_from_completion_step (Dyn csd))) in
      

    let _= Printf.fprintf !out_chan "%s" ("Current normalisation rules are: \n"^(Gamma.norm_rules_to_string (Gamma.get_norm_rules csd.g_content))^"\n\nAlphabet="^(Alphabet.to_string a)^"\nand Variables= "^(Variable_set.to_string variables)^"\nand States= "^(Alphabet.to_string current_state_ops)^"\n\nType additionnal normalization rules using the 'States' and 'Rules' keyword and end by a dot '.': \n\n(use keyword 'Top' to place a rule at the beginning of the rule list)\n\n"); flush !out_chan in 
      
      try (let (top, bot, sops)= parse_norm_aux a current_state_ops variables 
				   (lexer (Stream.of_channel !in_chan)) in
	     {trs= csd.trs; last= csd.last; epsilon=csd.epsilon; alhs= csd.alhs; alhs_x_last= csd.alhs_x_last;
	      alhs_x_epsilon= csd.alhs_x_epsilon; index=csd.index; 
	      g_content= Gamma.set_new_states (Alphabet.union (Gamma.get_new_states csd.g_content) sops)
			   (Gamma.set_norm_rules 
			      ((List.rev top)@(Gamma.get_norm_rules csd.g_content)@bot) csd.g_content);
	      step= csd.step})
      with 
	| Stream.Error s -> 
	    begin
	      Printf.fprintf !out_chan "%s" ("\n\nSyntax error, try again\n"^s); 
	      flush !out_chan;
	      parse_norm_rules csd variables
	    end
	| Term.Undefined_symbol(f) -> 
	    begin Printf.fprintf !out_chan "%s" ("\n\nError: Symbol "^f^" is undefined, try again\n"); 
	      flush !out_chan;
	      parse_norm_rules csd variables
	    end
	| Term.Badly_formed_term(f) -> 
	    begin
	      Printf.fprintf !out_chan "%s" ("\n\nError: Bad term syntax! "^f^", try again\n"); 
	      flush !out_chan;
	      parse_norm_rules csd variables
	    end
	| TRS.Badly_formed_rule(f) -> 
	    begin
	      Printf.fprintf !out_chan "%s" ("\n\nError: Bad rule syntax! "^f^", try again \n");
	      flush !out_chan;
	      parse_norm_rules csd variables
	    end
	| _ -> 
	    begin
	      Printf.fprintf !out_chan "%s" "Syntax error, try again!\n"; 
	      flush !out_chan;
	      parse_norm_rules csd variables
	    end

      
      
  (* parsing of merging rules *)
      
  let rec parse_merging_rules alphabet state_ops (s:string)=
    let merging_rules_aux alphabet state_ops=
      parser
	  [< trs= Transition.parse_ground_special alphabet state_ops ;
	     'Genlex.Kwd "." >] -> trs 
    in 
      
    let rules= 
      if s="" then
	try (merging_rules_aux alphabet state_ops (lexer (Stream.of_channel !in_chan)))
	with _ -> 
	  begin
	    Printf.fprintf !out_chan "%s" "Syntax error, try again:\n"; 
	    flush !out_chan;
	    parse_merging_rules alphabet state_ops s
	  end
      else 
	merging_rules_aux alphabet state_ops (lexer (Stream.of_string s))
	  
    in if (List.for_all (function t-> (Automaton.is_state_config (Transition.lhs t)) &&
			   (Automaton.is_state_config (Transition.rhs t))) (Transition.to_list rules))
      then 
	rules 
      else 
	begin
	  Printf.fprintf !out_chan "%s" "Be careful, one of the rules is not of the form q1 -> q2 where q1 and q2 are states\nTry again:\n"; 
	  flush !out_chan;
	  parse_merging_rules alphabet state_ops s
	end
	
	
  (* state merging: merging together some states and renaming state label by another. *)
	
  let merge_state (cs: completion_state) (s:string) =
    begin
      if s="" then 
	begin
	  Printf.fprintf !out_chan "%s" "Give a sequence of rewrite rules on state labels ended by a dot: '.'\n\n";
	  flush !out_chan
	end;
      let transitions= parse_merging_rules (get_alphabet cs) (get_state_ops cs) s in
      let _= Printf.fprintf !out_chan "%s" ("Merging using rules:\n"^(Transition.to_string transitions)^"\n\n");
	flush !out_chan in
      let trs_from_transitions= 
	TRS.list_to_trs
	  (Common.my_map 
	     (function t-> 
		TRS.new_rule (Automaton.state_label (Transition.lhs t))
		  (Automaton.state_label (Transition.rhs t))) (Automaton.simplify_equivalence_classes (Transition.to_list transitions))) in
      let (new_automaton:Automaton.t)= suppress_empty_trans 
					 ((Automaton.rewrite_state_labels 
					     (get_automaton_from_completion_step cs) trs_from_transitions):Automaton.t) in
	match cs with
	    Dyn(csd) -> Dyn(make_dynamic_completion_state csd.trs new_automaton (Gamma.set_prior_in_gamma Transition.empty csd.g_content) csd.index csd.step)
	  | Static(css) -> Static(make_static_completion_state css.strs new_automaton css.sg_content css.sstep !is_forced)

    end


	
  (* determinisation of current automaton *)
	
  let determinise (cs: completion_state)=
    begin
      Printf.fprintf !out_chan "%s" "\nDeterminisation... ";
      flush !out_chan;
      let (new_automaton:Automaton.t)= Automaton.determinise (get_automaton_from_completion_step cs) in
      let _= Printf.fprintf !out_chan "%s" " done\n\n"; flush !out_chan in
	match cs with
	    Dyn(csd) -> Dyn(make_dynamic_completion_state csd.trs new_automaton (Gamma.set_prior_in_gamma Transition.empty csd.g_content) csd.index csd.step)
	  | Static(css) -> Static(make_static_completion_state css.strs new_automaton css.sg_content css.sstep !is_forced)
    end


  (* Epures a list of transition with regards to a bifolder of transitions. 
     Transitions to be retrieved are of the form:
     
     q -> q, 
     q1 -> q2, if all transitions of q1 are already (syntactically) in q2

     (transitions of the form c->q such that we already have c->A*q are normally not produced
     by this matching algorithm...
  *)
    
  let rec epure new_trans (delta: transition_table)=
    match new_trans with
	[] -> []
      | t::lrem -> 
	  let lh= Transition.lhs t in
	  let rh= Transition.rhs t in
	  let remainder= epure lrem delta in
	    if Automaton.is_state_config lh then
	      if (Term.equal lh rh) || (Automaton.is_covered lh rh delta)
	      then remainder
	      else t::remainder
	    else 	
	      (* This is checked in the gamma module *)
	      (* If no useless solution is produced there is no need to check this 
		 if Automaton.is_recognized_into lh rh delta then remainder 
		 else *)
	      t::remainder
		


  (* the rule number [i] corresponding to symbol [rule_i] *)
		
  let rule_number (r: symbol): int= 
    let s= (Symbol.to_string r) in
    let len= (String.length Gamma.variable_top_state_string) in
      int_of_string (String.sub s len ((String.length s)- len))
	
	
  (* produces a transition table containing all the new transitions coming from
     substitutions [solutions] found with matching *)

  let rec produce_new_transitions (trs: TRS.t)(solutions: labelled_substitution):transition_table=
    match solutions with
	[] -> Transition.empty
      | (Fsym(_, [Fsym(r,_);q]), subst_list)::rem -> 
	  let rhs= TRS.rhs (TRS.nth trs ((rule_number r)-1)) in
	  let state_q= Automaton.make_state_config q in
	  let new_transitions= 
	    Common.my_map (function sub -> Transition.new_rule (Term.apply sub rhs) state_q) subst_list
	  in
	    Transition.union (Transition.list_to_trs new_transitions) (produce_new_transitions trs rem)
      | _ -> failwith "Bad labelled substitution!!"


  let dyn_complet_one_step (cs: dynamic_completion_state) (init_state: state_set) =
    (* find the new solutions of matching *)
    let solutions= new_subst (cs.alhs_x_last) (cs.alhs_x_epsilon) in
      (* construct the related transitions and suppress useless ones *)
    let new_trans= Transition.list_to_trs (epure (Transition.to_list (produce_new_transitions (cs.trs) solutions)) (get_all_trans (Dyn cs))) in
      (* we apply the approximation gamma in order to normalize the transitions *)
    let all_trans= get_all_trans (Dyn cs) in
    let  (normalized_trans_with_gamma,
	  newgc, new_state_ops, new_i)=   Gamma.gamma new_trans
					    (Automaton.transitions_by_state_by_symbol 
					       (Transition.to_list all_trans))
					    (cs.g_content) (get_alphabet (Dyn cs))
					    (get_state_ops (Dyn cs)) (cs.index) 
					    (* init_state *) (* for auto_prior to be exact *)
					    (Automaton.states_of_transitions all_trans)
    in 
      dyn_modif_after_one_step cs normalized_trans_with_gamma newgc new_state_ops new_i 

  (* -------- the completion in static mode ------- *)
	

  (* Splitting nodes of the graph between var and non-var states *)

  let rec dep_tree_split (g: dep_tree) (g1: dep_tree) (g2: dep_tree): (dep_tree * dep_tree)=
    match g with 
	[] -> (g1, g2)
      | (s1, l)::rem -> 
	  (match s1 with 
	       Fsym(_, [Fsym(_,[Var(_)]);_]) -> (* it is a variable *)
		 dep_tree_split rem ((s1, l)::g1) g2
	     | _ -> dep_tree_split rem g1 ((s1, l)::g2))
	  
	  
  (* Find every new partial substitution for a given static rule *)
	  
  let rec dep_tree_one_path (nlist: state list) (tree: dep_tree) (ldone: state list): (state list)=
    match nlist with 
	[] -> ldone
      | (s::rem) ->
	  (* In our setting final states are states where the first component is a variable state! *)
	  if 
	    (match s with 
		 Fsym(_, [Fsym(_, [Var(_)]);_]) -> true
	       | _ -> false)
	  then dep_tree_one_path rem tree (s::ldone)
	  else 
	    let lsucc= try (List.assoc s tree) with Not_found -> [] in
	      if lsucc=[] then dep_tree_one_path rem tree ldone
	      else dep_tree_one_path (lsucc@rem) tree ldone


  let rec dep_tree_pathes (new_subst: dep_tree) (remainder: dep_tree) (ldone: ((variable * state * substitution) list)): ((variable * state * substitution) list)=
    match new_subst with
	[] -> ldone
      | (Fsym(_, [Fsym(_, [Var(x)]); q]), lsucc)::rem ->
	  let related_final_states= dep_tree_one_path lsucc remainder [] in
	  let new_done= 
	    (* The symbol used to label the final state of the automaton for the lhs of the rule 
	       is converted into the variable labelling the final state of the rhs of the rule by
	       [(Variable.of_string (Symbol.to_string rule_state))]  *)

	    Common.my_map (function s -> 
			(match s with 
			     Fsym(_, [Fsym(_,[Var(y)]); aut_state]) -> 
			       (y, Special(aut_state), [(x, Special(q))])
			   | _ -> failwith "dep_tree_pathes: non variable states as final!"))
	      related_final_states in
	    dep_tree_pathes rem remainder (new_done@ldone)


      | _ -> failwith "dep_tree_pathes: dep_tree not valid, may be non var states"
	  
	  
  (* main function of new partial substitution construction for non linked variables: uses [dep_tree] *)

  let static_new_substs_non_linked (last: dep_tree) (epsilon: dep_tree): ((variable * state * substitution) list)= 
    
    (* We split new_subst_dep_tree between variable states (necessarily new) and the remainder (non var states) *)

    let (only_new_subst, remainder)= dep_tree_split epsilon [] [] in
      dep_tree_pathes only_new_subst (dep_tree_union remainder last) []

	

  (* main function of new partial substitution construction for linked variables: uses [linked_var_match] *)

  let rec static_new_substs_linked (lvm: linked_var_match list): ((variable * state * substitution) list)=
    match lvm with
	[] -> []
      | partial_match::rem -> 
	  
	  (* dynamic matching uses some hash tables that have to be set *)
	  
	  (Hashtbl.clear !hsh_left_all);    
	  hsh_left_all:= hashtable_modif !hsh_left_all (TRS.to_list (Automaton.get_transitions partial_match.linked_inter_last));
	  
	  let solutions= new_subst (Automaton.modify_transitions partial_match.linked_inter_last (TRS.empty))
			   (Automaton.make_fast_union partial_match.linked_inter_last 
			      partial_match.linked_inter_epsilon) in 


	  (* The dynamic matching algorithm [new_subst] gives a result of a slightly different type that the
	     one we use for static matching, so the result has to be reorganised *)
	    
	    
	  let casted_solutions= 
	    List.flatten (Common.my_map 
			    (function s -> match s with 
				 (Fsym(_, [Fsym(_, [Var(x)]); q]), lsub) -> 
				   Common.my_map (function one_sub -> (x, Special(q), one_sub)) lsub
			       | _ -> failwith "Static_new_substs_linked: Non valid intersection state!")
			    solutions)

	  in
	    List.append casted_solutions (static_new_substs_linked rem)
	      

  (* apply all found partial substitutions to a given [rhs_data] *)	

  let rec apply_all_subst (ls: (variable * state * substitution) list) (trl: transition_table) 
    (rhsd: Gamma.rhs_data): (transition_table * Gamma.rhs_data)=
    match ls with 
	[] -> (trl, rhsd)
      | (qvar, s2, subst)::rem ->
	  let (new_trans, new_rhsd)= Gamma.produce_new_transition qvar s2 subst rhsd in
	    apply_all_subst rem (Transition.union_fast trl new_trans) new_rhsd 
	      
	      
  (* The type of states constrained by a subst: used for non linearity renaming of Tree Automaton and
     then for smart cleaning, i.e. retrieve transitions corresponding to impossible non linear substitutions *)

  type temp_state= TS of state * substitution
    
  type temp_trans= TT of symbol * temp_state list * temp_state



  (* Adding a list of elements in a folder (see automaton module) for a selected criteria *)

  let add_aux criteria l folder=
    let rec add_aux_aux folder =
      match folder with
	  [] -> raise Automaton.Not_in_folder
	| (c, al)::rem when c=criteria -> 
	    (c, Common.union l al)::rem
	| any::rem -> any::(add_aux_aux rem)
    in try add_aux_aux folder with 
	Automaton.Not_in_folder -> (criteria, (Common.clean l))::folder

	    
  (* Add a new state (with its corresponding subst restricted to non linear variables) to every 
     [temp_trans] of a list of partial [temp_trans] *)

  let rec apply_all_aux (new_state: temp_state) (tl: temp_trans list)=
    let TS(st, subst)= new_state in 
    match tl with
	[] -> []
      | (TT(f, l, TS(rhs, s)))::rem ->
	  try (
	    let new_sub= coherent (s@subst) in
	      (TT(f, new_state::l, TS(rhs, new_sub)))::(apply_all_aux new_state rem)
	  )
	  with Term.Terms_do_not_match(_,_) -> apply_all_aux new_state rem 

	      
  (* produce every possible transitions, given a top symbol a list of states, a rhs state, a 
     substitution for *)

  let rec produce_aux (f: symbol) (sl: state list) (rhs: state) (s: substitution) 
    (done_states: (state * (temp_state list))list) (non_lin_var: variable list): temp_trans list=
    
    match sl with
	[] -> [TT (f, [], TS(rhs, s))]
      | state::rem ->
	  let rest= produce_aux f rem rhs s done_states non_lin_var in
	    match state with 
		Fsym(_, [Fsym (_,[Var(x)]);v]) -> 
		  if List.mem x non_lin_var then
		    apply_all_aux (TS(state,[(x,Special(v))])) rest
		  else 
		    apply_all_aux (TS(state,[])) rest
	      | _ -> 
		  try (let lnew= List.assoc state done_states in
			 (List.flatten (Common.my_map (function new_state -> (apply_all_aux new_state rest)) lnew))
		      )
		  with Not_found -> failwith ("Produce_aux: state "^(State_type.to_string state)^" not in list!")
	        

  (* Unfolding of transitions which contains non linear variables: transitions [f((x, q1),(y,q2)) -> q]
     and [f((x, q2), (y, q3)) -> q]  are renamed into  f( TS((x, q1),[(x,q1)]), TS((y,q2),[])) -> TS(q,[(x,q1)])
     and f( TS((x, q2),[(x,q2)]), TS((y,q3),[])) -> TS(q,[(x,q2)]) if y is a linear variable and x is not *)

  (* Thanks to the specific structure of matching automata, if a transition is considered on a 
     given pass, there is no use to consider it again.
     transitions of ltrans are supposed to be grouped by destination state. With this weak sorting of
     transition, when considering a state (q,q') in a transition of the form f(..., (q, q'), ...) -> ..., 
     if q is in the [done_states], we are sure that every possible cases have already been reviewed.
     (Note that in these transition lists no cycle in the transitions are permitted, because those
      transitions come from matching automata that do not contain cycles. *)

  let rec trans_unfolding (ltrans: transition list) (temp: transition list) (is_done: temp_trans list) 
    (done_states: (state * (temp_state list))list) (non_lin_vars: variable list) (touched: bool): temp_trans list=

   match ltrans with 
       [] -> 
	 if touched 
	 then trans_unfolding temp [] is_done done_states non_lin_vars false
	 else is_done
	   
     | t::rem -> 
	 try(
	 let f= Automaton.top_symbol t in
	 let rhs= Automaton.rhs t in
	 let lhs= Automaton.lhs t in
	   
	   (* we keep the substitution part that corresponds to non linear variables *)

	 let subst= List.filter (function (x, v) -> (List.mem x non_lin_vars)) 
		      (coherent (get_substitution_part lhs)) in
	 let lstates= Common.my_map
			(function s -> 
			   match s with 
			       Special(q) -> q 
			     | _ -> failwith "trans_unfolding: Non special state!") (get_non_substitution_part lhs) in
	   if List.for_all (function s -> (List.mem_assoc s done_states)) lstates
	   then 
	     (* If every state of the right-hand side has been already processed *)

	     (* we propagate the new states onto the unfolded transitions already seen *)
	     let new_temp_trans= produce_aux f (Automaton.list_state t) rhs subst done_states non_lin_vars in
	       trans_unfolding rem temp (new_temp_trans @ is_done) 
		 (add_aux rhs (Common.my_map (function tt -> match tt with TT(_,_,s) -> s) new_temp_trans) 
		    done_states) non_lin_vars true
	     
	   else 
	     (* otherwise the transition may be considered later *)
	     trans_unfolding rem (t::temp) is_done done_states non_lin_vars touched
	     
	 )
	   (* If the transition is of the form [f(..., (x, q1),..., (x, q2)) -> q] then it is thrown away *)
	 with Term.Terms_do_not_match(_,_) -> 
	   trans_unfolding rem temp is_done done_states non_lin_vars touched



  
  (* Renaming of [temp_trans] into standard transitions *)
	     
  let rec temp_trans_rename (ltrans: temp_trans list) (is_done: transition list)
    (renaming: (temp_state * state) list): transition list=
    let rec rename_aux (ls: temp_state list) (renaming: (temp_state * state) list)
      (is_done: state list): (state list * ((temp_state * state) list))=
      match ls with
	  [] -> (List.rev is_done, renaming)
	| (TS(Fsym(s1, [Fsym (s2,[Var(s)]);v]), sub))::rem  -> 
	    rename_aux rem renaming ((Fsym(s1, [Fsym (s2,[Var(s)]);v]))::is_done)
	| (TS(Fsym(s1, [q1;q2]), sub))::rem ->
	    let (new_state, new_renaming) = 
	      try ( (List.assoc (TS( (Fsym(s1, [q1;q2])), sub)) renaming),renaming)
	      with Not_found -> 
		let new_symb= make_new_state () in
		  
		  (* a [temp_state] of the form [prod(q1, q2)|| sub] is renamed by a specific state of the 
		     form [prod(q1, prod(q2, new))] where [new] is new for every different 
		     encountered [sub]. *)

		  (* It is not possible to renumber q1 because it could be a top variable state. It is not
		     possible to renumber q2 since we need to find back which transition it was initially *)

		  (Fsym(s1, [q1; Fsym(s1, [q2; new_symb])])), ((TS(Fsym(s1, [q1;q2]), sub), (Fsym(s1, [q1; Fsym(s1, [q2; new_symb])])))::renaming)
		    
	    in
	      rename_aux rem new_renaming (new_state::is_done)
	| _ -> failwith "rename_aux: non product state in a temp_state"
    in

    match ltrans with
	[] -> is_done
      | (TT(f, ls, fs))::rem ->
	  let new_final,new_ren1 = rename_aux [fs] renaming [] in
	  let new_args,new_ren2 = rename_aux ls new_ren1 [] in
	    temp_trans_rename rem ((Automaton.new_trans f new_args (List.hd new_final))::is_done) new_ren2
	  

  (* Recover initial transition from renamed transition *)

    let recover_state (s: state): state=
      match s with
	  Fsym(s1, [q1; Fsym(_, [q2; _])]) -> Fsym(s1, [q1; q2])
	| Fsym(_, [Fsym(_, [Var(_)]);_]) -> s
 
	| _ -> failwith "recover_state: state in non valid renamed form!"	      
	    
    let recover_trans (t: transition): transition=
      Automaton.new_trans (Automaton.top_symbol t) (Common.my_map recover_state (Automaton.list_state t)) (recover_state (Automaton.rhs t))
	

  (* Achieve a complete completion step with each static rule *)
    
  let rec static_complet_aux (lsr1: static_rule list) (found_trans: transition_table) 
    (new_lsr: static_rule list): 
    (transition_table * static_rule list)= 
    match lsr1 with
	[] -> (found_trans, new_lsr)
      | sr::rem -> 	
	  (* automaton built for simplifying invalid transition w.r.t non linear variables *)
	  let (cleant_last, cleant_epsilon)= static_clean sr.inter_last sr.inter_epsilon in 
	  let (cleant_last2, cleant_epsilon2)=
	    if (sr.non_lin_vars = [])
	    then 
	      cleant_last, cleant_epsilon
	    else
	      let trans_epsilon= Transition.to_list (Automaton.get_transitions cleant_epsilon) in
	      let trans_last= Transition.to_list (Automaton.get_transitions cleant_last) in
	      let all_trans= List.append trans_epsilon trans_last in
		
	      (* This is a state renaming process used for taking into account the non linearity
	         problems w.r.t. matching of non linear lhs of a rule on a tree automaton. Every state
	         concerned with a non linear variable is renamed w.r.t. possible substitutions captured
	         by the state (see trans_unfolding) *)

	      let exploded_trans= temp_trans_rename 
				    (trans_unfolding 

				       (* transitions need to be sorted by state before unfolding *)
				       (Automaton.folder_flatten (transition_by_state all_trans ))

(*				       all_trans *)

				       [] [] [] (sr.non_lin_vars) false) [] [] in

	      let (new_epsilon_trans, new_last_trans)=
		List.partition (function t -> (List.mem (recover_trans t) trans_epsilon)) exploded_trans in
	      let new_states= Automaton.states_of_transitions (Transition.list_to_trs exploded_trans) in
	      let new_final_states= State_set.list_to_set (List.filter is_final_state (State_set.to_list new_states)) in 
		static_clean 
		  (Automaton.make_automaton 
		     (Automaton.get_alphabet cleant_last)
		     (Automaton.get_state_ops cleant_last)
		     new_states new_final_states Transition.empty (Transition.list_to_trs new_last_trans))
		  (Automaton.make_automaton 
		     (Automaton.get_alphabet cleant_last)
		     (Automaton.get_state_ops cleant_last)
		     new_states new_final_states Transition.empty (Transition.list_to_trs new_epsilon_trans))
	  in
	  if TRS.is_empty (Automaton.get_transitions cleant_epsilon2) 
	  then
	    (* No new transition, nor substitution can be found *)
	    static_complet_aux rem found_trans
	      ({salhs= sr.salhs; inter_last= sr.inter_last; inter_epsilon= sr.inter_epsilon;
		non_lin_vars= sr.non_lin_vars;
		last_dep_tree= sr.last_dep_tree;
		rhsdat= sr.rhsdat}::new_lsr)
	  else
	  let complete_dep_tree= 
	    make_dep_tree (fst (simplify (Automaton.make_fast_union cleant_last2 cleant_epsilon2) 
				  (sr.rhsdat).Gamma.non_linked_vars [])) in

	  let epsilon_dep_tree= dep_tree_difference complete_dep_tree sr.last_dep_tree in
	  let new_substs1= static_new_substs_non_linked sr.last_dep_tree epsilon_dep_tree in

(* It is necessary to reconsider every path in the intersection automaton due to the fact that 
   some partial substitution may not be considered before because of some non-linearity cleaning in
   the intersection automaton 

   old_version:

	  let new_substs2= static_new_substs_linked (split cleant_last2 cleant_epsilon2 (sr.rhsdat).Gamma.linked_vars) *)

	  let new_substs2= static_new_substs_linked (split (Automaton.modify_transitions cleant_last2 (TRS.empty)) (Automaton.make_fast_union cleant_last2 cleant_epsilon2) (sr.rhsdat).Gamma.linked_vars)
	  in
	  let all_substs=
	    if (sr.rhsdat).Gamma.non_linked_vars=[] && (sr.rhsdat).Gamma.linked_vars=[]
	    then (* lhs is ground *) 
	      match (new_subst cleant_last2 cleant_epsilon2) with
		  [] -> []
		|[(Fsym(_, [Fsym(_, [Var(x)]); q]), [[]])] -> [(x, Special(q), [])]
		|_ -> failwith "Problem with matching with ground right-hand sides!"
	    else (List.append new_substs1 new_substs2) 
	  in

	    
	  let (new_trans, new_rhs_data2)= apply_all_subst all_substs
					    Transition.empty sr.rhsdat in

	    static_complet_aux rem (Transition.union new_trans found_trans) 
	      ({salhs= sr.salhs; inter_last= sr.inter_last; inter_epsilon= sr.inter_epsilon;
		non_lin_vars= sr.non_lin_vars;
		last_dep_tree= complete_dep_tree;
		rhsdat= new_rhs_data2}::new_lsr)


  let static_complet_one_step (cs: static_completion_state)= 
    (* find the new solutions of matching and apply them directly to the right rule *)

    let (new_trans, new_list_static_rules)= static_complet_aux cs.static_rules Transition.empty [] in
      
    let cleant_new_trans= Transition.list_to_trs (epure (Transition.to_list new_trans) 
						    (get_all_trans (Static cs))) in

    (* Nearly all transitions are already normalised but not transitions of the form [q -> q'] *)

    let  (normalized_trans_with_gamma,
	  newgc, new_state_ops, new_i)=  Gamma.gamma cleant_new_trans
					   (Automaton.transitions_by_state_by_symbol 
					      (Transition.to_list (get_all_trans (Static cs))))
					   (cs.sg_content) (get_alphabet (Static cs))
					   (get_state_ops (Static cs)) (cs.new_state) State_set.empty

    in static_modif_after_one_step cs normalized_trans_with_gamma new_list_static_rules new_i



(* For optimisation reasons we first compute a simple and fast intersection
   for trivially empty intersections (states having no common top symbols in their transitions)  *)

  let all_top_symbols (q: state) (delta: (state, (transition list)) folder): (symbol list)=
    try Common.my_map (fun t -> Automaton.top_symbol t) (Automaton.folder_assoc q delta)
    with Not_found -> []

  let is_trivially_empty_multiple_intersection (ltrans: (state, transition list) folder) (lstates: state list):
    bool=
    let rec common_symbols (lstates: state list): (symbol list)=
      match lstates with 
	  [] -> []
	| [q] -> all_top_symbols q ltrans
	| q::rem -> Common.inter (all_top_symbols q ltrans) (common_symbols rem)
    in
      (common_symbols lstates)=[]

    
  (* Given an automaton a and a list of states q1,..., qn, this function verifies if 
     the intersection automaton a1= a /\ (a with q1 as final state) is empty, if not
     it verifies if intersection a2= a1 /\(a1 with q2 as final state) is empty, etc...*)

  let rec is_empty_multiple_intersection a a_init lstates=
    match lstates with
	[] -> false
      | q::lrem -> 
	  let intersec= 
	    Automaton.simplify 
	      (Automaton.inter a 
		 (Automaton.modify_final a_init (State_set.list_to_set [q]))) in
	    if Automaton.is_empty intersec then true
	    else is_empty_multiple_intersection intersec a_init lrem
	      

  (* is there a list l of states in l2 such that l<= l1, i.e. is there an empty
     intersection of states l such that the language recognized by l1 should be smaller
     or equal and thus also empty *)

  let covered intersec linter= 
    List.exists (function l -> Common.subeq_list l intersec) linter

  let rec subsume intersec l_intersec=
    match l_intersec with
	[] -> intersec::l_intersec
      | existing_intersec::lrem ->
	  (* if intersec subsumes one existing_intersec then we replace it *)
	  if Common.subeq_list intersec existing_intersec 
	  then intersec::lrem
	  else existing_intersec::(subsume intersec lrem)

  (* similar functions but for non empty intersections 
     i.e. if a list of intersec is not empty, so is every sublist *)

  let covered_neg intersec linter= 
    List.exists (function l -> Common.subeq_list intersec l) linter

  let rec subsume_neg intersec l_intersec=
    match l_intersec with
	[] -> intersec::l_intersec
      | existing_intersec::lrem ->
	  (* if intersec subsumes one existing_intersec then we replace it *)
	  if Common.subeq_list existing_intersec intersec
	  then intersec::lrem
	  else existing_intersec::(subsume intersec lrem)

	    
  let is_disjoint (cs: completion_state) (linter: (state list) list) (empty_inter: (state list) list)
    (not_empty_inter: (state list) list)=
    let last, epsilon, g_content=
      match cs with 
	  Dyn(csd) -> csd.last, csd.epsilon, csd.g_content
	| Static(css) -> css.slast, css.sepsilon, css.sg_content
    in
    let atemp= Automaton.make_fast_union last epsilon in
    let trans_by_state= 
      Automaton.transitions_by_state (Transition.to_list (Automaton.get_transitions atemp)) 
    in

    (* we compute the cartesian product of the transitions of automaton atemp with itself 
       only once, and use it for every intersection *)

    let trans_by_symbol= 
      Automaton.transitions_by_symbol (Transition.to_list (Automaton.get_transitions atemp)) 
    in
    let cartesian_prod= Transition.list_to_trs (Automaton.folder_cartesian_product trans_by_symbol trans_by_symbol) 
    in
    let rec aux (linter : (state list) list) (empty_inter: (state list) list)  
      (not_empty_inter: (state list) list) (ok: bool)=
      match linter with
	  [] -> (ok, [])
	| one_inter::lrem ->
	    if covered one_inter empty_inter
	    then aux lrem empty_inter not_empty_inter ok
	    else 
	      if covered_neg one_inter not_empty_inter then
		  aux lrem empty_inter not_empty_inter false
	      else 
		begin
		  Printf.fprintf !out_chan "%s" ("Checking intersection: "^(String.concat " ^ " (Common.my_map State_type.to_string one_inter)^" ..."));
		  flush !out_chan;
		  
		  if is_trivially_empty_multiple_intersection trans_by_state one_inter
		  then 
		    begin
		      Printf.fprintf !out_chan "%s" " done.\n";
		      flush !out_chan;
		      aux lrem (subsume one_inter empty_inter) not_empty_inter ok
		    end
		  else
		    (* we proceed the two first intersection apart from the other for better
		       efficiency (cartesian product is computed only once) *)
		    let first_inter=
		      Automaton.simplify
			(Automaton.make_automaton 
			   (Automaton.get_alphabet atemp)
			   (Alphabet.add_symbol State_set.default_prod_symbol 2
			      (Automaton.get_state_ops atemp))
			   (* states *)
			   (State_set.symbolic_product
			      (Automaton.get_states atemp)
			      (Automaton.get_states atemp))
			   (* final states *)
			   (State_set.symbolic_product 
			      (State_set.list_to_set [List.hd one_inter])
			      (State_set.list_to_set [List.hd (List.tl one_inter)]))
			   (Transition.empty)
			   cartesian_prod)
		    in
		      if Automaton.is_empty first_inter 
		      then 
			begin
			  Printf.fprintf !out_chan "%s" " done.\n";
			  flush !out_chan;
			  aux lrem (subsume one_inter empty_inter) not_empty_inter ok
			end
		      else 
			if List.length one_inter <= 2 
			then 
			  begin
			    Printf.fprintf !out_chan "%s" " Linearity problem!!!\n";
			    flush !out_chan;
			    aux lrem empty_inter (subsume_neg one_inter not_empty_inter) false
			end
		      else 
			(* there are other states to consider for intersection (3rd to nth) *)
			if (is_empty_multiple_intersection first_inter atemp (List.tl (List.tl one_inter)))
			then 
			  begin
			    Printf.fprintf !out_chan "%s" " done.\n";
			    flush !out_chan;
			    aux lrem (subsume one_inter empty_inter) not_empty_inter ok
			  end
			else
			  begin
			    Printf.fprintf !out_chan "%s" " Linearity problem!!!\n";
			    flush !out_chan;
			    aux lrem empty_inter (subsume_neg one_inter not_empty_inter) false
			  end
		end
    in
      aux linter empty_inter not_empty_inter true

  let rec subst_to_const (s: substitution) (iocc:  (variable * variable) list) 
    (sol_occ: (variable * (state list)) list):  (state list) list=
    let rec aux (l: (variable * (state list)) list):  (state list) list=
      match l with
	  [] -> []
	| (v, sl)::rem ->
	    let clean= Common.clean sl in
	      if List.length clean >= 2 then clean::(aux rem)
	      else aux rem
    in
      match s with 
	  [] -> aux sol_occ
	| (x, Special(q))::rem -> 
	    (try (let real_var= List.assoc x iocc in
		   subst_to_const rem iocc ((real_var, (q::(List.assoc real_var sol_occ)))::(List.remove_assoc real_var sol_occ)))
	     with Not_found -> subst_to_const rem iocc sol_occ)
	| _ -> failwith "Completion: subst_to_const: non valid state substitution!"



  let rec extract (sol: (state * (substitution list)) list) (iocc: (variable * variable) list)
    (sol_occ: (variable * (state list)) list)(res:(state list) list): (state list) list=
    match sol with
	[] -> res
      | (_, sub_list)::rem -> 
	  extract rem iocc sol_occ (Common.flat_map (function s -> (subst_to_const s iocc sol_occ)) sub_list)

  let fast_disj_constraint (t: term)(a: alphabet)(occ: (variable * (variable list)) list)
    (aut: automaton): ((state list) list)=    

    let aut_for_t= translate_one_term_into_automaton t 0 a in
    let inter_pattern_aut= intersection aut_for_t aut in
    let cleant_inter= special_clean inter_pattern_aut in
    let solutions= new_subst empty_automaton cleant_inter in
    let inverse_occ= Common.flat_map (function (x,l) -> (List.map (function y -> (y, x)) l)) occ in
    let sol_occ= Common.my_map (function (x, l) -> (x, [])) occ in
      extract solutions inverse_occ sol_occ []



  let check_linearity (cs: completion_state)=
    match cs with
	Dyn(csd) ->
	  let non_lin_lhs= TRS.non_linear_lhs csd.trs in
	    if non_lin_lhs= [] then (true, [])
	    else 
	      let renamed_lhs= List.map Term.linearize non_lin_lhs in
	      let aut= (get_automaton_from_completion_step (Dyn(csd))) in
	      let alphabet= (get_alphabet (Dyn(csd))) in
	      let disj_constraint= 
		Common.flat_map 
		  (function (t, occ) -> fast_disj_constraint t alphabet occ aut) renamed_lhs in

	      let _= Printf.fprintf !out_chan "%s" 
		       ("Intersections to be checked: \n"^
			(String.concat "\n" (Common.my_map (function l -> 
							      (String.concat " ^ " (Common.my_map State_type.to_string l))) disj_constraint))^"\n\n") in
						
		is_disjoint (Dyn(csd)) disj_constraint [] []
      | Static(css) -> 

	  (* Different states matching a non linear variable are gathered during completion but 
	     because of static normalisation, some of them may escape. This is solved by the following 
	     additional check:
	     
	     If a non linear variable is matched by a [norm_rule] then it is necessary
	     to look for other states that could have matched this non linear variable. 
	     For instance: f(x,x) -> g(g(x))  with [x -> y] -> [g(qa) -> qnew] then
	     if a transition g((x, qb)) -> qnew || x=qa  is in the static rule then [clean_unsat_trans] 
	     will retrieve it but it is necessary to add [qa =/= qb] to [locally_deterministic_states] *)
	  
	  let _= global_norm_rules_non_lin css in
	  
	  let disj_constraint=
	    (Common.clean (List.flatten (Common.my_map (function (x, l) -> Common.my_map (function z -> [x;z]) l) !locally_deterministic_states))) in
	  let _= Printf.fprintf !out_chan "%s" 
		   ("Intersections to be checked: \n"^
		    (String.concat "\n" (Common.my_map (function l -> 
							  (String.concat " ^ " (Common.my_map State_type.to_string l))) disj_constraint))^"\n\n") in
	    is_disjoint (Static(css)) disj_constraint [] []

	  
  (* prints the result of intersection between current completed automaton and a list of automata given
     with their names *)

  let rec verif_inter aut_comp laut=
    match laut with
	[] -> ()
      | (name, a)::lrem -> 
	  let intersec= Automaton.simplify (Automaton.inter aut_comp a) in
	  let interstring= Automaton.to_string intersec in
	    begin
	      Printf.fprintf !out_chan "%s" ("\nIntersection with "^name^" gives"^
					     (if Automaton.is_empty intersec then " (the empty automaton)" else " (not empty)")^":\n\n"^interstring^"\n\nPress Enter to continue.");
	      flush !out_chan;
	      let _= input_line !in_chan in ();
		verif_inter aut_comp lrem
	    end
	    

  (* user interaction capture for completion *)

  let rec answer()= 
    (Printf.fprintf !out_chan "%s" "(c/a/m/s/b/d/i/o/p/v/w/f/e/g/det/u/q)? ";
     flush !out_chan;
     let rep= input_line !in_chan in
       match rep with
	   "c"|"C"|"complete" -> 'c'
	 | "a"|"A"|"auto" -> 'a'
	 | "b"|"B"|"browse" -> 'b'
	 | "m"|"M"|"merge" -> 'm'
	 | "s"|"S"|"see" -> 's'
	 | "d"|"D"|"display" -> 'd'
	 | "i"|"I"|"inter" -> 'i'
	 | "v"|"V"|"verify" -> 'v'
	 | "f"|"F"|"forget" -> 'f'
	 | "u"|"U"|"undo" -> 'u'
	 | "q"|"Q"|"quit" -> 'q'
	 | "w"|"W"|"write" -> 'w'
	 | "o"|"O"|"other" -> 'o'
	 | "p"|"P"|"pattern" -> 'p'
	 | "e"|"equation" -> 'e'
	 | "g"|"gamma" -> 'g'
	 | "det" | "determinise" -> 't'
	 | _ -> 
	     (Printf.fprintf !out_chan "%s" "Answer by ";
	      flush !out_chan;
	      answer()))

  (* user interaction capture for interruption handling *)

  let rec answer_interrupt()= 
    (Printf.fprintf !out_chan "%s" "(c/f/s/q)? ";
     flush !out_chan;
     let rep= input_line !in_chan in
       match rep with
	   "c"|"C"|"continue" -> 'c'
	 | "f"|"F"|"finish" -> 'f'
	 | "s"|"S"|"see" -> 's'
	 | "q"|"Q"|"quit" -> 'q'

	 | _ -> 
	     (Printf.fprintf !out_chan "%s" "Answer by ";
	      flush !out_chan;
	      answer_interrupt()))
    (* Completion behaviour in case of user interruption (Ctrl-C).
       If Ctrl-C is hit, the current completion step is paused and the user
       is asked whether he wants 
       - to see current completed automaton (the one on which critical
       pairs are computed)
       - continue the current completion step
       - finish the current completion step and return to the menu
       - interrupt the current completion step NOW (thus loose current computation) and
       go back to the menu *)

  let rec interruption_handler (i:int)=
    begin
      Printf.fprintf !out_chan "%s" "\nDo you want to:\n\n(c)ontinue the completion\n(s)ee the current automaton (on which critical pairs are computed)\n(f)inish the current completion step and then go back to the menu\n(q)uit the completion step NOW (thus loose current computation) and go back to the menu\n\n";
      
      match answer_interrupt() with
	  'c' -> ()
	| 's' ->  
	    begin
	      Printf.fprintf !out_chan "%s"
		(Automaton.to_string !current_automaton);
	      flush !out_chan;
	      interruption_handler i
	    end
	| 'f' ->
	    user_interrupt:= true
	| 'q' -> raise Sys.Break
	| _ -> raise Sys.Break
    end


  (* reading a file name *)

  let rec file_name()= 
    (Printf.fprintf !out_chan "%s" "Give a file name (give an empty file name to cancel): ";
     flush !out_chan;
     let rep= input_line !in_chan in
       if rep="" then (false, "") else (true, rep))


  (* reading a term *)

  let rec term_read (a: alphabet) (aspecial: alphabet) (vars: Variable_set.t): term=
    try (let t= Term.check_special a aspecial (Term.parse_special a aspecial vars (lexer (Stream.of_string (input_line !in_chan)))) in
	   if (Term.is_special t) or (Term.is_variable t)
	   then 
	     begin
	       Printf.fprintf !out_chan "%s" "\nTerm should begin by a symbol of the Alphabet! try again\n\n";
	       flush !out_chan;
	       term_read a aspecial vars
	     end
	   else t)
    with Term.Badly_formed_term _ 
      | Term.Parse_error _ 
      | Stream.Failure 
      | Term.Undefined_symbol _ -> 
	  Printf.fprintf !out_chan "%s" "\nInvalid term, try again\n\n";
	  flush !out_chan;
	  term_read a aspecial vars


  (* Runs a completion on a given trs rws, a tree automaton a, an approximation material gamma_content.
     In the completion state: cs, trs may decrease during completion (for exploration purposes)
     delta can only increase with new transitions, new_delta contains all new transitions obtained by applying
     all rules on all transitions ONE time and then is added to delta.
     index increase during completion each time that we generate a new state automatically.
     states, state_ops, and gamma_content are intialised with the automaton and
     are only enriched during the completion from one step to another.

     laut is a list of pairs (string, tree automaton) on which user can try to intersec the current automaton computed during 
     completion.

     In completion in static mode, only the last completion step is kept (nothing to forget!) *)

  let complet trs aut gamma_content laut (is_static: string) (variables: Term.variable_set) (init_name:string): automaton =
    let _= Gamma.varset:= variables in
    let init_states= Automaton.get_states aut in
    let rec menu (lcs: completion_state list) =
      try (
	begin
	  Printf.fprintf !out_chan "%s" ("\nCompletion step: "^(string_of_int (get_step_number (List.hd lcs)))^"\n\nDo you want to:\n\n(c)omplete one step  (use Ctrl-C to interrupt if necessary)\ncomplete (a)ll steps (use Ctrl-C to interrupt if necessary)\n(m)erge some states\n(s)ee current automaton\n(b)rowse current automaton with Tabi\n(d)isplay the term rewriting system\n(i)ntersection with verif automata\nintersection with (o)ther verif automata on disk\nsearch for a (p)attern in the automaton\n(v)erify linearity condition on current automaton\n(w)rite current automaton, TRS and approximation to disk\n(f)orget old completion steps\n(e)quation approximation in gamma\n(g)amma normalisation rules\n(det)erminise current automaton\n(u)ndo last step\n(q)uit completion\n\n");
	  match answer() with
	      'c' -> 
		begin
		  (* Ctrl-C is mapped to a specific handler *)
		  Sys.set_signal Sys.sigint (Sys.Signal_handle interruption_handler); 
		  current_automaton:= (get_automaton_from_completion_step (List.hd lcs));
		  Gamma.next_epsilon();
		  complet_on_state lcs
		end
	    | 'a' -> 
		begin
		  user_interrupt:= false;	
		  (* Ctrl-C is mapped to a specific handler *)
		  Sys.set_signal Sys.sigint (Sys.Signal_handle interruption_handler);
		  current_automaton:= (get_automaton_from_completion_step (List.hd lcs));
		  Gamma.next_epsilon();
		  complete_all_steps lcs
		end
	    | 'g'-> 
		let last_cs= List.hd lcs in
		  (match last_cs with
		      Dyn(cs) -> 
			let new_csd= parse_norm_rules cs variables in
			  menu ((Dyn new_csd)::lcs)
		    | Static(_) -> 
			begin
			  Printf.fprintf !out_chan "\nNot implemented in static mode!\n\n"; 
			  flush !out_chan;
			  menu lcs
			end)
			
	    | 'm' -> 
		let new_cs= merge_state (List.hd lcs) "" in
		  begin
		    current_automaton:= (get_automaton_from_completion_step new_cs);
		    Gamma.reinit_epsilon();
		    menu (new_cs::lcs)
		  end
	    | 't' -> 
		let new_cs= determinise (List.hd lcs) in
		  begin
		    current_automaton:= (get_automaton_from_completion_step new_cs);
		    Gamma.reinit_epsilon();
		    menu (new_cs::lcs)
		  end
	    | 'b' -> 
		(IFDEF TABI THEN
		   let merge= Visu.tabi_call (convert_automaton (get_automaton_from_completion_step (List.hd lcs))) in
		     if merge="." then menu lcs
		     else 
		       let new_cs= merge_state (List.hd lcs) merge in
			 begin
			   current_automaton:= (get_automaton_from_completion_step new_cs);
			   Gamma.reinit_epsilon();
			   menu (new_cs::lcs)
			 end
	        ELSE
		  begin
		    Printf.fprintf !out_chan "%s" "Tabi is not installed!\n\n";
		    flush !out_chan;
		    menu lcs
		  end END)
	    | 's' ->  
		begin
		  Printf.fprintf !out_chan "%s"
		    (Automaton.to_string !current_automaton);
		  flush !out_chan;
		  menu lcs
		end
	    | 'd' -> 
		begin
		  Printf.fprintf !out_chan "%s"
		    (TRS.to_string trs);
		  Printf.fprintf !out_chan "%s" "\n";
		  flush !out_chan;
		  menu lcs
		end
		
	    | 'q' -> 
		if not ((TRS.non_linear_lhs trs)=[]) then
		  begin
		    Printf.fprintf !out_chan "%s" "Your TRS is non left-linear the completion is correct only if\nyou have verifed the linearity condition\nDo you want to verify it before quitting?";
		    flush !out_chan;
		    if Gamma.go() then menu lcs
		    else (get_automaton_from_completion_step (List.hd lcs))
		  end
		else
		  (get_automaton_from_completion_step (List.hd lcs))
		  
	    | 'f' -> 
		if List.length lcs > 1 then 
		  begin
		    Printf.fprintf !out_chan  "%s" "Forget old completion steps!\n";
		    menu [(List.hd lcs)]
		  end
		else 
		  begin
		    Printf.fprintf !out_chan  "%s" "Nothing to forget!\n";
		    menu lcs
		  end

	    | 'u' -> 
		if List.length lcs > 1 then 
		  begin
		    Printf.fprintf !out_chan  "%s" "Undo last completion step!\n";
		    current_automaton:= (get_automaton_from_completion_step (List.hd (List.tl lcs)));
		    Gamma.previous_epsilon();
		    menu (List.tl lcs)
		  end
		else 
		  begin
		    Printf.fprintf !out_chan  "%s" "Nothing to undo!\n";
		    menu lcs
		  end

	    | 'i' -> 
		begin
		  if laut=[]
		  then 
		    begin
		      Printf.fprintf !out_chan "%s" "List of automata is empty: cannot compute intersections!\n\n";
		      menu lcs;
		    end
		  else 
		    begin
		      verif_inter (get_automaton_from_completion_step (List.hd lcs)) laut;
		      menu lcs
		    end
		end


	    | 'o' -> 
		let (ok, f)= file_name() in
		  if not ok then (menu lcs)
		  else 
		    let lautext= 
		      try(let s= Spec.file_parse f in
			    Spec.get_list_automata s)
		      with _ -> 
			begin Printf.fprintf !out_chan "%s" ("\n\nWARNING: "^f^" is an invalid specification file!\n\n");
			  []
			end
		    in
		      if lautext=[]
		      then 
			begin
			  Printf.fprintf !out_chan "List of automata is empty: cannot compute intersections!\n\n";
			  menu lcs;
			end
		      else 
			begin
			  verif_inter (get_automaton_from_completion_step (List.hd lcs)) lautext;
			  menu lcs
			end

	    | 'p' ->
		let aut= (get_automaton_from_completion_step (List.hd lcs)) in
		let alphabet= (get_alphabet (List.hd lcs)) in
		let state_ops= (get_state_ops (List.hd lcs)) in
		let _= Printf.fprintf !out_chan "%s" 
			 ("Alphabet=\n"^(Alphabet.to_string alphabet)^"\n\nStates=\n"^(Alphabet.to_string state_ops)^"\n\nVariables=\n"^(Variable_set.to_string variables)^"\n\nType a term and hit Return: "); flush !out_chan in
		let t = term_read alphabet state_ops variables in
		let aut_for_t= translate_one_term_into_automaton t 0 alphabet in
		let inter_pattern_aut= intersection aut_for_t aut in
		let cleant_inter= special_clean inter_pattern_aut in
		let solutions= new_subst empty_automaton cleant_inter in
		let string_of_solutions= (labelled_substitution_to_string solutions) in
		  if string_of_solutions = "" 
		  then 
		    begin
		      Printf.fprintf !out_chan "%s" "\n\nPattern not found!\n\n";
		      menu lcs
		    end
		  else
		    begin
		      Printf.fprintf !out_chan "%s" ("\n\nSolutions:\n"^
						     string_of_solutions^
						     "\n\n");
		      menu lcs
		    end


	    | 'v' -> 
		let (is_lin, lstates)= (check_linearity (List.hd lcs)) in
		  if is_lin then
		    begin
		      Printf.fprintf !out_chan  "%s" "No linearity problem!\n";
		      menu lcs
		    end
		  else 
		    begin 
		      Printf.fprintf !out_chan  "%s" "Warning: there was at least one linearity problem";
		      let _=Common.my_map (function q -> Printf.fprintf !out_chan  "%s" ((Term.to_string q)^" ")) lstates in
			menu lcs
		    end		 
	    | 'w' -> 
		let (ok, file_name)= file_name() in
		  if not ok then (menu lcs)
		  else 
		    let last= List.hd lcs in
		    let aut= get_automaton_from_completion_step last in
		    let s= 
		      {Spec.alphabet= get_alphabet last;
		       Spec.variables= variables;
		       Spec.trs_list= [("current_TRS", trs)];
		       Spec.automata_list= ((("completed_"^init_name), aut)
					    ::(("initial_"^init_name), 
					       get_automaton_from_completion_step 
						 (List.nth lcs ((List.length lcs) -1)))
					    ::laut);
		       Spec.gamma_list= [("current_approx", Gamma.set_new_states (Automaton.get_state_ops aut) (get_gamma last))] } 
		    in
		    begin
		      (try (Spec.write_to_disk s file_name)
		       with
			   _ -> 
			     begin
			       Printf.fprintf !out_chan  "%s" ("Cannot write in file: "^file_name^"!\n");
			       flush !out_chan
			     end);
		      menu lcs
		    end
	    | 'e' -> 
		(let first= List.hd lcs in
		  match first with 
		      Dyn(csd) -> 
			let new_csd= parse_equation_rules csd variables in
			  menu ((Dyn (final_state_merge new_csd))::lcs)

		    | Static(csd) -> 
			begin 
			  Printf.fprintf !out_chan "\nNot implemented in static mode!\n\n"; 
			  flush !out_chan;
			  menu lcs
			end)


	    | _ -> failwith "Bug in parsing of user command: Completion.answer()"
	end)
      with
	  Sys.Break -> 
	    begin
	      Printf.fprintf !out_chan "%s" "\n\nLast completion step has been aborted!!\n";
	      Printf.fprintf !out_chan "%s" "---------------------------------------\n\n";
	      (* Ctrl-C is re-mapped to its default behaviour *)
	      Sys.set_signal Sys.sigint (Sys.Signal_default);
	      menu lcs
	    end
	    
      (* complete only one step *)

      and complet_on_state lcs= 
		 let first= (List.hd lcs) in
		 let one_step= 
		   match first with
		       Dyn(csd) -> (Dyn (dyn_complet_one_step csd init_states))
		     | Static(css) -> (Static (static_complet_one_step css))
		 in
		   if Transition.is_empty(get_new_trans one_step) 
		   then
		     begin 
		       Printf.fprintf !out_chan "%s" "\nAutomaton is complete!!\n";
		       Printf.fprintf !out_chan "%s" "------------------------\n\n"; 
		       menu (one_step::lcs)
		     end
		   else 
		     begin
		       current_automaton:= (get_automaton_from_completion_step one_step);
		       menu (one_step::lcs)
		     end
		       
      (* complete until the automaton is complete or user type Ctrl-C *)

      and complete_all_steps (lcs: completion_state list)=
		 let first= List.hd lcs in
		   try (
		     let one_step= 
		       match first with
			   Dyn(csd) -> (Dyn (dyn_complet_one_step csd init_states))
			 | Static(css) -> (Static (static_complet_one_step css))
		     in
		       if Transition.is_empty(get_new_trans one_step)
		       then 
			 begin
			   Printf.fprintf !out_chan "%s" "\nAutomaton is complete!!\n";
			   Printf.fprintf !out_chan "%s" "------------------------\n\n"; 
			   menu (one_step::lcs)
			 end
		       else
			 if !user_interrupt then
			   begin
			     (* Ctrl-C is re-mapped to its default behaviour *)
			     
			     Sys.set_signal Sys.sigint (Sys.Signal_default);
			     menu (one_step::lcs)
			   end
			 else
			   begin
			     current_automaton:= (get_automaton_from_completion_step one_step);
			     complete_all_steps (one_step::lcs)
			   end)
		   with
		       Sys.Break -> 
			 begin
			   Printf.fprintf !out_chan "%s" "\n\nLast completion step has been aborted!!\n";
			   Printf.fprintf !out_chan "%s" "---------------------------------------\n\n";
			   (* Ctrl-C is re-mapped to its default behaviour *)
			   Sys.set_signal Sys.sigint (Sys.Signal_default);
			   menu lcs
			 end
			 
    in
      begin
	Printf.fprintf !out_chan "%s" ("\nSTARTING COMPLETION (with "^is_static^" normalisation)...\n");
	Printf.fprintf !out_chan "%s" "-----------------------------------------------------\n\n\n"; 
	flush !out_chan;
	current_automaton:= aut;
	locally_deterministic_states:= [];
	if is_static="dynamic" then
	  menu [(Dyn(make_dynamic_completion_state trs aut gamma_content 0 0))]
	else 
	  begin
	    is_forced:= (is_static="forced static");
	    menu [(Static (make_static_completion_state trs aut gamma_content 0 !is_forced))]
	  end
      end

end
  
