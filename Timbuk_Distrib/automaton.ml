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

open Common

(* Tree Automata with normalized transitions *)

module TreeAutomata
  (Symbol_type: PRINTABLE_TYPE)(Alphabet_type: ALPHABET_TYPE with type symbol= Symbol_type.t)
  (Variable_type: PRINTABLE_TYPE)
  (Configuration_type: TERM_TYPE with type symbol= Symbol_type.t and type variable= Variable_type.t
				 and type alphabet= Alphabet_type.t)
  (State_content: STATE_CONTENT_TYPE)
  (Transition_type: TRS_TYPE with type alphabet= Alphabet_type.t and type term= Configuration_type.t)
  (State_set_type: STATE_SET_TYPE with type state= Configuration_type.t and type state_content= State_content.t 
				  and type alphabet= Alphabet_type.t and type symbol= Symbol_type.t)=
struct
  exception Not_a_state of string
  exception Not_in_folder
  exception Multiply_defined_symbol of string
  exception Linearity_problem of string
  exception Normalisation_problem of string 

  module State_type= Configuration_type
  module TRS_type= Transition_type

  type symbol= Symbol_type.t
  type alphabet= Alphabet_type.t
  type term= Configuration_type.t
  type rule= Transition_type.rule
  type substitution= Configuration_type.substitution
  type state= term
  type state_set= State_set_type.t
  type transition_table= Transition_type.t

  type tree_automata = {alphabet: Alphabet_type.t;
			state_ops: Alphabet_type.t;
			states: State_set_type.t;
			final_states: State_set_type.t;
			prior: transition_table;
			transitions: transition_table}


  type t = tree_automata

  type ('a, 'b) folder = ('a * 'b) list


  (* States are terms!!! In configurations, states are separated from
     other subterms by their embedding in constructor Special (see
     term.ml). The exact description of a state (its meaning described
     by a string) is only given in the state set *)

			   
  (* Types used for the construction of matching solutions, then converted into
     substitutions *)


  type mini_subst= (term * term)
  type sol_filt=  
    | Empty
    | Bottom
    | S of mini_subst   
    | Not of sol_filt
    | And  of sol_filt * sol_filt  
    | Or of sol_filt * sol_filt          

  (* Type used for the determinisation of tree automata *)

  type det_state= state list  (* set of states, represented by ordered lists of states. 
				 states are ordered w.r.t. their [to_string] value *)

  type det_trans= symbol * det_state list * det_state  (* a deterministic transition is built on a symbol a 
							  list of [det_state] (its arguments) and a destination
							  deterministic state *)

  (* state labels for specific operations *)

  let temporary_state_label = "q#q#q"
  let temporary_state_label2 = "q#q#q2"
  let default_state_label = "q"
  let default_bottom_label = "qbot"
  let default_tf_label = "qTF"
  let default_red_label = "qred"

  (* accessors of automata *)

  let get_alphabet a = a.alphabet
  let get_state_ops a = a.state_ops
  let get_states a = a.states
  let get_final_states a = a.final_states
  let get_transitions a = a.transitions
  let get_prior a = a.prior
  let make_automaton al stops state_set final prior trans=
    {alphabet= al; state_ops= stops; states= state_set; final_states=final;
     transitions= trans; prior= prior}

  let modify_state_ops a (ops: alphabet)=
    {alphabet= a.alphabet; state_ops= ops; states= a.states; 
     final_states=a.final_states; transitions= a.transitions; prior= a.prior}

  let modify_prior a p= 
    {alphabet= a.alphabet; state_ops= a.state_ops; states= a.states; 
     final_states=a.final_states; transitions= a.transitions; prior= p}

  let modify_final a final= 
    {alphabet= a.alphabet; state_ops= a.state_ops; states= a.states; 
     final_states=final; transitions= a.transitions; prior= a.prior}

  let modify_transitions a trans= 
    {alphabet= a.alphabet; state_ops= a.state_ops; states= a.states; 
     final_states=a.final_states; transitions= trans; prior= a.prior}

  let modify_states a states= 
    {alphabet= a.alphabet; state_ops= a.state_ops; states= states; 
     final_states=a.final_states; transitions= a.transitions; prior= a.prior}

  (* emptyness of an automaton (for emptyness of the language apply simplify before) *)

  let is_empty a= Transition_type.is_empty (get_transitions a)

  (* Construction of a state from a symbol with arity 0 *)
  let make_state (symb: symbol)= Const(symb)

  (* Construction of a state config from a state *)
  let make_state_config (state: state)= Special(state)

  (* Construction of a new normalised transition *)

  let new_trans (symb: symbol) (l_states: state list) (state: state) = 
    let l_args = List.map 
		   (function a -> Special(a)) l_states in
      Transition_type.new_rule
	(if l_states = [] then Const(symb)
	 else Fsym(symb, l_args))
	(Special state)


  (* Since a state is a Special term in configuration, we can know if a given 
     subterm of a config is a state by the following function: *)

  let is_state_config= Configuration_type.is_special

  (* Left-hand side and right hand side of a transition *)

  let lhs trans = Transition_type.lhs trans
  let rhs trans = match (Transition_type.rhs trans) with
      Special(q) -> q
    | x -> raise (Not_a_state ((Configuration_type.to_string x)^
			       " is not a state in "^
			       (Transition_type.rule_to_string trans)))

  (* Top symbol of a transition *)

  let top_symbol trans = Configuration_type.top_symbol (lhs trans)

  (* State label of a state in a configuration (special term) *)
			   
  let state_label = State_type.get_special


  (* is a transition normalized? i.e. of the for f(q1,... qn) -> q' *)

  let is_normalized trans= 
    let lhs = (lhs trans) in
    let depth= Configuration_type.depth lhs in
      if depth=0 then
	if Configuration_type.is_constant lhs then true  (* a -> q is normalised *)
	else false (* but q1 -> q2 is not *)
      else
	if depth=1 then
	  if List.for_all is_state_config (Configuration_type.list_arguments lhs) 
	  then true (* f(q1, ..., qn) -> q is normalized *)
	  else false (* f(q1, ..., a, ..., qn) -> q is not if a is a constant *)
	else
	  false (* if depth is greater to 1, it is necessarily not normalised *)
	    
	    
  (* This one returns only states occurring in the left hand side of 
     a transition *)

  let list_state trans = Configuration_type.list_special (lhs trans)


  (* prettyprint of tree automata *)

  let to_string ta = 
    "States "^(Alphabet_type.to_string ta.state_ops)^"\n\n"^
    (let descr= State_set_type.to_string_verb ta.states in
       if descr="" then ""
       else "Description\n"^(State_set_type.to_string_verb ta.states)^"\n\n")^
    "Final States "^(State_set_type.to_string ta.final_states)^"\n\n"^
    (if (Transition_type.is_empty ta.prior) 
     then "" 
     else "Prior\n"^(Transition_type.to_string ta.prior)^"\n\n")^
    "Transitions "^"\n"^(Transition_type.to_string ta.transitions)^"\n"

  let print ta= print_string (to_string ta)

  let states_of_transitions trs = 
    let rec aux l= 
      match l with
	  [] -> []
	| t::rem -> 
	    List.append ((rhs t)::(list_state t)) (aux rem)
    in
    let res= (aux (Transition_type.to_list trs)) in
      State_set_type.list_to_set res

      
  (* Parsing of a tree automaton *)

  let rec parse alphabet = parser
      [<  'Genlex.Kwd "States";
	  state_ops = State_set_type.parse_ops;
	  aut = parse_state_part alphabet state_ops >] -> 
	if Alphabet_type.disjoint alphabet state_ops then aut
	else raise (Multiply_defined_symbol "states and symbols are not disjoint")

  and parse_state_part alphabet state_ops = 
    parser
	[< 'Genlex.Kwd "Description";
	   descr_state_set = State_set_type.parse_verb alphabet state_ops;
	   'Genlex.Kwd "Final";'Genlex.Kwd "States";
	   final = State_set_type.parse alphabet state_ops;
	   (trs, prior) = parse_remaining alphabet state_ops >] ->
	  make_automaton alphabet state_ops 
	    (State_set_type.union (states_of_transitions trs)
	       descr_state_set) final prior (Transition_type.union prior trs)

      |	[< 'Genlex.Kwd "Final";'Genlex.Kwd "States";
	   final = State_set_type.parse alphabet state_ops;
	   (trs, prior) = parse_remaining alphabet state_ops >] ->
	  let union_prior_trs= (Transition_type.union prior trs) in
	    make_automaton alphabet state_ops (states_of_transitions union_prior_trs) final prior 
	      union_prior_trs

  and parse_remaining alphabet state_ops = 
    parser
	[< 'Genlex.Kwd "Transitions";
	   trs = Transition_type.parse_ground_special alphabet state_ops >] -> 
	  if List.for_all is_normalized (Transition_type.to_list trs) then
	    (Transition_type.check_special trs alphabet state_ops, Transition_type.empty)
	  else raise (Normalisation_problem 
			("Some transitions in: \n"^
			 (Transition_type.to_string trs)^
			 "\n\nare not normalized!!"))
	  
      | [< 'Genlex.Kwd "Prior";
	   prior = Transition_type.parse_ground_special alphabet state_ops;
	   'Genlex.Kwd "Transitions";
	   trs = Transition_type.parse_ground_special alphabet state_ops >] ->
	  if not (List.for_all is_normalized (Transition_type.to_list trs))
	  then raise (Normalisation_problem 
			("Some transitions in: \n"^
			 (Transition_type.to_string trs)^
			 "\n\nare not normalized!!"))
	  else 
	    if not (List.for_all is_normalized (Transition_type.to_list prior))
	    then raise (Normalisation_problem 
			("Some transitions in: \n"^
			 (Transition_type.to_string prior)^
			 "\n\nare not normalized!!"))
	    else 
	      (Transition_type.check_special trs alphabet state_ops, 	    
	       Transition_type.check_special prior alphabet state_ops)



  (* Cleaning of tree automaton *)

  (* accessibility cleaning of tree automaton *)
	  
	  
  let accessibility_cleaning ta = 
    let old_set = ta.states in
    let rec acc_aux trans_in trans_temp trans_out set (new_addition: bool)= 
      if (Transition_type.is_empty trans_in)
      then 
	if not new_addition then set,trans_out
	else acc_aux
	  trans_temp
	  Transition_type.empty
	  trans_out
	  set
	  false
      else 
	let first_trans = (Transition_type.first trans_in) in
	let l_args = list_state first_trans in
	let right_state = rhs first_trans in
	  if State_set_type.all_mem l_args set
	  then acc_aux 
	    (Transition_type.remainder trans_in)
	    trans_temp
	    (Transition_type.add_fast first_trans trans_out)
	    (State_set_type.add_verb right_state 
	       (State_set_type.state_description right_state old_set)
	       set)
	    true
	  else acc_aux
	    (Transition_type.remainder trans_in)
	    (Transition_type.add_fast first_trans trans_temp)
	    trans_out
	    set
	    new_addition

    in 
    let new_set, new_trans = 
      acc_aux ta.transitions Transition_type.empty 
	Transition_type.empty State_set_type.empty false in
    let new_final = State_set_type.inter new_set ta.final_states in
      make_automaton ta.alphabet ta.state_ops new_set new_final 
	(Transition_type.inter ta.prior new_trans) new_trans


  (* utility cleaning *)

  let utility_cleaning ta = 
    let valid_ta=
  (* if ta is a tree automaton with structured state sets,
     we first build the set of states and set of final states. *)
      if State_set_type.is_structured ta.states 
      then 
	let states= states_of_transitions ta.transitions in
	let final_states= State_set_type.inter states ta.final_states in
	  {alphabet= ta.alphabet; state_ops= ta.state_ops; states= states;
	   final_states= final_states; prior= ta.prior; transitions= ta.transitions}
      else ta 
    in
    let old_set = valid_ta.states in
    let rec acc_aux trans_in trans_temp trans_out set = 
      if (Transition_type.is_empty trans_in)
      then set,trans_out
      else 
	let first_trans = (Transition_type.first trans_in) in
	let l_args = list_state first_trans in
	let right_state = rhs first_trans in
	  if (State_set_type.mem right_state
		set)
	  then acc_aux
	    (Transition_type.union trans_temp 
	       (Transition_type.remainder trans_in))
	    (Transition_type.empty)
	    (Transition_type.add first_trans trans_out)
	    (State_set_type.add_all_verb l_args set old_set)

	  else acc_aux
	    (Transition_type.remainder trans_in)
	    (Transition_type.add first_trans trans_temp)
	    trans_out
	    set

    in 
    let new_set, new_trans = 
      acc_aux valid_ta.transitions Transition_type.empty 
	Transition_type.empty (State_set_type.inter valid_ta.states 
				 valid_ta.final_states) in
      {alphabet= valid_ta.alphabet; state_ops= valid_ta.state_ops; states= new_set; 
       final_states= valid_ta.final_states; prior= (Transition_type.inter valid_ta.prior new_trans);
       transitions= new_trans}


  let clean a = utility_cleaning (accessibility_cleaning a) 


  (* Rewriting of states label in a state set *)

  (* if the trs contains cycles then termination of renaming is forced using the following rule *)
  let rec terminating_rewriting (trs: rule list) (t: term)=
    match trs with 
	[] -> t
      | first::rem -> 
	  terminating_rewriting rem (TRS_type.left_inner_norm (TRS_type.list_to_trs [first]) t)
	    
  let rec rewrite_state_set set trs=
    if State_set_type.is_empty set then set
    else let prems = State_set_type.first set in
      State_set_type.add_verb (terminating_rewriting (TRS_type.to_list trs) prems)
	(State_set_type.state_description prems set)
	(rewrite_state_set (State_set_type.remainder set) trs)
	

  (* For automaton renaming or renumbering *)

  (* Build an equivalent renaming without cycles, by precomputing equivalence classes *)
  (* could be optimised using hash tables if necessary *) 

  (* partition_with_class returns [] as first parameter if there is no equivalence class for t1 in eqc, otherwise
     it returns the equivalence class of t1 as first parameter and the remainder of eqc as second parameter *)

  let rec partition_with_class (t1: term) (eqc: (term list) list) (temp: (term list) list): 
    ((term list) * ((term list) list))=
    match eqc with
	[] -> [],[]
      | clss::rem ->
	  if List.mem t1 clss
	  then (clss, List.append temp rem)
	  else partition_with_class t1 rem (clss::temp)
    

  (* Add an equivalence in an equivalence class *)

  let add_equivalence (t1: term) (t2: term) (eqc: (term list) list): (term list) list=
    let (eqc_t1, rem1)= partition_with_class t1 eqc [] in
      if eqc_t1=[]
      then 
	let (eqc_t2, rem2)= partition_with_class t2 eqc [] in
	  if eqc_t2= []
	  then ([t1;t2]::eqc)
	  else ((t1::eqc_t2)::rem2)
      else 
	if List.mem t2 eqc_t1
	then eqc
	else 
	  let (eqc_t2, rem2)= partition_with_class t2 rem1 [] in
	    if eqc_t2=[]
	    then ((t2::eqc_t1)::rem1)
	    else ((List.append eqc_t1 eqc_t2)::rem2)


  let rec rules_to_equiv_class (l: rule list) (eqc: (term list) list): (term list)list=
    match l with
	[] -> eqc
      | t::rem -> 
	  let lhs= TRS_type.lhs t in
	  let rhs= TRS_type.rhs t in
	    if lhs=rhs then rules_to_equiv_class rem eqc
	    else rules_to_equiv_class rem (add_equivalence lhs rhs eqc)

  let rec equiv_class_to_rules (eqc: (term list) list): (rule list)=
    match eqc with 
	[] -> []
      | clss::rem ->
	  if List.length clss < 2 then failwith "equiv_class_to_rules: malformed equivalence class of size < 2!"
	  else 
	    List.append 
	      (List.map (function t -> TRS_type.new_rule t (List.hd clss)) (List.tl clss))
	      (equiv_class_to_rules rem)
      
  let simplify_equivalence_classes (l: rule list): rule list=
    let eqc= rules_to_equiv_class l [] in
      equiv_class_to_rules eqc



  (* Renaming (or renumbering) of state labels 
     Be careful! Renaming may modify the [state_ops] alphabet  
     
     Be careful (2) !  for state set including states q1, q2 for
     example and structured states labels like q(f(q1,q2)),
     if q1 and q2 are to be renamed into q3 and q4 respectively, then
     so is q(f(q1,q2)) which is renamed into q(f(q3,q4))!!

     When renaming tree automata produced by intersection, this is
     different, and new states (not structured) are used for the
     renaming of product states #prod(q1,q2) obtained by cartesian
     product of transitions  *) 

  let renum_state_labels ta new_state_ops (trs: TRS_type.t) =
    let rec terminating_renaming (trs: rule list) trans=
      match trs with 
	  [] -> trans
	| first::rem -> 
	    terminating_renaming rem 
	      (TRS_type.left_inner_norm_special_system (TRS_type.list_to_trs [first]) trans) in 

    (* if the trs contains cycles then termination of renaming is forced using the following transformation *)
    let new_trans = terminating_renaming (TRS_type.to_list trs) ta.transitions in
    let new_prior = terminating_renaming (TRS_type.to_list trs) ta.prior in 
      {alphabet= ta.alphabet;
       state_ops= new_state_ops;
       states= rewrite_state_set ta.states trs;
       final_states= rewrite_state_set ta.final_states trs;
       prior = new_prior;
       transitions= new_trans}



  (* Rewriting of state labels in a tree automaton thanks to a term
     rewriting system.
     Rewriting of state labels in a tree automaton shall not modify the
     state ops alphabet *)

  let rewrite_state_labels ta trs= 
    renum_state_labels ta ta.state_ops trs

  (* producing a trs for automatic renaming of states *)
  let rec prod_renum seed state_set i trs new_alpha=
    if State_set_type.is_empty state_set then trs,new_alpha
    else
      let new_symb = Symbol_type.of_string (seed^(string_of_int i)) in
      let new_state = Const(new_symb) in
	prod_renum seed (State_set_type.remainder state_set)
	  (i + 1)
	  (TRS_type.add 
	     (TRS_type.new_rule 
		(State_set_type.first state_set)
		new_state)
	     trs)
	  (Alphabet_type.add_symbol new_symb 0 new_alpha)
	  

  (* if working on automaton with structured state sets (obtained
     after intersection for example),
     use [accessibility_cleaning] before this one, in order to physically 
     build the state set first (instead of using symbolic products of 
     state sets) *) 

  let automatic_renum ta = 
    let renaming_trs1,new_alpha1 =  
      prod_renum temporary_state_label
	ta.states 0 Transition_type.empty 
	Alphabet_type.new_alphabet
    in let temp_ta = renum_state_labels ta new_alpha1 renaming_trs1
    in let renaming_trs2,new_alpha2 =
	prod_renum default_state_label temp_ta.states 0 
	  Transition_type.empty
	  Alphabet_type.new_alphabet
    in renum_state_labels temp_ta new_alpha2 renaming_trs2


  (* union of tree automata, by renaming and union of transition tables, state set, 
     final state sets etc... *)

  let union a1 a2 = 
    let renaming_trs1, new_alpha1 =  
      prod_renum temporary_state_label
	a1.states 0 Transition_type.empty 
	Alphabet_type.new_alphabet in
    let renaming_trs2, new_alpha2 = 
      prod_renum temporary_state_label2
	a2.states 0 Transition_type.empty 
	Alphabet_type.new_alphabet 
    in let temp_ta1 = renum_state_labels a1 new_alpha1 renaming_trs1 
    in let temp_ta2 = renum_state_labels a2 new_alpha2 renaming_trs2 
    in let union_ta = 
	{alphabet= a1.alphabet;
	 state_ops= Alphabet_type.union_fast temp_ta1.state_ops temp_ta2.state_ops;
	 states= State_set_type.union temp_ta1.states temp_ta2.states;
	 final_states= State_set_type.union temp_ta1.final_states temp_ta2.final_states;
	 prior= Transition_type.union_fast temp_ta1.prior temp_ta2.prior;
	 transitions= Transition_type.union_fast temp_ta1.transitions 
			temp_ta2.transitions}
    in let renaming_trs3,new_alpha3 =
	prod_renum default_state_label union_ta.states 0 
	  Transition_type.empty
	  Alphabet_type.new_alphabet
    in renum_state_labels union_ta new_alpha3 renaming_trs3
	 

  (* Rough union of tree automata by union of transition table ... *)

  let make_fast_union at1 at2 =
    {alphabet = (Alphabet_type.union at1.alphabet at2.alphabet);
     state_ops = (Alphabet_type.union at1.state_ops at2.state_ops);
     states = (State_set_type.union at1.states at2.states);
     final_states = (State_set_type.union at1.final_states at2.final_states);
     prior = (Transition_type.union at1.prior at2.prior);
     transitions = (Transition_type.union at1.transitions at2.transitions)}


  (* Simplification of a tree automaton is a renaming of the result of
     cleaning (accessibility + utility) of the tree automaton *)

  let simplify a = automatic_renum (clean a)

  let is_language_empty a = is_empty (simplify a)


  let rec transition_graph l=
    match l with
	[] -> []
      | trans::rem -> 
	  let state= Transition_type.rhs trans in
	  let list_succ= Configuration_type.list_arguments (Transition_type.lhs trans) in
	  let rem_graph= transition_graph rem in
	  let old_succ= try (List.assoc state rem_graph) with Not_found -> [] in
	    if old_succ=[] 
	    then (state, (Common.clean list_succ))::rem_graph 
	    else (state, (Common.union list_succ old_succ))::(List.remove_assoc state rem_graph)


  let closure_one_step g=
    let rec aux l1 l2 b=
      match l1 with
	  [] -> (l2, b)
	| (vertex, succ)::rem ->
	    let new_succ= 
	      List.fold_right (function a -> function b -> (Common.union 
							      (try (List.assoc a g) with Not_found -> []) b)) succ [] in
	      if subeq_list new_succ succ
	      then aux rem ((vertex,succ)::l2) b
	      else aux rem ((vertex, (Common.union new_succ succ))::l2) true
    in
      aux g [] false
  

  (* fixpoint *)
	  
  let rec fix f l =
    let (lnew, modified) = (f l) in
      if modified then (fix f lnew)
      else l    
	


  (* Are the transitions recursive? *)

  let is_recursive delta: bool= 
    let graph= transition_graph (Transition_type.to_list delta) in
    let transitive_closure= fix closure_one_step graph in
    let rec is_cyclic graph=
      match graph with
	  [] -> true
	| (v,l)::rem -> if List.mem v l then false else is_cyclic rem 
    in
      is_cyclic transitive_closure


 (* Is the recognized language finite? *)
  let finite_recognized_language ta: bool= is_recursive (get_transitions (simplify ta))

  (* head and tail of a folder *)
  let folder_hd f = List.hd f
  let folder_tail f = List.tl f

  (*is a folder empty  *)
  let is_empty_folder f= f==[]

  let folder_assoc= List.assoc 

  (* adding a transition into a folder according to a given criteria 
     (top symbol or rhs state) *)

  let folder_add trans criteria folder = 
    let rec add_aux folder =
      match folder with
	  [] -> raise Not_in_folder
	| (c, trs)::rem when c=criteria -> 
	    (c, trans::trs)::rem
	| any::rem -> any::(add_aux rem)

    in try add_aux folder with 
	Not_in_folder -> (criteria,[trans])::folder

  (* replacing the whole set of element of a folder associated with a given criteria *)

  let rec folder_replace (ltrans: 'a) (criteria: 'b) (folder: ('b, 'a) folder)  =
    match folder with
	[] -> [(criteria, ltrans)]
      | (c, trs)::rem when c=criteria -> 
	  (c, ltrans)::rem
      | any::rem -> any::(folder_replace ltrans criteria rem)


  (* a [bi_folder] is a folder of folder, for adding we thus need 2 criteria *)

  let bi_folder_add trans crit1 crit2 bifolder = 
    let rec add_aux folder =
      match folder with
	  [] -> raise Not_in_folder
	| (c, folder)::rem when c=crit1 -> 
	    (c, folder_add trans crit2 folder)::rem
	| any::rem -> any::(add_aux rem)

    in try add_aux bifolder with 
	Not_in_folder -> (crit1, [(crit2, [trans])])::bifolder

  (* membership of a transition in a [bi_folder] of transitions categorized by symbol and then by state *)
	    (* state index are only state names and not special terms *)

  let bi_folder_mem trans bifolder=
    try (List.mem trans 
	   (List.assoc (rhs trans) 
	      (List.assoc (Configuration_type.top_symbol (lhs trans)) bifolder)))
    with Not_found -> false


  (* adding a list of transition to a folder ... transitions are not added if they are already in the folder *)

  let rec bi_folder_add_trans_list ltrans bifolder=
    match ltrans with
	[] -> bifolder
      | tr1::rem ->  
	  let remainder= bi_folder_add_trans_list rem bifolder in
	    if bi_folder_mem tr1 remainder then remainder
	    else bi_folder_add tr1 (Configuration_type.top_symbol (lhs tr1))
	      (rhs tr1) remainder


  (* Obtain configurations from a bifolder corresponding to a given top symbol (of the rhs) and a state (the lhs) *)

  let configs_from_symbol_to_state symb q folder=
    try 
      List.map Transition_type.lhs 
	(List.assoc q (List.assoc symb folder))
    with
	Not_found -> []

  (* [folder_flatten] flattens a folder into a transition list *)

  let rec folder_flatten folder= 
    match folder with
	[] -> []
      | (_,l)::rem -> List.append l (folder_flatten rem)

  let bi_folder_flatten bifolder= 
    (folder_flatten (folder_flatten bifolder))


  (* [transitions_by_symbol] returns the folder of transitions in trs
     gathered according to the top symbol of the lhs of each rule *)

  let rec transitions_by_symbol (trs: 'a list) = 
    match trs with
	[] -> []
      | first::remainder -> 
	  folder_add first (top_symbol first) 
	    (transitions_by_symbol remainder)

  (* [transitions_by_state] returns the folder of transitions in trs
     gathered according to the rhs of each rule (a state) *)

  let rec transitions_by_state (trs: 'a list) = 
    match trs with
	[] -> []
      |first::remainder ->
	 folder_add first (rhs first) 
	   (transitions_by_state remainder)


  (* [transitions_by_state_by_symbol] returns the folder of folders of
     transitions in trs gathered according to its top symbol and then
     according to the rhs of each rule (a state)*)

  let rec transitions_by_state_by_symbol (trs: 'a list) = 
    let rec aux folder=
      match folder with 
	  [] -> []
	| (f,ltrans)::rem_folder -> (f,(transitions_by_state ltrans))::(aux rem_folder)
    in aux (transitions_by_symbol trs)


  (* cartesian product of 2 transitions (with the same top symbol) *)

  let transition_product r1 r2= 
    let ts = top_symbol r1 in 
    let ls1 = list_state r1 in let ls2= list_state r2 in
    let state1 = rhs r1 in let state2= rhs r2 in
      
      new_trans ts (List.map2 State_set_type.state_product ls1 ls2)
	(State_set_type.state_product state1 state2)

  (* cartesian product of transition sets (all transitions have the same top symbol) *)
	
  let simple_prod system1 system2 acc=
    let rec prod_aux trs1 trs2 a= 
      match trs1, trs2 with
	  _, [] -> a
	|[],_::rem2 ->  prod_aux system1 rem2 a
	|r1::rem1, r2::_ -> 
	   (prod_aux rem1 trs2  ((transition_product r1 r2):: a))
    in
      prod_aux system1 system2 acc 
	 
	 
  (* Cartesian product of transition folders *)

  let folder_cartesian_product lf1 lf2= 
    let rec aux lf1 lf2 acc =
      match lf1 with
	  [] -> acc
	| (symbol,trs1)::reste -> 
	    let trs2 = 
	      (try List.assoc symbol lf2 
	      with Not_found -> []) in
	    let new_acc = simple_prod trs1 trs2 acc in
	      (aux reste lf2 new_acc )
    in aux lf1 lf2 []

  (* Automaton intersection *)

  let inter a1 a2 = 
    if (try (Alphabet_type.get_arity 
	       State_set_type.default_prod_symbol (get_state_ops a1)) = 2 
        with Alphabet_type.Symbol_not_in_alphabet(_) -> true)
    then 
      (if 
	 (try (Alphabet_type.get_arity 
	         State_set_type.default_prod_symbol (get_state_ops a2)) = 2 
          with Alphabet_type.Symbol_not_in_alphabet(_) -> true)
       then {alphabet= a1.alphabet;
	     state_ops= 
	       Alphabet_type.add_symbol 
		 State_set_type.default_prod_symbol 
		 2
		 (Alphabet_type.union a1.state_ops a2.state_ops);
	     states= State_set_type.symbolic_product a1.states a2.states;
	     final_states= State_set_type.symbolic_product
		             a1.final_states a2.final_states;
	     prior= Transition_type.list_to_trs 
		      (folder_cartesian_product
			 (transitions_by_symbol (Transition_type.to_list a1.prior))
			 (transitions_by_symbol (Transition_type.to_list a2.prior)));
	     transitions= Transition_type.list_to_trs 
			    (folder_cartesian_product
		               (transitions_by_symbol (Transition_type.to_list a1.transitions))
		               (transitions_by_symbol (Transition_type.to_list a2.transitions)))}

       else raise (Multiply_defined_symbol ("Reserved state product "^(Symbol_type.to_string State_set_type.default_prod_symbol)^" is already defined with an arity different from 2!")))
    else raise (Multiply_defined_symbol ("Reserved state product "^(Symbol_type.to_string  State_set_type.default_prod_symbol)^" is already defined with an arity different from 2!"))


  (* normalization of epsilon transition q1 -> q2  with current delta *)

  let normalize_epsilon q1 q2 (delta: transition_table)  =
    match q1 with
	Special(q1name) ->
	  let trans_to_q1= 
	    try (List.assoc q1name (transitions_by_state (Transition_type.to_list delta)))
	    with Not_found -> []
	  in (Transition_type.list_to_trs 
		(List.map (function trans -> Transition_type.new_rule (lhs trans) q2) trans_to_q1))
	       
      | q -> failwith ("Problem in normalize_epsilon: "^
		       (State_type.to_string q)^" is not a state")
	  

  (* choice of new states for a given list of arguments. Where label is the default
     label for states and i is the last state label used. *)

  let new_states_for_arguments largs label i state_ops=
    let rec aux largs i ltrans lnew_args state_ops=
      match largs with
	  [] -> (ltrans, (List.rev lnew_args), state_ops)
	| c::lrem -> 
	    if is_state_config c 
	    then aux lrem i ltrans (c::lnew_args) state_ops
	    else 
	      let new_state_label= (Symbol_type.of_string 
				      (label^(string_of_int i))) in
	      let new_state= Special(Const(new_state_label)) in
	      let new_trans= Transition_type.new_rule c new_state in
		
		aux lrem (i + 1) (Transition_type.add new_trans ltrans) (new_state::lnew_args)
		  (Alphabet_type.add_symbol new_state_label 0 state_ops)

    in aux largs i Transition_type.empty [] state_ops
	 

  (* This function normalizes a list of transitions ltrans with new states whose labels are label^j where j starts
     from i and is increased repeatedly *)
	 

  let normalize ltrans delta label i=
    let rec aux ltrans i state_ops=
      if Transition_type.is_empty ltrans 
      then (Transition_type.empty, i, state_ops)
      else let t= Transition_type.first ltrans and lrem= Transition_type.remainder ltrans in
	if is_normalized t 
	then 
	  let (resrem, j, new_s_ops)= aux lrem i state_ops in ((Transition_type.add t resrem), j, new_s_ops)
	else
	  let lhs= Transition_type.lhs t in
	  let rhs= Transition_type.rhs t in
	    if is_state_config lhs then
	      let (resrem, j, new_s_ops)= aux lrem i state_ops in
	      let copy= normalize_epsilon lhs rhs delta in
		(Transition_type.union_fast copy resrem, j, new_s_ops)
	    else
	      
	      let (new_trans, new_args, new_s_ops)= 
		(new_states_for_arguments (Configuration_type.list_arguments lhs)
		   label i state_ops)  in 
		
	      let new_top_trans= 	
		Transition_type.new_rule (Fsym(
					    (Configuration_type.top_symbol lhs), 
					    new_args)) rhs in
		
		aux (Transition_type.add_fast
		       new_top_trans
		       (Transition_type.union_fast new_trans lrem))
		  (i + (List.length (Transition_type.to_list new_trans))) new_s_ops	    
		  
    in aux ltrans i Alphabet_type.new_alphabet


  (* This function determinise a list of transition produded by normalisation of a transition *)

  let rec compact (ltrans: rule list) (total: rule list): rule list=
    match ltrans with
	[] -> total 
      | t::rem ->
	  let (same_lhs, different)= List.partition (function t1 -> (Transition_type.lhs t1)=(Transition_type.lhs t)) rem in
	    if same_lhs = []
	    then compact rem total
	    else 
	      let rhs_t= rhs t in 
	      let trs= Transition_type.list_to_trs (List.map (function t1 -> (Transition_type.new_rule (rhs t1) rhs_t)) same_lhs) in
	      let renamed_and_cleant=
		Common.clean (Transition_type.to_list (Transition_type.left_inner_norm_special_system trs (Transition_type.list_to_trs total))) in
		compact renamed_and_cleant renamed_and_cleant


  (* Same as normalize but produce a set of deterministic transitions. For instance [f(a, a)->q0] will be normalized
     into [f(q1, q1)->q0] and [a -> q1]. *)
	 
  let normalize_deterministic ltrans delta label i=
    let (normed_temp, j, states_temp)= normalize ltrans delta label i in
    let temp_list= Transition_type.to_list normed_temp in
    let det_normed= Transition_type.list_to_trs (Common.clean (compact temp_list temp_list)) in
      (det_normed, j, states_temp)


  (* Produce a deterministic tree automaton from a term list [lt], where states are labeled with [label^j] 
     where [j] starts at [i].*) 

  let rec term_set_to_transitions (lt: term list) (label: string) (i: int)
    (ldone: rule list) (stateops: alphabet): (rule list * alphabet * int)=
    match lt with 
	[] -> (ldone, stateops, i)
      | t::rem -> 
	  let qlabel= Symbol_type.of_string (label^(string_of_int i)) in
	    term_set_to_transitions rem label (i + 1) 
	      ((Transition_type.new_rule t (Special (make_state qlabel)))::ldone)
	      (Alphabet_type.add_symbol qlabel 0 stateops)


  (* Produce a deterministic tree automaton from a term list [lt], where states are labeled with [label^j] 
     where [j] starts at [i].*) 

  let term_set_to_automaton (al: alphabet) (lt: term list) (label: string) (i: int):(tree_automata * int) = 
    let (trans, finalalpha, j)= term_set_to_transitions lt label i [] Alphabet_type.new_alphabet in
    let (norm_trans, k, states_temp)= 
      normalize_deterministic (Transition_type.list_to_trs trans) Transition_type.empty label j in
      ((make_automaton al (Alphabet_type.union finalalpha states_temp) (states_of_transitions norm_trans)
	(State_set_type.list_to_set (List.map (function (x, y) -> make_state x) (Alphabet_type.to_list finalalpha)))
	 Transition_type.empty norm_trans), k)
      
	 
  (* Matching a term on a configuration given a transition folder (by symbol and by state) delta *)
	 
  let rec matching_one_term_one_config term config (delta: (symbol, (state, rule list) folder) folder)   =
    match (term, config) with
	(Var(x), Special(q)) -> S(Var(x), Special(q))
      | (Special(t), Special(q)) -> S(Special(t), Special(q))
      | (Const(a), Const(b)) -> if Symbol_type.equal a b then Empty else Bottom
      | (Const(a), Special(q)) -> 
	  matching_term_with_configs (Const(a)) (configs_from_symbol_to_state a q delta) delta
      | (Const(a), _) -> Bottom
      | (Fsym(f, largs), Special(q)) -> 
	  matching_term_with_configs (Fsym(f, largs)) (configs_from_symbol_to_state f q delta) delta
      | (Fsym(f, largs1), Fsym(g, largs2)) -> 
	  (if (Symbol_type.equal f g) 
	   then matching_args_on_args largs1 largs2 delta
	   else Bottom)
	  
      | (t1,t2) -> failwith ("Matching on tree automata problem: Trying to match "^(Configuration_type.to_string t1)^" with "^(Configuration_type.to_string t2))
	  
			 and matching_args_on_args term_args config_args (delta: (symbol, (state, rule list) folder) folder)=
	   match (term_args, config_args) with
	       ([t],[c]) -> matching_one_term_one_config t c delta
	     | (t::rt, c::rc) -> And((matching_one_term_one_config t c delta), matching_args_on_args rt rc delta)
	     | (t::rt, []) -> failwith ("Matching on tree automata problem: no argument to match subterm "^(Configuration_type.to_string t)^"on.")
	     | ([], t::rt) -> failwith ("Matching on tree automata problem: no term to match subconfig "^(Configuration_type.to_string t))
	     | ([], []) -> failwith ("Matching on tree automata problem: there is some non-constant symbols with 0 argument")
		 
		 
					  and matching_term_with_configs term lconfigs (delta: (symbol, (state, rule list) folder) folder)=
		  match lconfigs with
		      [c] -> matching_one_term_one_config term c delta
		    | c::rc -> Or((matching_one_term_one_config term c delta), 
				  (matching_term_with_configs term rc delta))
		    | [] -> Bottom
			

  (* Simplification of matching solutions, by propagating Bottom solutions into
     the formula and retrieving Bottom occuring in disjunctions and retrieving
     conjunctions where Bottom occurs *)

  let rec simplify_sol (p: sol_filt) =  
    match 
      p
    with 
      	S(x) -> S(x)      
      | And (a,b) -> let ca =simplify_sol a and cb =simplify_sol b in
	  if ca=Bottom || cb=Bottom 
	  then Bottom
	  else 
	    if ca=cb then ca
	    else And (ca,cb)
      | Or(a,b) -> 
	  let ca= simplify_sol a and cb= simplify_sol b in
	    if ca=Bottom 
	    then cb
	    else 
	      if cb=Bottom
	      then ca
	      else if ca=cb then ca else Or(ca,cb)
      | Not(a) ->
	  let ca= simplify_sol a in
	    if ca= Bottom 
	    then Empty 
	    else 
	      if ca= Empty 
	      then Bottom
	      else Not(ca)
      | x -> x
	  
	
  let dnf (s: sol_filt)=
    let rec aux s=
      match s with
	  And(a,Or(b,c)) ->  (Or(And(a,b),And(a,c)),true)
	| And(Or(b,c),a)->  (Or(And(b,a),And(c,a)), true)
	| And(a,b) -> 
	    let (anew, modif_a) = (aux a) in
	    let (bnew, modif_b) = (aux b) in
	      (And(anew, bnew), modif_a or modif_b)
	| Or (a,b) ->
	    let (anew, modif_a) = (aux a) in
	    let (bnew, modif_b) = (aux b) in
	      (Or(anew, bnew), modif_a or modif_b)
	| Not(And(a, b)) -> (Or(Not(a), Not(b)), true)
	| Not(Or(a, b)) -> (And(Not(a), Not(b)), true)
	| Not(Not(x)) -> (x, true)
	| Not(x) -> (Not(x), false)
	| x -> (x, false)
	    
    in (fix aux s)
	 
	 
  (* checks if a list of associations is a substitution i.e., a same variable cannot 
     be mapped to different values. s should be either:
     - the empty list (no subst) 
     - [[]] the empty subst 
     - [s'] where s' is the subst *)
	 
  let check_subst s= 
    match s with 
	[] -> []
      | _ -> 
	  try 
	    [(Configuration_type.coherent (List.hd s))] with 
		Configuration_type.Terms_do_not_match(_,_) -> []
		    
 
  (* Constructs a list of substitutions from a logical formula in **disjunctive
     normal form**, where litterals are of the form: Empty  (empty substitution), 
     Bottom (no substitution), or S(x, t) where x is a variable and t is its 
     value *)

  let  rec substlist (s: sol_filt)=
    let rec aux f =
      match 
	f
      with 
	  
	| Empty -> []
	| S(Var(x),t)-> [(x, t)]
	| And(a,b) -> (aux a)@(aux b)
	| Or(a,b) -> failwith "Problem in substitution conversion: not in Disjunctive normal form!!"
	| Bottom-> failwith "Problem in substitution conversion: Bottom encountered! simplification may not have been done before!"
	| S(t1, _) -> failwith ("Problem in substitution conversion (substlist aux): term "^(Configuration_type.to_string t1)^" is not a variable!!")
	| Not(_) -> failwith ("Problem in substitution conversion (substlist aux): remains some negations!")
	    
	    
    in 
      match 
	s
      with 
(*  Or(a,b) -> (check_subst (substlist a))@(check_subst (substlist b)) *)
	| Or(a,b) -> (substlist a)@(substlist b)
	| And(a,b) -> (check_subst [aux s])
	| Bottom -> []
	| Empty-> [[]]
	| S((Var(x), t)) -> [[(x, t)]]
	| S(t1, _) -> 
	    failwith ("Problem in substitution conversion (substlist): term "^(Configuration_type.to_string t1)^" is not a variable!!")
	| Not(_) -> failwith ("Problem in substitution conversion (substlist): remains some negations!")


  let matching term config (delta: (symbol, (state, rule list) folder) folder)= 
    substlist (dnf (simplify_sol (matching_one_term_one_config term config delta))) 

(*
  let matching term config (delta: (symbol, (state, rule list) folder) folder)= 
    let result=
      substlist (dnf (simplify_sol (matching_one_term_one_config term config delta))) in
    let _= print_string ("Filtrage de "^(Configuration_type.to_string term)^" sur "^(Configuration_type.to_string config)^(if result=[] then " ECHEC\n" else " OK")) in
      result
*)


  (* This function simplifies the solutions of matching up to true or false, provided that matching has be 
     done between a configuration and a state... this is used by the next function *)

  let rec matching_solve (p: sol_filt) =  
    match 
      p
    with 
	Empty -> true
      | Bottom -> false
      | S((x,y)) -> Configuration_type.equal x y
      | And (a,b) -> 
	  if matching_solve a then matching_solve b 
	  else false
      | Or(a,b) -> 
	  if matching_solve a then true
	  else matching_solve b
      | Not(_) -> failwith ("Problem in (substlist aux): remains some negations!")

  (* Construct the disjointness constraint for non left-linear terms
  matching on the automaton: if a rule f(x, x) matches a configuration
  of the form f(q1, q2), we need to verify that q1 and q2 do not
  recognize any common term. First we need to get all the pairs that
  have to be checked such a way, starting from a set of non linear
  terms and a transition table delta *)



  let matching_non_linear_terms_with_all_configs lterm (delta: (symbol, (state, rule list) folder) folder)=
    let rec aux lterm=
      match lterm with 
	  [] -> Empty
	| t::lrem -> 
	    let top_symb= Configuration_type.top_symbol t in
	    let concerned_transitions= try (folder_flatten (List.assoc top_symb delta)) with Not_found -> [] in
	    let matching_sol= matching_term_with_configs t (List.map lhs concerned_transitions) delta in
	      Or(matching_sol, aux lrem)
    in aux lterm


  let rec add_ordered x t lassoc=
    let rec aux t l=
      match l with
	  [] -> [t]
	| t1::lterm -> 
	    if (Configuration_type.equal t1 t) then l
	    else 
	      if (Configuration_type.to_string t1) > (Configuration_type.to_string t) then t::l
	      else t1::(aux t lterm)

    in
      match lassoc with 
	  [] -> [(x, [t])]
	|(y, l)::rem -> 
	   if Variable_type.equal x y then (y, (aux t l))::rem
	   else (y,l)::(add_ordered x t rem)


	     
  let sub_to_constraint subst=
    let rec suppress_linear l= 
      match l with
	  [] -> []
	|(x,lstate)::rem -> 
	   if List.length lstate <= 1 then (suppress_linear rem)
	   else lstate::(suppress_linear rem)
    in
    let rec aux subst lassoc=
      match subst with
	  [] -> suppress_linear lassoc
	|(x,t)::reml -> 
	   aux reml (add_ordered x t lassoc)
    in aux subst []


  let rec check_linear list_sub= 
    match list_sub with 
	[] -> []
      | sub::rem_lsub -> 
	  (sub_to_constraint sub)@(check_linear rem_lsub)
	  
  let  rec matchingsol_to_constraint (s: sol_filt)=
    let rec aux f =
      match 
	f
      with 
	  
	| Empty -> []
	| S(Var(x),Special(q))-> [(x, q)]
	| And(a,b) -> (aux a)@(aux b)
	| Or(a,b) -> failwith "Problem in matchingsol conversion: not in Disjunctive normal form!!"
	| Bottom-> failwith "Problem in matchingsol conversion: Bottom encountered! simplification may not have been done before!"
	| S(t1, _) -> failwith ("Problem in matchingsol conversion (matchingsol aux): term "^(Configuration_type.to_string t1)^" is not a variable!!")
	| Not(_) -> failwith ("Problem in matchingsol conversion: remains some negations!")   
	    
    in 
      match 
	s
      with 
	  Or(a,b) -> (matchingsol_to_constraint a)@(matchingsol_to_constraint b)
	| And(a,b) -> [aux s]
	| Bottom -> []
	| Empty-> []
	| S((Var(x), t)) -> []
	| S(t1, _) -> 
	    failwith ("Problem in matchingsol conversion (substlist): term "^(Configuration_type.to_string t1)^" is not a variable!!")
	      
	| Not(_) -> failwith ("Problem in matchingsol conversion: remains some negations!")

  (* used to verify if the application of a (possibly) non linear TRS to an automaton
     may match disjoint states with common recognized terms *)


  let disjointness_constraint lterms delta_folder=
    check_linear(matchingsol_to_constraint (dnf (simplify_sol (matching_non_linear_terms_with_all_configs lterms delta_folder))))


  (* used to verify if a term rewrites to a given state thanks to Tree Automata transitions i.e., t ->*A q ?? *)

  let rec matching_solve (p: sol_filt) =  
    match 
      p
    with 
	Empty -> true
      | Bottom -> false
      | S((x,y)) -> Configuration_type.equal x y
      | And (a,b) -> 
	  if matching_solve a then matching_solve b 
	  else false
      | Or(a,b) -> 
	  if matching_solve a then true
	  else matching_solve b
      | Not(_) -> failwith ("Problem in (matching_solve): remains some negations!")
	    
  (* this function permits to know if a given configuration can be rewritten (hence recognized) into a given
     state (special term), thanks to transition folder delta.
     Instead of using rewriting, we here use matching to obtain a more goal-directed algorithm, and thus more 
     efficient! 
  *)

  let is_recognized_into config state (delta: (symbol, (state, rule list) folder) folder)=
    matching_solve (matching_one_term_one_config config state delta)

  (* make a run of a tree automaton: verify if a term t rewrites into 
     state q with regards to transitions of automaton a.
     same thing but starting from a term, a state and a tree automaton.*)

  let run config state (a:t)=
    is_recognized_into config (Special state) (transitions_by_state_by_symbol (Transition_type.to_list (get_transitions a)))


  (* same as the previous one but in the particular case where the transition is an epsilon transition 
     q1 -> q2, this consists in verifying that all the transitions in q1 are already in q2.
     note that state_config and state are special terms so we first need to get the label first *)

  let is_covered q1 q2 (delta: transition_table)=
    let label_q1= state_label q1 in (* non special terms now *)  
    let label_q2= state_label q2 in 
      
    let transitions_by_state= transitions_by_state (Transition_type.to_list delta) in
    let transitions_to_q1= try (List.assoc label_q1 transitions_by_state) with Not_found -> [] in
    let transitions_to_q2= try (List.assoc label_q2 transitions_by_state) with Not_found -> [] in
    let configs_to_q1= List.map lhs transitions_to_q1 in
    let configs_to_q2= List.map lhs transitions_to_q2 in
      
      List.for_all (function x -> List.mem x configs_to_q2) configs_to_q1


  (* Determinisation of tree automata. 
     The algorithm used here is modification of the classical algorithm
     which is based on constructing transitions on sets of states (det_state), the
     only optimisation is that we only build accessible set of det_state. 

     Initially we start from an empty set of det_state, then assuming
     that we have a constant a such that a->q1 and a->q2, we build a det
     transition a->{q1,q2} and add {q1,q2} to the set of new
     det_states. Then assuming that we have 2 transitions f(q1, q2)->q3
     and f(q2, q2)->q4, we can add a first transition
     (a) f({q1,q2},{q1,q2})->{q3} since q1\in{q1,q2} and q2\in{q1,q2}
     and similarly add a transition (b) f({q1,q2},{q1,q2})->{q4} with
     respective new det_states: {q3}, {q4}. What we have chosen here is
     that when adding transition (b) after having added transition (a)
     both are merged into f({q1,q2},{q1,q2})->{q3,q4} and this provoques
     the apparition of new det_state {q3,q4}. *)

  (* Operations on det_states.
     Det states are sets of states represented here by ordered 
     lists of states, we order states by comparing their strings with > *)

  let rec det_state_add (s:state) (set: det_state)=
    match set with
	[] -> [s]
      | s1::rem -> 
	  if (State_type.to_string s) > (State_type.to_string s1) 
	  then s1::(det_state_add s rem)
	  else 
	    if (State_type.to_string s) = (State_type.to_string s1) 
	    then s1::rem
	    else s::s1::rem

  let rec det_state_union (s1: det_state) (s2: det_state)=
    match s1 with
	[] -> s2
      |s::srem -> det_state_add s (det_state_union srem s2)

  (* union of det_state sets (lists) *)

  let rec list_union l1 l2=
    match l1 with
	[] -> l2
      |s::lrem -> 
	 let union_rem= list_union lrem l2 in
	   if List.mem s union_rem then union_rem else s::union_rem

  let det_state_equal = (=)


  (* is a state member of a det_state (set of states) *)
			  
  let det_state_mem = List.mem


  (* is a det_state included in another i.e., is it less general *)

  let rec det_state_is_included (ds1: det_state) (ds2:det_state)=
    match ds1,ds2 with
	[],_ -> true
      | _,[] -> false
      | s1::rem1, s2::rem2 -> 
	  if (State_type.to_string s1)= (State_type.to_string s2)
	  then det_state_is_included rem1 rem2
	  else det_state_is_included (s1::rem1) rem2

	    
  (* det transition constructor *)      

  let make_det_trans sym largs state= (sym, largs, state)

  (* and destructor (or accessors) *)
					
  let det_trans_symbol t =
    match t with (sym, _, _) -> sym

  let det_trans_args t =
    match t with (_, args, _) -> args

  let det_trans_state t =
    match t with (_, _, state) -> state


  let det_state_to_string s= "{"^(List.fold_right (function a -> function b -> 
						     ((State_type.to_string a)^" "^b)) s "}")

  let det_state_list_to_string ls= List.fold_right (function a -> function b -> 
						      ((det_state_to_string a)^" "^b)) ls ""

  let det_trans_to_string (symb, largs, state)= 
    (Symbol_type.to_string symb)^"( "^(det_state_list_to_string largs)^") -> "^(det_state_to_string state)
    
  (* adding a transition to a deterministic set of transitions (folder). 

     When adding transition (b) after having added transition (a)
     both are merged into f({q1,q2},{q1,q2})->{q3,q4} and this provoques
     the apparition of new det_state {q3,q4}. *)

  let add_det_trans (t: det_trans) (folder: (symbol, det_trans list)folder)  =
    (*      let _= print_string ("Adding "^(det_trans_to_string t)^"\n") in *)
    let rec aux t ltrans new_trans=
      match t,ltrans with
	  (_,_,ds1), [] -> (t::new_trans, [ds1])
	      
	| (sym1, l1, ds1), (_, l2, ds2)::rem when l1=l2 ->
	    if det_state_is_included ds1 ds2 then (new_trans@ltrans, [])
	    else 
	      let new_det_state= det_state_union ds1 ds2 in
		(* let _=print_string ("gives: "^(det_trans_to_string (sym1, l1, new_det_state))^"\n\n") in *)
		(new_trans@[(sym1, l1, new_det_state)]@rem, [new_det_state])
		
	| _, t2::rem -> aux t rem (t2::new_trans)
    in 
    let symb= det_trans_symbol t in
    let (new_trans, new_det_states) = (aux t (try List.assoc symb folder
					      with Not_found -> []) []) in
      (folder_replace new_trans symb folder, new_det_states)
      

  (* adding a list of transition to a deterministic set of transitions *)

  let add_all_det_trans (ltrans: det_trans list) (folder: (symbol, det_trans list)folder)=
    let rec aux ltrans folder new_states=
      match ltrans with
	  [] -> (folder, new_states)
	| t::rem -> 
	    let (new_delta, first_new_states)= add_det_trans t folder in
	      aux rem new_delta (list_union first_new_states new_states)

    in aux ltrans folder []

  (* all combinations of several lists 
     
     all_combinations : 'a list list -> 'a list list 

     example: 
     all_combinations [[1];[2;3];[4]];;
     - : int list list = [[1; 2; 4]; [1; 3; 4]] *)


  let rec all_combinations l=
    let rec add_one_of (l1: 'a list) (l2: 'a list list)=
      match l1 with
	  [] -> []
	| elt::lrem -> (List.map (function x -> elt::x) l2)@(add_one_of lrem l2)
    in
      match l with
	  [] -> [[]]
	| first_comb::lrem -> 
	    let rem_combinations= all_combinations lrem in
	      add_one_of first_comb rem_combinations


  (* instanciating a transition by all possible and corresponding deterministic states. *)

  let instanciate (t: det_trans) (l: det_state list)=
    let symb= (det_trans_symbol t) and dest_state= (det_trans_state t) in
    let rec get_det_states_containing (s: det_state) (l: det_state list)=
      match l with 
	  [] -> []
	| s2::lrem -> 
	    if det_state_is_included s s2 then s2::(get_det_states_containing s lrem) 
	    else (get_det_states_containing s lrem) 
    in 
      if (det_trans_args t) = [] then [t]
      else 
	let all_possible_cases= List.map (function s -> (get_det_states_containing s l)) (det_trans_args t) in
	  if List.for_all (function x -> not (x=[])) all_possible_cases 
	  then (List.map (function x -> (symb, x, dest_state)) (all_combinations all_possible_cases))
	  else []


  (* translating a transition into a deterministic transition *)

  let trans_to_det_trans (t: Transition_type.rule)=
    let the_lhs= Transition_type.lhs t in
      (Configuration_type.top_symbol the_lhs, List.map (function x -> [x]) 
	 (Configuration_type.list_arguments the_lhs), [Transition_type.rhs t])

  (* list of states of a det_trans list *)
      (*
	let rec states_of_det_trans ltrans=
	match ltrans with 
	[] -> []
	| (_,largs,state)::rem -> 
	let rem_states= list_union largs (states_of_det_trans rem) in	      
	if List.mem state rem_states then rem_states
	else state::rem_states
      *)
      


  (* constructing the maping from det_states to new_states. Gives a pair
     constituted by the maping and the new state_ops *)
      
  let rec states_for_det_states ldet i=
    match ldet with
	[] -> ([], Alphabet_type.new_alphabet)
      | ds::rem -> 
	  let (maping, alphabet)= states_for_det_states rem (i+1) in
	  let symbol= Symbol_type.of_string (default_state_label^(string_of_int i)) in
	  let state= Const(symbol) in
	    ((ds, state)::maping, Alphabet_type.add_symbol symbol 0 alphabet)

  (* applying the maping on a given det_states. The result is the
     corresponding state in the maping *)

  let state_for_det_state maping s=
    try List.assoc s maping with Not_found -> failwith ("Automata determinisation: maping of deterministic states to normal states is incomplete. No mapping for state: {"^(List.fold_right (function a-> function b -> ((State_type.to_string a)^" "^b)) s "}")) 

  (* Constructing the set of final states from the initial set of final
     states and the maping: a det_state is final if at least one state
     it contains is final *)

  let rec det_final final_states maping=
    let rec aux s maping=
      match maping with
	  [] -> State_set_type.empty
	| (ds, s2)::lrem -> 
	    if det_state_mem (Special s) ds 
	    then State_set_type.add s2 (aux s lrem)
	    else (aux s lrem)
    in
      if State_set_type.is_empty final_states then State_set_type.empty
      else 
	let first_final= aux (State_set_type.first final_states) maping in
	  State_set_type.union first_final (det_final (State_set_type.remainder final_states) maping)
	    

  (* The determinisation function: given a tree automaton it gives an
     equivalent deterministic one (it may need to be cleant) *)
	    
  let determinise (a: tree_automata)=
    let rec det_trans_to_trans (ltrans: det_trans list) maping=
      match ltrans with
	  [] -> Transition_type.empty
	| (sym, largs, state)::lrem -> 
	    Transition_type.add
	      (new_trans sym (List.map (state_for_det_state maping) largs) 
		 (state_for_det_state maping state)) (det_trans_to_trans lrem maping)
    in
      
    let init_trans= (List.map trans_to_det_trans (Transition_type.to_list (get_transitions a))) in
    let rec aux (ltrans: det_trans list) (new_trans: (symbol, det_trans list)folder) 
      (new_states: det_state list) (added: bool)=
      match ltrans with 
	  [] -> 
	    if not added then 
	      let flat_trans= folder_flatten new_trans in
	      let (maping, state_ops)= states_for_det_states new_states 0 in
		(*		let _= List.iter (function (a,b) -> 
				begin (List.iter (function s -> (print_string ((State_type.to_string s)^" "))) a);
				(print_string ("-> "^(State_type.to_string b)^"\n")) end) maping in *)
	      let trans= det_trans_to_trans flat_trans maping in
	      let states= states_of_transitions trans in
	      let final= det_final (get_final_states a) maping in
		make_automaton (get_alphabet a) state_ops states final Transition_type.empty trans 
		  
	    else 
	      aux init_trans new_trans new_states false
	| one_trans::rem ->
	    let possible_trans= instanciate one_trans new_states in
	    let (incremented_new_trans, other_new_states)=
	      add_all_det_trans possible_trans new_trans in
	      aux rem incremented_new_trans (list_union other_new_states new_states) 
		((not (other_new_states = [])) or added)
		
    in aux init_trans [] [] false
	 
  (* Completion of a tree automata A: i.e. add transitions and states to
     A such that for every term t \in T(F) \exists q\inQ such that 
     t ->*A q *)

  (* construction of a list of i elt *)

  let rec make_list elt i=
    if i=0 then [] else elt::(make_list elt (i - 1)) 
      

  (* Construction of a set of transition recognising T(F) in state q, i.e. for all f\in F
     creating a transition f(q, ..., q) -> q *)

  let rec makeTF (alphabet: ((symbol * int) list)) (state: state)=
    match alphabet with
	[] -> Transition_type.empty
      |(sym,arity)::rem_alpha -> 
	 Transition_type.add_fast (new_trans sym (make_list state arity) state)
	   (makeTF rem_alpha state)
	   
  (* Completion of tree automaton... in a non-deterministic way i.e.,
     the result is a non-deterministic tree automaton. If a
     deterministic one is needed, it needs to be determinised afterwards
  *)   

  let make_complete a=
    let dead_symbol= (Symbol_type.of_string default_bottom_label) in
    let alphabet= get_alphabet a in
    let state_ops= get_state_ops a in
      if Alphabet_type.occur dead_symbol alphabet
      then raise (Multiply_defined_symbol ("the bottom symbol:"^default_bottom_label^" already occurs in the alphabet!"))
      else 
	if Alphabet_type.occur dead_symbol state_ops
	then raise (Multiply_defined_symbol ("the bottom symbol:"^default_bottom_label^" already occurs in state operators!"))
	else
	  let dead_state= (make_state dead_symbol) in
	  let transTF= makeTF (Alphabet_type.to_list alphabet) dead_state in
	    make_automaton alphabet (Alphabet_type.add_symbol dead_symbol 0 state_ops)
	      (State_set_type.add dead_state a.states) a.final_states a.prior 
	      (Transition_type.union transTF a.transitions)

  (* construction of an automaton recognising reducible terms *)

  (* function that produces [[a;b;b;b][b;a;b;b][b;b;a;b][b;b;b;a]] from [b;b;b] and a *)

  let list_perm l elt=
    let rec turn l sols=
      if List.hd l = elt then l::sols
      else turn ((List.tl l)@[(List.hd l)]) (l::sols)
    in turn (l@[elt]) []
	 
  (* produced all rules for a symbol symb of arity i recognising a term rooted by symb with
     at least one term recognised by state red_state (i.e. at least one reducible subterm) *)

  let make_red_trans symb i red_state tf_state=
    if i<1 then Transition_type.empty
    else 
      Transition_type.list_to_trs (List.map (function largs -> new_trans symb largs red_state)
				     (list_perm (make_list tf_state (i - 1)) red_state))
	
  let rec make_red_trs (alphabet: ((symbol * int) list)) (red_state: state) (tf_state: state)=
    match alphabet with
	[] -> Transition_type.empty
      | (sym, arity)::rem_alpha ->
	  Transition_type.union_fast (make_red_trans sym arity red_state tf_state) 
	    (make_red_trs rem_alpha red_state tf_state)

  let make_red_automaton (alphabet: Alphabet_type.t) (trs: TRS_type.t)=
    if not ((TRS_type.non_linear_lhs trs) = []) then
      raise (Linearity_problem "make_red_automaton: cannot construct from a non left linear trs!")
    else
      let tf_symbol= (Symbol_type.of_string default_tf_label) in
      let red_symbol= (Symbol_type.of_string default_red_label) in
	if Alphabet_type.occur tf_symbol alphabet 
	then raise (Multiply_defined_symbol ("default bottom label: "^default_tf_label^" already occurs in alphabet"))
	else
	  if Alphabet_type.occur red_symbol alphabet 
	  then raise (Multiply_defined_symbol ("default reducible label: "^default_red_label^" already occurs in alphabet"))
	  else 
	    let tf_state= make_state tf_symbol and red_state= make_state red_symbol in
	    let red_state_config= make_state_config red_state and tf_state_config= make_state_config tf_state in
	    let context_rules= Transition_type.union_fast 
				 (makeTF (Alphabet_type.to_list alphabet) tf_state)
				 (make_red_trs (Alphabet_type.to_list alphabet) red_state tf_state) in
	    let list_of_lhs= List.map TRS_type.lhs (TRS_type.to_list trs) in
	    let list_of_variables= 
	      List.fold_right (function a -> function b -> list_union (Configuration_type.list_variables a) b) list_of_lhs [] in
	    let substitution= List.map (function x -> (x, tf_state_config)) list_of_variables in
	    let non_normalised_trans_to_add= 
	      Transition_type.list_to_trs
		(List.map (function t ->  Transition_type.new_rule 
			       (Configuration_type.apply substitution t) red_state_config) list_of_lhs) in
	    let (normalised_trans_to_add, _, state_ops)= 
	      normalize non_normalised_trans_to_add Transition_type.empty default_state_label 0 in
	    let states= State_set_type.add tf_state 
			  (State_set_type.add red_state (states_of_transitions normalised_trans_to_add)) in
	    let final= State_set_type.add red_state (State_set_type.empty) in
	      make_automaton alphabet 
		(Alphabet_type.add_symbol tf_symbol 0 (Alphabet_type.add_symbol red_symbol 0 state_ops))
		states final Transition_type.empty 
		(Transition_type.union context_rules normalised_trans_to_add)
		

  (* The complement operation. *)	
 	
  let inverse a=
    let det_complete= (determinise (make_complete a)) in
      modify_final det_complete (State_set_type.minus det_complete.states det_complete.final_states)

  (* The automaton recognizing the subtraction of langages: subtract L(a2) to L(a1)  *)
	
  let subtract a1 a2= simplify (inter a1 (inverse a2))


  (* Decision of inclusion between two langages: is L(a1) included in L(a2)? *)

  let is_included a1 a2= is_language_empty (inter (inverse a2) a1)


  (* Production of the automaton recognizing normal form w.r.t. a TRS r *)

  let nf_automaton (alpha:alphabet) (r:transition_table)= 
    if Transition_type.is_empty r 
    then (make_red_automaton alpha Transition_type.empty) 
    else inverse (make_red_automaton alpha r)


  (* Similar but optimized version. The optimisation is really simple but usually gives 
     better results in practice. We simply compute a [nf_automaton] for each rewrite rule 
     and then intersect all the obtained automata in order to obtain the automaton for the 
     whole system. *)

  let rec nf_opt (alpha:alphabet) (r:transition_table)=
    if Transition_type.is_empty r
    then (make_red_automaton alpha Transition_type.empty) 
    else
      if (Transition_type.is_empty (Transition_type.remainder r)) 
      then simplify (nf_automaton alpha r)
      else 
	let nf_rem= nf_opt alpha (Transition_type.remainder r) in
	let nf_first= simplify (nf_automaton alpha (Transition_type.list_to_trs [Transition_type.first r])) in
	  simplify (inter nf_first nf_rem)

end



