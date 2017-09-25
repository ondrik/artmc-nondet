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

module Gamma 
  (Symbol_type: PRINTABLE_TYPE)(Alphabet_type: ALPHABET_TYPE with type symbol= Symbol_type.t)
  (Variable: PRINTABLE_TYPE)
  (Variable_set_type: VARIABLE_SET_TYPE with type variable= Variable.t)
  (Term: TERM_TYPE with type symbol= Symbol_type.t 
		   and type alphabet= Alphabet_type.t
		   and type variable_set= Variable_set_type.t
		   and type variable=Variable.t)
  (TRS_type: TRS_TYPE with type alphabet= Alphabet_type.t 
		      and type term= Term.t
		      and type variable_set= Variable_set_type.t)
  (State_set_type: STATE_SET_TYPE with type state= Term.t
				  and type alphabet= Alphabet_type.t 
				  and type symbol= Symbol_type.t)
  (Automata_type: AUTOMATA_TYPE with type symbol= Symbol_type.t 
				and type alphabet= Alphabet_type.t 
				and type substitution= Term.substitution
				and type term= Term.term 
				and type state= Term.term
				and type transition_table= TRS_type.t 
				and type rule= TRS_type.rule
				and type state_set= State_set_type.t)=

struct
  module State_type= Term
  module Trans_type= TRS_type

  (*  channels for user interaction *)

  let out_chan= ref stdout
  let in_chan= ref stdin

  type automaton = Automata_type.t
  type alphabet = Alphabet_type.t
  type state = Automata_type.state
  type transition_table = Trans_type.t
  type transition = Trans_type.rule
  type variable_set= Variable_set_type.t
  type variable= Variable.t
  type substitution= Term.substitution
  type ('a, 'b) folder= ('a, 'b) Automata_type.folder
  type symbol= Symbol_type.t
  type rule= Trans_type.rule
  type trs= TRS_type.t
  type term= Term.t
  type sol_filt= Automata_type.sol_filt

  type equation = {lhs: term; rhs: term}
  type norm_rule = {pat:transition; modifs: transition_table}
  type state_set = State_set_type.t
  type gamma_content= {prior: transition_table; new_states:alphabet; 
		       norm_rules: norm_rule list; strategy: string list; equations: equation list}
  open Automata_type
			
  exception Multiply_defined_symbol of string
  exception Error_in_parsing of string
  exception Badly_formed_term of string
  exception Strategy_error of string 
  exception Normalisation_error of string
  exception Terms_do_not_semiunify of string * string

  let is_empty g= g.norm_rules = [] && g.equations= [] 

  let equation_to_string e= (Term.to_string e.lhs)^" = "^(Term.to_string e.rhs)
  let rec equations_to_string (e: equation list)= 
    match e with 
	[] -> ""
      | e1::rem -> (equation_to_string e1)^"\n"^(equations_to_string rem)

  let variable_renaming_string = "#var_rn#"
  let variable_top_state_string = "#qrule#"
  let variable_sep= '|'


  (* clock like characters for showing static compilation processing *)

  let clock_char= ref '|'
  let init_clock ()= 
    begin
      Printf.fprintf !out_chan "%c" ' ';
      Printf.fprintf !out_chan "%c" !clock_char;
      Printf.fprintf !out_chan "%c" ' ';
      flush !out_chan
    end

  let next_clock ()=
    let new_char=
      match !clock_char with
	  '|' -> '/'
	| '/' -> '-'
	| '-' -> '\\'
	| '\\' -> '|'
	| _ -> '|'
    in 
      Printf.fprintf !out_chan "%c" '\b';
      Printf.fprintf !out_chan "%c" '\b';
      Printf.fprintf !out_chan "%c" '\b';
      Printf.fprintf !out_chan "%c" ' ';
      Printf.fprintf !out_chan "%c" new_char;
      Printf.fprintf !out_chan "%c" ' ';
      clock_char:= new_char;
      flush !out_chan

  (* Variable set for parsing only...*)

  let varset= ref Variable_set_type.empty

  (* List of produced epsilon transitions *)

  let epsilon_trans = ref [[]]
  let reinit_epsilon () = begin epsilon_trans:=[[]] end
  let previous_epsilon () = 
    begin 
      if not (!epsilon_trans = []) 
      then epsilon_trans:= List.tl !epsilon_trans 
    end
  let next_epsilon () = begin epsilon_trans:= []::!epsilon_trans end
  

  (* Solver for equality and disequality constraints built on litterals [x=q] and with connectives
     [and], [or], [not] *)
		    
  (* checks if an equality [+] or a disequality [-] is coherent with a list of equality and diseq *)
		    
  let rec sat (sign: char) (v: term) (t1: term) (c: ((term * (char * term)) list)): bool=
    match c with 
	[] -> true
      | (x, (s2, t2))::rem -> 
	  if x= v
	  then
	    if sign='+' then
	      if s2='+' then 
		if t1=t2 
		then sat sign v t1 rem
		else false
	      else 
		if t1= t2 
		then false
		else sat sign v t1 rem
	    else 
	      if s2= '+'then 
		if t1=t2 
		then false
		else sat sign v t1 rem
	      else sat sign v t1 rem
		
	  else sat sign v t1 rem
	    
  (* checks if a conjunction of equality and disequality is correct and simplifies it if necessary.
     [p] should be in disjunctive normal form! *)
	    
  let rec simplif (p: sol_filt) (seen: (term * (char * term)) list): (sol_filt *  ((term * (char * term)) list))=     match p with 
      And(a, b) -> 
	let (v,l) = (simplif a seen) in
	  if v= Bottom
	  then (Bottom, [])
	  else
	    let (v2, l2) = (simplif b l) in
	      if v2= Bottom 
	      then (Bottom, [])
	      else 
		if v= Empty then (v2, l2)
		else 
		  if v2= Empty then (v, l2)
		  else (And(v, v2), l2)

    | Empty -> (Empty, seen)
    | Bottom -> (Bottom, [])
    | Not(S(x, t)) -> 
	if (Term.equal x t) 
	then
	  (Bottom, [])
	else 
	  if (List.mem (x, ('-', t)) seen)
	  then (Empty, seen)
	  else 
	    if (sat '-' x t seen) then 
	      (Not(S(x, t)), (x, ('-', t))::seen)
	    else 
	      (Bottom, [])
    | S(x, t) -> 
	if (List.mem (x, ('+', t)) seen)
	then (Empty, seen)
	else 
	  if (sat '+' x t seen) then 
	    (S(x, t), (x, ('+', t))::seen)
	  else 
	    (Bottom, [])
    | Or(_,_) -> failwith "simplif is applied to a formula that is not in DNF: found OR under AND!"
    | Not(_) ->  failwith "simplif is applied to a formula that is not in DNF: found NOT above AND or OR!"


  (* Find if there is a positive constraint in c (under some And eventually) for one of the variables in l *)
	
  let rec const_find (l: variable list) (c: sol_filt): (variable * term) list=
    match c with
	And(a, b) ->
	  (const_find l a)@(const_find l b)
      | S(Var(x), t) -> 
	  if List.mem x l 
	  then [(x, t)]
	  else []
      | _ -> [] 


  (* [pos_constrained] look for a positive constraint on a variable x *) 
	
  let rec pos_constrained (x: term) (seen:  (term * (char * term)) list): bool=
    match seen with
	[] -> false
      |(y, ('+', _))::rem  ->
	 if Term.equal x y then true
	 else pos_constrained x rem
      |e::rem -> pos_constrained x rem


  (* [simplif2]  remove every equation of the form x=/=a if there is at least one x=b *)

  let rec simplif2 (p: sol_filt) (seen: (term * (char * term)) list): sol_filt=     
    match p with 
	And(a, b) -> 
	  let v1 = (simplif2 a seen) in
	  let v2 = (simplif2 b seen) in
	    if v1= Empty then v2
	    else 
	      if v2= Empty then v1
	      else And(v1, v2)

      | Empty -> Empty
      | Bottom -> Bottom
      | Not(S(x, t)) -> 
	  if pos_constrained x seen
	  then Empty
	  else p
      | S(x, t) -> p
      | Or(_,_) -> failwith "simplif2 is applied to a formula that is not in DNF: found OR under AND!"
      | Not(_) ->  failwith "simplif2 is applied to a formula that is not in DNF: found NOT above AND or OR!"


  (* propagation of disequalities and equalities in [p]... [p] is supposed to be in DNF *) 

  let rec propag_diseq (p: sol_filt): sol_filt=
    match p with
	Empty -> Empty
      | Bottom -> Bottom
      | S(x,t) -> S(x,t)
      | And(a, b) -> 
	  let (v, s) = simplif(And(a, b)) [] in 
	    (*	  v *)
	    simplif2 v s
      | Or(a, b) -> Or(propag_diseq a, propag_diseq b)
      | Not(S(x, t)) -> 	if Term.equal x t then Bottom else Not(S(x, t))
      | Not(Empty) -> Bottom
      | Not(Bottom) -> Empty
      | Not(_) -> failwith "Problem in diseq propagation: not in disjunctive normal form!"

  let eq_solve (p: sol_filt): sol_filt=
    Automata_type.simplify_sol(propag_diseq (Automata_type.simplify_sol(Automata_type.dnf p)))
      

  (* Transformation of a substitution into a constraint *)

  let rec subst_to_const (s: substitution): sol_filt=
    match s with 
	[] -> Empty
      | (x,t)::rem -> And(S(Var(x),t), subst_to_const rem)


  (* The empty gamma approximation content with the default strategy ! *)
	  
  let empty= {prior=Trans_type.empty; new_states=Alphabet_type.new_alphabet; norm_rules=[];
	      strategy= ["prior"; "norm_rules"; "manual_conf"; "auto_conf"]; equations=[]}

  let add_prior_to_gamma ltrans (g: gamma_content)= {prior= Trans_type.union ltrans g.prior;
						     new_states= g.new_states;
						     norm_rules= g.norm_rules;
						     strategy=g.strategy; equations= g.equations}
  let set_prior_in_gamma ltrans (g: gamma_content)= {prior= ltrans; 
						     new_states= g.new_states;
						     norm_rules= g.norm_rules;
						     strategy=g.strategy; equations= g.equations}
  let get_prior g= g.prior
  let get_new_states g= g.new_states
  let get_norm_rules g= g.norm_rules
  let new_norm_rule pat rules= {pat=pat; modifs= rules}
  let set_norm_rules lrules (g: gamma_content)= {prior= g.prior; new_states= g.new_states;
						 norm_rules= lrules;
						 strategy=g.strategy; equations= g.equations}
  let set_new_states state_ops (g: gamma_content)= {prior= g.prior; new_states= state_ops;
						    norm_rules= g.norm_rules;
						    strategy=g.strategy; equations= g.equations}
  let get_strategy (g: gamma_content)= g.strategy
  let set_strategy (strat: string list) (g: gamma_content)= 
    {prior= g.prior; new_states= g.new_states;
     norm_rules= g.norm_rules;
     strategy= strat; equations= g.equations}

  let get_equations (g: gamma_content)= g.equations
  let set_equations (eq: equation list) (g: gamma_content)= 
    {prior= g.prior; new_states= g.new_states;
     norm_rules= g.norm_rules;
     strategy= g.strategy; equations= eq}

  let eq_lhs e= e.lhs
  let eq_rhs e= e.rhs

  let rec go()= 
    (Printf.fprintf !out_chan "%s" "(y/n)? ";
     flush !out_chan;
     let rep= input_line !in_chan in
       match rep with
	   "y"|"Y"|"YES"|"yes"|"Yes" -> true
	 | "n"|"N"|"NO"|"No"|"no" -> false
	 | _ -> 
	     (Printf.fprintf !out_chan "%s" "Answer by ";
	      flush !out_chan;
	      go()))
    
    
    
  (* the lexer for adding rules interactively *)	

  let lexer = Genlex.make_lexer [",";"(";")";"->";"."; "*"; "States";"Rules";"Top";"[";"]";":"]

  (* the parser for adding rules interactively the result is a triple (trans, prior, new_states_ops) where
     new state_ops are the new states defined for the description of the normalising rules, and prior is a SUBSET
     of trans, such that this subset is to be added to the prior field of the gamma_content *)


  let rec parse_user_transitions alphabet state_ops= 
    let (new_trans, new_prior, new_ops)= try (parse_user_aux alphabet state_ops (lexer (Stream.of_channel !in_chan))) with
	Multiply_defined_symbol(m) -> 
	  begin
	    Printf.fprintf !out_chan "%s" ("\nBe careful: "^m^", try again:\n");
	    flush !out_chan;
	    parse_user_transitions alphabet state_ops
	  end
	  
      | Stream.Error s -> 
	  begin
	    Printf.fprintf !out_chan "%s" ("\n\nSyntax error, try again\n"^s); 
	    flush !out_chan;
	    parse_user_transitions alphabet state_ops
	  end
      | Term.Undefined_symbol(f) -> 
	  begin Printf.fprintf !out_chan "%s" ("\n\nError: Symbol "^f^" is undefined, try again\n"); 
	    flush !out_chan;
	    parse_user_transitions alphabet state_ops
	  end
      | Term.Badly_formed_term(f) -> 
	  begin
	    Printf.fprintf !out_chan "%s" ("\n\nError: Bad term syntax! "^f^", try again\n"); 
	    flush !out_chan;
	    parse_user_transitions alphabet state_ops
	  end
      | TRS_type.Badly_formed_rule(f) -> 
	  begin
	    Printf.fprintf !out_chan "%s" ("\n\nError: Bad rule syntax! "^f^", try again \n");
	    flush !out_chan;
	    parse_user_transitions alphabet state_ops
	  end
      | _ -> 
	  begin
	    Printf.fprintf !out_chan "%s" "Syntax error, try again!\n"; 
	    flush !out_chan;
	    parse_user_transitions alphabet state_ops
	  end
    in 
      if List.for_all Automata_type.is_normalized (Trans_type.to_list new_prior) then (new_trans, new_prior, new_ops)
      else 
	begin
	  Printf.fprintf !out_chan "%s" "\nUser prior transtions should be normalized!! \ni.e. of the form f(q1, ..., qn) -> q' or a -> q' if a is a constant tymbol\nTry again:\n";
	  flush !out_chan;
	  parse_user_transitions alphabet state_ops
	end

	
  and parse_user_aux alphabet state_ops=
    parser
	[< 'Genlex.Kwd "States"; new_state_ops= State_set_type.parse_ops;
	   'Genlex.Kwd ".";
	   (trans, prior)= parse_transitions alphabet (Alphabet_type.union state_ops new_state_ops) 
	                     Trans_type.empty Trans_type.empty>] -> 
	  if Alphabet_type.disjoint alphabet new_state_ops then (trans, prior, new_state_ops)
	  else raise (Multiply_defined_symbol "states and symbols are not disjoint")
      | [< (trans, prior) = parse_transitions alphabet state_ops Trans_type.empty Trans_type.empty>] 
	-> (trans, prior, Alphabet_type.new_alphabet)
	  
  and (parse_transitions: alphabet -> alphabet -> Trans_type.t -> Trans_type.t -> Genlex.token Stream.t
	 -> (Trans_type.t * Trans_type.t))= 
    function alphabet -> function state_ops -> function (trans: Trans_type.t) -> function (prior: Trans_type.t) -> parser
	[< 'Genlex.Kwd "." >] -> (trans, prior)
      |	[< 'Genlex.Kwd "*"; one_prior= Trans_type.parse_ground_special_rule alphabet state_ops;
	   remainder= parse_transitions alphabet state_ops (Trans_type.add one_prior trans) 
			(Trans_type.add one_prior prior)>] -> remainder
      | [< one_trans= Trans_type.parse_ground_special_rule alphabet state_ops;
	   remainder=  parse_transitions alphabet state_ops (Trans_type.add one_trans trans) 
			 prior>] -> remainder


  let rename_norm_rule (r: norm_rule) (s: string): norm_rule=
    {pat= TRS_type.rename_rule_var r.pat s;
     modifs= TRS_type.rename_var r.modifs s}


  let rename_norm_rule_list (rl: norm_rule list) (s: string): norm_rule list=
    List.map (function e -> rename_norm_rule e s) rl

  (* construct the list of linked vars *)
      
  (* linked variables are variables who are under the same functionnal symbol in the rhs of a rule. The "link" 
     relation is reflexive, symetric and transitive so, 

     for instance linked variables of term f(x, g(x), g(v), h(z, u, x), z) are not [[x;z]; [x]; [v]; [z;u;x]] 
     but [[x; z; u]; [v]] *)

  type var_link= ((variable list) list)

  let rec identify (lv: variable list) (l: var_link) (not_modif: var_link)
    (modifs: var_link): var_link=
    match l with 
	[] -> 
	  if modifs=[] then not_modif             (* no new equivalence found with [lv] *)
	  else (List.flatten modifs)::not_modif    (* all classes containing variables in common with [lv]
						      are gathered together *)
      | c::rem -> 
	  let intersec= Common.inter c lv in
	    if intersec = [] then 
	      identify lv rem (c::not_modif) modifs
	    else 
	      identify lv rem not_modif (c::modifs)

  let rec search_in_term (t: term) (l: var_link): var_link=
    (match t with
	 Special(_) | Const(_) | Var(_)-> l
       | Fsym(_, largs) -> 
	   let lvar= List.map (function t -> match t with Var(x) -> x | _ -> failwith "Incoherence: should be a variable term") (List.filter Term.is_variable largs) in
	     search_in_term_list largs (identify lvar l [] []) )
    
  and search_in_term_list (lt: term list) (l: var_link) : var_link=
    match lt with 
	[] -> l
      | t::rem -> 
	  search_in_term_list rem (search_in_term t l)
		   
  let get_linked_vars (t: term): var_link =
    (* modify the links between variables in [l] w.r.t. new dependances [lv]  *)
    let (list_var: var_link)= (List.map (function x -> [x]) (Common.clean (Term.list_variables t))) in
      (List.filter (function x -> ((List.length x)>1)) (search_in_term t list_var))
	 
  (* Special normalisation for gamma: rules with variable lhs like: x -> a 
     are applied only once to prevent non-termination *)

  let gamma_norm (term: Term.t) (trs: TRS_type.t)= 
    let rec aux trs=
      if TRS_type.is_empty trs 
      then (false, [])
      else 
	let first_rule= TRS_type.first trs in
	let lhs= TRS_type.lhs first_rule in
	let rhs= TRS_type.rhs first_rule in
	  if Term.is_variable lhs then (true, [rhs])
	  else aux (TRS_type.remainder trs)
    in
    let (some_var_lhs, value)= aux trs in
      if some_var_lhs then List.hd value
      else TRS_type.bottom_up_norm trs term

	
  (* look for the normalisation of a term w.r.t. to partially instanciated rewrite rules
     the result of [norm_term t trs] is a couple (t', l) where t' is a
     normalised term with the corresponding list of transitions used to normalise t in to t' *)

  let rec norm_term trs t=
    match t with
	Special(t2) -> (t, [])
      | Const(_) -> 
	  let norm= gamma_norm t trs in
	    if Term.equal t norm then (t, [])
	    else (norm, [Trans_type.new_rule t norm])
      | Fsym(f, largs) -> 
	  let norm_args_and_trans= Common.my_map (norm_term trs) largs in
	  let (normed_args, normed_trans)= List.split norm_args_and_trans in
	  let flat_trans= List.flatten normed_trans in
	  let not_top_normed= Fsym(f, normed_args) in
	  let top_normed= gamma_norm not_top_normed trs in
	    if Term.equal not_top_normed top_normed 
	    then (not_top_normed, flat_trans) 
	    else (top_normed, (Trans_type.new_rule not_top_normed top_normed)::flat_trans)
      | _ -> raise (Badly_formed_term ("Term "^(Term.to_string t)^" is not a valid configuration"))


  (* Application of a substitution to a trs *)

  let rec trs_apply (s: substitution) (r: transition_table)= 
    if TRS_type.is_empty r then r
    else
      let first= TRS_type.first r in 
	TRS_type.add (TRS_type.new_rule 
			(Term.apply_special s (TRS_type.lhs first))
			(Term.apply_special s (TRS_type.rhs first)))
	  (trs_apply s (TRS_type.remainder r))


  (* Application of several substitutions to a trs *)

  let rec trs_apply_list (sl: substitution list) (r: transition_table)= 
    match sl with
	[] -> TRS_type.empty
      | sub::rem -> TRS_type.union (trs_apply sub r) (trs_apply_list rem r)
	  

  let rec separate_ground_transitions (lt: transition list): (transition list * transition list)=
    let rec aux lt not_ground ground=
      match lt with
	  [] -> (not_ground, ground)
	| trans::rem -> 
	    if Term.is_ground (Trans_type.lhs trans)
	    then 
	      if Term.is_ground (Trans_type.rhs trans)
	      then aux rem not_ground (trans::ground)
	      else aux rem (trans::not_ground) ground
	    else aux rem (trans::not_ground) ground
    in aux lt [] []
	 

  (* normalisation of a new transition [trans] w.r.t. a [norm_rule] 
     we only normalise the lhs of the transition *)

  let norm_with_one_rule trans norm_rule=
    try (let sol1= Term.matching_special (TRS_type.lhs norm_rule.pat)(TRS_type.lhs trans) in
	 let sol2= Term.matching_special (TRS_type.rhs norm_rule.pat)(TRS_type.rhs trans) in
	 let combined_subst= Term.coherent sol1@sol2 in
	 let substituted_rules= trs_apply combined_subst norm_rule.modifs in
	 let (new_config, new_trans)= norm_term substituted_rules (TRS_type.lhs trans) in

	   (* if the result of the normalisation is a state config, this means that normalisation
	      has been performed up to the top transition, for instance transition [f(g(q1)) -> q5] if
	      normalised with a strong rule of the form: [x -> q2] gives the config q2 and set 
	      of transitions [f(q2) -> q2; g(q1) -> q2]... the first one is not necessary since 
	      if enlarges (with no use) the approximation, so we suppress it. *)

	   if Automata_type.is_state_config new_config then
	     (* new_trans *)
	     (Trans_type.new_rule 
		(Trans_type.lhs (List.hd new_trans)) (Trans_type.rhs trans))::(List.tl new_trans)	     else 
	       (Trans_type.new_rule new_config (Trans_type.rhs trans))::new_trans)
    with Term.Terms_do_not_match(_,_) -> [trans]


  (* normalisation of a new transition [trans] w.r.t. a list of [norm_rule] *)

  let rec norm_with_norm_rules trans (nrl: norm_rule list)=
    match nrl with
	[] -> (false, Trans_type.list_to_trs [trans])
      | one_trans::lrem -> 
	  let res= norm_with_one_rule trans one_trans in
	    match res with
		[t] -> 
		  if Trans_type.rule_equal t trans
		  then norm_with_norm_rules trans lrem
		  else (true, Trans_type.list_to_trs res)
	      | _ -> (true, Trans_type.list_to_trs res)


  (* Static compilation of normalisation with a complete set of normalisation rules *)

  (* types *)
		  
  (* a branch of normalisation for a given transition to be normalised (initially in [to_do]), 
     a [transition_table] representing the normalised transitions obtained by its normalisation,
     [c] the constraint on the values of the variables contained in transitions of [to_do] and [finished]
     for the given branch,
     [current_modifs] the transition table currently applied to the [to_do] transitions to be normalised
     in case where the pattern has been successfully matched over the first transition of [to_do] *)		
		  
  type norm_branch = {to_do: transition list;
		      finished: transition list;
		      c: sol_filt;
		      norm_rules: norm_rule list}
		       
  let get_normed_trans (b: norm_branch): transition list= b.finished

  let init_norm_state (t: transition) (nr: norm_rule list): norm_branch=
    {to_do= [t];
     finished= [];
     c= Empty;
     norm_rules=nr}
    

  (* Several problems are to be tackled here: 
     1) trying to unify [f(g(v)) -> z] on a transition f(x)->q must fail!... since during completion,
     we are sure that x will be replaced by a state!. However, [f(g(q')) -> z]  may unify with f(x)->q
     
     2) when normalising f(g(x), g(y)) -> q with [f(u,v) -> z] -> [u -> q], we obtain a set of modifiers 
     which is [g(x) ->q] where x should be seen as a state constant! Hence g(y) should be normalised 
     with g(x) -> q if and only if x=y... *)

  (* Semi unification of term1 on term2: variables of term2 can only match Special terms!
     No unification into Special terms. Variables of term1 and term2 
     are to be disjoint.
     Semi-unification produces to substitution [s1] and [s2] (one for each term) such that
     [term1 s1 = term2 s2].  Equalities between variables only occur in the first one.
     [varl] is the list of the variables of the term [t] on which we are trying to achieve normalisation. 
     Hence, [term2] is a subterm of [t] and so is its list of variables. If a variable of [term1] occurs
     in [varl] it should be seen as a "constant" *)


  let semi_unify term1 term2 (varl :variable list): (substitution * substitution) = 
    let rec semi_aux term1 term2: (substitution * substitution)= 
      match (term1,term2) with
    	  (Const(a), Const(b)) -> 
	    if Symbol_type.equal a b 
	    then ([], []) 
	    else raise (Terms_do_not_semiunify ((Term.to_string term1),(Term.to_string term2)))
	      
	| (Fsym(f, l1),Fsym(g, l2)) -> 
	    if Symbol_type.equal f g 
	    then 
	      if l1=[] or l2=[] then failwith ("Empty list of args under an Fsym symbol in term: " ^ 
					       (Term.to_string term1)^" or "^(Term.to_string term2))
	      else 
		let (partial_s1, partial_s2)= semi_aux (List.hd l1) (List.hd l2) in
		let (partial2_s1, partial2_s2)= 
		  unify_list 
		    (Term.apply_substs_on_terms [partial_s1] (List.tl l1))
		    (Term.apply_substs_on_terms [partial_s2] (List.tl l2)) in
		  (partial_s1@partial2_s1, partial_s2@partial2_s2)
	    else raise (Terms_do_not_semiunify ((Term.to_string term1),(Term.to_string term2)))

	(* We only unify Special if they are equal: no var in them *)
	      
	|	(Special(t1), Special(t2)) -> 
		  if Term.equal t1 t2
		  then ([], [])
		  else raise (Terms_do_not_semiunify ((Term.to_string term1),(Term.to_string term2)))
		    
	| (Var(x), Var(y)) -> 
	    if List.mem x varl && not (Term.equal (Var(x)) (Var(y)))
	    then ([(x, Var(y))], [(y, Var(x))])
	    else ([(x, Var(y))], [])
	| (Var(x), t1) -> 
	    if List.mem x varl 
	    then raise (Terms_do_not_semiunify ((Term.to_string (Var(x))),(Term.to_string t1))) 
	    else ([(x, t1)], [])
	| (Special(t1), Var(x)) -> ([], [(x, Special(t1))])
	| x       -> raise (Terms_do_not_semiunify ((Term.to_string term1),(Term.to_string term2)))
	    
			  and unify_list l1 l2 = match (l1, l2) with
    			      ([], []) -> ([], [])
			    | (t1::reste1, t2::reste2) -> 
				let (partial_s1, partial_s2)= semi_aux t1 t2 in
				let (partial2_s1, partial2_s2)= 
				  unify_list 
				    (Term.apply_substs_on_terms [partial_s1] reste1)
				    (Term.apply_substs_on_terms [partial_s2] reste2) in
				  (partial_s1@partial2_s1, partial_s2@partial2_s2)

			    | x -> raise (Terms_do_not_semiunify ("Not the same number of arguments!", ""))
				
    in semi_aux term1 term2


  (* [left_inner_surred_form] tries to apply a rule [r] (with unification instead of matching)
     on a transition [t] given a constraint [c] on variables of [t]. The result is a pair [(c',l)] 
     where [c'] is Bottom if no occurrence of the left-hand side of the rule has been found.
     Otherwise [c'] is different from bottom and is the mgu between the left-hand side of the rule 
     and the innermost occurrence of a unifiable subterm. The result of the normalisation 
     of [t] is given in [l]. *) 
	 
  let left_inner_surred_form (t: transition) (r: transition) (c:sol_filt) (varl: variable list): (sol_filt*transition list)=
    let lhs= Trans_type.lhs r in 
    let rec lisf_aux (t1: term): (substitution * sol_filt * term)=
      (match t1 with
	   Special(_) 
	 | Var(_)   -> ([],Bottom, t1)
	 | Const(_) -> 
	     (try 
		let (s1, s2) = (semi_unify lhs t1 varl) in
		let const2= subst_to_const s2 in
		  if eq_solve (And (const2, c))= Bottom then ([], Bottom, t1)
		  else (s1, subst_to_const s2, (Trans_type.rhs r))
	      with Terms_do_not_semiunify(_,_) -> ([],Bottom,t1))
	 | Fsym(f, largs) -> 
	     let (s,sub_mgu, modif_largs)= lisf_aux_list largs [] in
	       if sub_mgu=Bottom
	       then 
		 (try 
		    let (s1, s2)= (semi_unify lhs t1 varl) in
		    let const2= subst_to_const s2 in
		      if eq_solve (And (const2, c))= Bottom then ([], Bottom, t1)
		      else (s1, subst_to_const s2, (Trans_type.rhs r)) 
		  with Terms_do_not_semiunify(_,_) -> ([], Bottom,t1))
	       else (* one subterm have been rewritten *)
		 (s, sub_mgu, Fsym(f, modif_largs)))


    (* Tries to find a term to rewrite in the list of term *)

    and lisf_aux_list (l: term list) (ldone: term list): (substitution * sol_filt * term list)=
      match l with 
	  [] -> ([], Bottom, ldone)
	| t::rem -> 
	    let (s, mgu, tmodif)= lisf_aux t in
	      if mgu = Bottom
	      then lisf_aux_list rem (ldone@[t])
	      else (s, mgu, (ldone@[tmodif]@rem))
		
    in
    let lhs_to_rewrite= Trans_type.lhs t in      (* we reduce under the top symbol of lhs only !! *)
      match lhs_to_rewrite with
	  Var(_)| Const(_) | Special(_) -> (Bottom, [])
	| Fsym(f, largs) ->
	    let (s, mgu, normed_list)= lisf_aux_list largs [] in
	      if mgu= Bottom 
	      then (Bottom, [])
	      else (mgu, [(Trans_type.new_rule (Fsym (f, normed_list)) (Trans_type.rhs t));
			  (Trans_type.new_rule 
			     (Term.apply s (Trans_type.lhs r))
			     (Trans_type.rhs r))])
		(* (Term.apply s (Trans_type.rhs r)))]) *)
		
  (* tail recursive append *)

  let tlr_append l1 l2=
    let rec aux l1 l2=
      match l1 with
	  [] -> l2
	| e::rem -> aux rem (e::l2)
    in
      aux (aux l1 []) l2

  (* [static_norm_trans] tries to achieve a symbolic normalisation (i.e. static normalisation) of list
     of transitions [ltrans] with a constraint [c] on the variables of transition of [ltrans] with a set
     of rewrite rules [modifs] used to find normalisation states ([minit] is the initial set of rewrite rules). 
     [current_branch] and [nrinit] are used to re-construct valid norm_branch records. [done] contains the 
     result of normalisation *)  

  let rec static_norm_trans (ltrans: transition list) (finished: transition list) (c: sol_filt) 
    (modifs: transition list) (minit: transition list) (current_branch: norm_branch) 
    (nrinit: norm_rule list) (varl: variable list): norm_branch list= 
    let _= next_clock() in 
    match c with
	Bottom -> []
      | _ -> 
	  match (ltrans, finished, modifs) with 
	      [t], [], [] -> [{to_do= current_branch.to_do;
			       finished= current_branch.finished;
			       c= c;
			       norm_rules= List.tl current_branch.norm_rules}
			     ] (* case were the transition has not been normalised by the modifs *)


	    | _, _, [] (* cases where something has been done and we cannot go further *)
	    | [], _, _ -> 
		
		(* there may remain some transitions to normalise but they are in current_branch.to_do *) 
		[{to_do= tlr_append ltrans (List.tl current_branch.to_do);
		  (* normalised transitions are put into current_branch.finished *)
		  finished= tlr_append finished current_branch.finished;
		  c= c;
		  (* we start over with the initial set of normalisation rules *)
		  norm_rules= nrinit}]

	    | t::rem, _, m::rem_modifs -> 
		if let d= Term.depth (Trans_type.lhs (List.hd ltrans)) in d=1 or d=0   (* transition is normalised *)
		then static_norm_trans rem (t::finished) c minit (* modifs? *) minit current_branch nrinit varl
		else 
		  let (const, lisf)= left_inner_surred_form t m c varl in
		    if const=Bottom 
		    then static_norm_trans ltrans finished c rem_modifs minit current_branch nrinit varl
		    else 
		      let nextsol= eq_solve (And(c, (Not(const)))) in 
			if nextsol= Bottom   (* [t] was necessarily normalised by [m] *)
			then (static_norm_trans (tlr_append lisf rem) finished (eq_solve (And(const, c))) minit minit current_branch nrinit varl)
			else 
(*
			  (static_norm_trans (lisf@rem) finished (eq_solve (And(const, c))) minit minit current_branch nrinit varl)@(static_norm_trans ltrans finished nextsol rem_modifs minit current_branch nrinit varl)
	*)

			  let (const2,_)= left_inner_surred_form t m nextsol varl in
			    if const2= Bottom
			    then (* there is no other way to normalise [t] with [m] *)
			      tlr_append
				(static_norm_trans (tlr_append lisf rem) finished (eq_solve (And(const, c))) 
				   minit minit current_branch nrinit varl)
				(static_norm_trans ltrans finished nextsol rem_modifs minit current_branch nrinit varl)
			    else (* there is another way to normalise [t] with [m]: [rem_modifs] is replaced 
				    by [modifs] i.e. we try again with the same normalisation rule. *)
			      tlr_append 
				(static_norm_trans (tlr_append lisf rem) finished (eq_solve (And(const, c))) 
				   minit minit current_branch nrinit varl)
				(static_norm_trans ltrans finished nextsol modifs minit current_branch nrinit varl)

			      
			      


  let rec static_aux (to_do: norm_branch list) (finished: norm_branch list) (nrinit: norm_rule list) (varl: variable list) : norm_branch list=
    let _= next_clock() in 
    match to_do with
	[] -> finished 
      | b::rem -> 
	  if b.to_do=[] then    (* the first branch is successfully normalised *)
	    static_aux rem (b::finished) nrinit varl (* we continue with the others *)
	  else
	    let first_trans= List.hd b.to_do in  (* if it is normalised, we continue with the others *)
	      if let d= Term.depth (Trans_type.lhs first_trans) in d=1 or d=0 
	      then static_aux ({to_do= List.tl b.to_do;
				finished= first_trans::b.finished;
				c= b.c;
				norm_rules= nrinit}::rem) finished nrinit varl
	      else 
		match b.norm_rules with
		    [] -> raise (Normalisation_error ("Set of transition: "^(Trans_type.to_string (Trans_type.list_to_trs b.to_do))^ 
						      "\ncannot be normalised by current set of normalisation rules!"))
		  | r1::remrules -> 
		      try (
			let (subsl, constl)= semi_unify (TRS_type.lhs r1.pat) (TRS_type.lhs first_trans) varl in
			let (subsr, constr)= semi_unify (TRS_type.rhs r1.pat) (TRS_type.rhs first_trans) varl in
			let unif1= subst_to_const constl in
			let unif2= subst_to_const constr in
			let simp= eq_solve (And(b.c, And(unif1, unif2))) in
			  if simp= Bottom 
			  then static_aux ({to_do= b.to_do;
					    finished= b.finished;
					    c= b.c;
					    norm_rules= remrules}::rem) finished nrinit varl
			  else 
			    let subst_modifs= Trans_type.to_list (trs_apply subsl (trs_apply subsr r1.modifs)) in
			    let norm_trans_result= 
(*			      let _= Printf.fprintf !out_chan "%s" "in!\n"; flush !out_chan in *)
			      static_norm_trans [first_trans] [] simp subst_modifs subst_modifs b nrinit varl in
(*			      let _= Printf.fprintf !out_chan "%s" "out!\n"; flush !out_chan in *)
			      
			      if norm_trans_result= []  (* if normalisation fails *)
			      then (* normalisation continues with the next rule on the same transition *)
				static_aux ({to_do=b.to_do;
					     finished=b.finished;
					     c= b.c;
					     norm_rules= remrules}::rem) finished nrinit varl
			      else 
				(* we construct the constraint for the negation of the unifier *)
				
				let simp2= eq_solve(And(b.c, Not(And(unif1, unif2)))) in
				  if simp2= Bottom 
				  then static_aux (tlr_append norm_trans_result rem) finished nrinit varl 
				  else static_aux 
				    (tlr_append norm_trans_result ({to_do= b.to_do;
							 finished= b.finished;
							 c= simp2;
							 norm_rules= remrules}::rem)) finished nrinit varl)
			
		      with Terms_do_not_semiunify(_,_) -> 
			static_aux ({to_do= b.to_do;
				     finished= b.finished;
				     c= b.c;
				     norm_rules= remrules}::rem) finished nrinit varl
			  
			  
  (* The fonction that computes the set of statically normed transitions!
     Be careful! variable names between the transition and every normalisation rule should be distinct!
     It is also the case between every couple of normalisation rules
     the set of normalisation rules should be complete with regards to the transition to normalise *)
			  
  let static_norm_one_trans (t: transition) (nr: norm_rule list): norm_branch list=
    static_aux [(init_norm_state t nr)] [] nr (tlr_append (Term.list_variables (Trans_type.lhs t))
						 (Term.list_variables (Trans_type.rhs t)))

  let get_var_set (x:variable): int=
    try(
      let st=  (Variable.to_string x) in
	(int_of_string (String.sub st 0 (String.index st variable_sep)))
    )with Not_found -> failwith "get_var_set: Problem in string variable renaming"

  let is_top_variable (x:variable): bool=
    try (
      let st=  (Variable.to_string x) in
      let pos= (String.index st variable_sep) in
	(String.sub st (pos + 1) ((String.length st) - (pos+1))) = variable_top_state_string
    ) with Not_found -> failwith "is_top_variable: Problem in string variable renaming"


  type value_table= ((variable list) * (substitution list)) list 

  let make_value_table (non_linked: variable list) (linked_vars: var_link): value_table=
	List.append 
	(List.map (function x-> ([x], [])) non_linked)
	(List.map (function x-> (x, [])) linked_vars)


  let is_new_subst (s: substitution) (vt: value_table)=
    let rec aux x t vt=      
      match vt with
	  [] -> failwith ("found a var "^(Variable.to_string x)^" that was not in the initial varset")
	| (l, subst_l)::rem -> 
	    if List.mem x l       (* Assumption (A): 
				     We assume that substitutions are always constructed s.t. variables are
				     always in the same order! *)
	                          (* i.e. we cannot receive a subst [(x,q1);(y,q2)] and later 
				     on [(y,q2);(x;q1)] *)

	    then not (List.mem s subst_l)
	    else aux x t rem 		 
    in
      match s with
	  (x, t)::_ -> aux x t vt
      | _ -> failwith ("Found an empty substitution in is_new_subst!")


  (* where there is no redundancy in vars and no state variable *)

  type rhs_data= {trans: transition list; non_linked_vars: variable list; 
		  linked_vars: var_link; rhs_vars: variable list; 
		  const: sol_filt; vt: (state * value_table) list}

  type rhs_table= rhs_data list

  let (empty_rhs_table: rhs_table)=[]

  (* constructs all possible substitutions from a list of all possible instanciation choices
     for each variable (which should occur in rhs): variable should be instanciated at least once 
     in the lhs (so that the rule can be applied) but its value is may be not necessary (if the 
     variable does not occur in the rhs! *)

  let rec all_combinations (l: value_table) (rhs_lvar: variable list): substitution list=
    match l with
	[] -> [[]]
      | (_, [])::rem -> []
      | (lvar, subst_list)::rem ->
	  if (List.length lvar) =1 && not (List.mem (List.hd lvar) rhs_lvar) 
	  then
	    all_combinations rem rhs_lvar
	  else 
	    let (rem_substs: substitution list)= all_combinations rem rhs_lvar in
	      if rem_substs= [] 
	      then []
	      else
		List.flatten(List.map (function (s: substitution) -> 
					 List.map (function (sl: substitution) -> List.append s sl) rem_substs) subst_list)


  let rec value_table_add (x: variable) (s: substitution) (vt: value_table): value_table=
    match vt with
	[] -> failwith ("value_table_add: Variable "^(Variable.to_string x)^" not in the value table!")
      | (lvar, lsubst)::rem -> 
	  if List.mem x lvar 
	  then (lvar, s::lsubst)::rem
	  else (lvar, lsubst)::(value_table_add x s rem)

  let rec value_table_get (x: variable) (vt: value_table): substitution list=
    match vt with
	[] -> failwith ("value_table_get: Variable "^(Variable.to_string x)^" not in the value table!")
      | (lvar, lsubst)::rem ->
	   if List.mem x lvar 
	   then lsubst
	   else (value_table_get x rem)


  let rec value_table_modif (x: variable) (s:substitution) (vt: value_table): value_table=
    match vt with
	[] -> failwith ("value_table_modif: Variable "^(Variable.to_string x)^" not in the value table!")
      | (lvar, lsubst)::rem ->
	   if List.mem x lvar 
	   then (lvar, [s])::rem
	   else (lvar, lsubst)::(value_table_modif x s rem)


  (* the function that produces list combination of all susbts *)
	     
  (* Before producing new_substitution, we propagate non linearity constraints: substitutions associated
     to several occurences of a non linear variable are intersected before production. This should not
     be done on the value table of the static rule itself because non matching substitutions at completion
     step i may become matching a step i+1 *) 

  let produce_substs (l: value_table) (rhs_lvar: variable list): substitution list=
    all_combinations l rhs_lvar
      (* (propag_non_linearity (prepare_propag l [] []) [])  *)


  (* The function that given a state variable, a state, a substitution
     and a rhs_table produces a list of new transition and an updated rhs_table *)

  let produce_new_transition (qvar: variable) (q: state) 
    (s: substitution) (d: rhs_data): (transition_table * rhs_data)=
    match s with 
	[] ->            (* lhs is ground! *)
	  if List.mem_assoc q d.vt 
	  then (TRS_type.empty, d)   (* rhs has already been added for this q, so nothing to be done *)
	  else 
	    let new_vtq= [] in
	    let new_substs= produce_substs (([qvar], [[(qvar,q)]])::new_vtq) (qvar::d.rhs_vars) in
	    let new_trans= trs_apply_list new_substs (Trans_type.list_to_trs d.trans) in
	      (* if there is at least one application of the rule, ground sub-transitions are not 
		 to be added ONCE, so they are retrieved from d.trans *)
	    let filtered_trans= 
	      if new_substs = [] then d.trans 
	      else List.filter (function t -> not (Trans_type.is_ground t)) d.trans in

	      (new_trans, {trans= filtered_trans;
			   non_linked_vars= d.non_linked_vars;
			   linked_vars= d.linked_vars;
			   rhs_vars= d.rhs_vars;
			   const= d.const;
			   vt= (q, new_vtq)::d.vt})
      |	(x, t)::rem -> 
	  let vtq= try (List.assoc q d.vt) with Not_found -> [] in
	    if vtq=[] (* there is no value table for q yet *)
	    then
	      let new_vtq= value_table_add x s (make_value_table d.non_linked_vars d.linked_vars) in
	      let new_substs= produce_substs (([qvar], [[(qvar,q)]])::new_vtq) (qvar::d.rhs_vars) in 
	      let only_correct= 
		List.filter (function s2 -> not((eq_solve (And (d.const, (subst_to_const s2))))=Bottom))
		  new_substs
	      in
		(* if there is at least one application of the rule, ground sub-transitions are not 
		   to be added ONCE, so they are retrieved from d.trans *)
	      let filtered_trans= 
		if only_correct = [] then d.trans 
		else List.filter (function t -> not (Trans_type.is_ground t)) d.trans in
		
	      let new_trans= trs_apply_list only_correct (Trans_type.list_to_trs d.trans) in
		(new_trans, {trans= filtered_trans;
			     non_linked_vars= d.non_linked_vars;
			     linked_vars= d.linked_vars;
			     rhs_vars= d.rhs_vars;
			     const= d.const;
			     vt= (q, new_vtq)::d.vt})
	    else (* we have already a partial subst for q *)
	      let values_for_x= value_table_get x vtq in
		if List.mem s values_for_x   (* Assumption (A) (see in file) *)
		then (TRS_type.empty, d) (* nothing new *)
		else 			    
		  let new_vtq= value_table_add x s vtq in
		  let new_substs= produce_substs (([qvar], [[(qvar,q)]])::(value_table_modif x s vtq)) (qvar::d.rhs_vars) 
		  in
		    (* because some substitutions may still not be correct w.r.t constraints at this step.
		       for instance a rule f(x, y) -> h(f(x, g(y))) normalised with f(q1, g(q2))->q0 
		       gives when its constraint is negated: Or(not(x=q1), not(x=q2)) which can not be verified
		       on the intersection tree automaton since variables are not linked! *)

		  let only_correct= 
		    List.filter (function s2 -> not((eq_solve (And (d.const, (subst_to_const s2))))=Bottom))
		      new_substs
		  in

		  let new_trans= trs_apply_list only_correct (Trans_type.list_to_trs d.trans) in
		    (new_trans, {trans= d.trans;
				 non_linked_vars= d.non_linked_vars;
				 linked_vars= d.linked_vars;
				 rhs_vars= d.rhs_vars;
				 const= d.const;
				 vt= (q, new_vtq)::(List.remove_assoc q d.vt)})
	  

  let rec norm_branches_to_rhs_table (bl: norm_branch list) (is_done: rhs_table) (lnk_vars: var_link)
    (non_lnk_vars: variable list) (rhs_vars: variable list): rhs_table=
    match bl with
	[] -> is_done
      | b::rem -> 
	    norm_branches_to_rhs_table rem 
	      ({trans= b.finished;
		    linked_vars= lnk_vars;
		    non_linked_vars= non_lnk_vars;
		    rhs_vars= rhs_vars;
		    const= b.c;
		    vt= []}::is_done) lnk_vars non_lnk_vars rhs_vars
	      

  (* Static normalisation of [r] w.r.t. [nr], produces a list of rules (with renamed variables) and 
     corresponding rhs statically normalised *)

  let static_norm (r: trs) (nr: norm_rule list): (rule list * rhs_table)=
    let renamed_nr=  rename_norm_rule_list nr variable_renaming_string in
    let rec aux (r: trs) (lhsdone: rule list) (rhsdone: rhs_table): (rule list * rhs_table)= 
      let is= (string_of_int (List.length (TRS_type.to_list r))) in
      let _ = 
	Printf.fprintf !out_chan "%s" ("\b\b\b\b\b\b\b\b"^(String.make (5- (String.length is)) ' ')^is);
	init_clock()
      in
	if TRS_type.is_empty r then (lhsdone, rhsdone)
	else 
	  let first_rule= TRS_type.first r in
	    
	  (* the common variable between the lhs automaton and the rhs automaton *) 
	    
	  let new_state_var= (Var(Variable.of_string variable_top_state_string)) in
	  let lhs_term= TRS_type.lhs first_rule in
	  let lhs_rule= TRS_type.new_rule lhs_term new_state_var in
	  let old_rhs= TRS_type.rhs first_rule in
	  let rhs_rule= TRS_type.new_rule old_rhs new_state_var in
	    
	  let linked_vars_in_rhs= get_linked_vars old_rhs in  
	  let all_linked_in_rhs= List.flatten linked_vars_in_rhs in
	  let non_lin_var_not_linked= 
	    List.filter (function v -> not (List.mem v all_linked_in_rhs)) (Term.list_non_linear_variables lhs_term) in
	    
	  (* linked vars are variables linked in the rhs and variables non linear in the lhs *)
	    
	  let linked_vars= 
	    if non_lin_var_not_linked=[] then linked_vars_in_rhs
	    else non_lin_var_not_linked::linked_vars_in_rhs in 
	    
	  let all_linked= List.flatten linked_vars in
	  let non_linked_vars= List.filter (function x -> not (List.mem x all_linked)) (Term.list_variables lhs_term) in
	  let rhs_vars= Term.list_variables old_rhs in
	    
	  let nbl= static_norm_one_trans rhs_rule renamed_nr in
	  let rt= norm_branches_to_rhs_table nbl [] linked_vars non_linked_vars rhs_vars in
	  let renamed_lhs= Common.list_make lhs_rule (List.length rt) in
	    aux (TRS_type.remainder r) (tlr_append renamed_lhs lhsdone) (tlr_append rt rhsdone)
	      
    in 
    let _= Printf.fprintf !out_chan "%s" "Static compilation of rules and approximation\n\nRemaining rewrite rules:     0"; init_clock() in
      aux r [] []

  (* suppressing transitions going to states in state set init *)

  let rec suppress_trans_to (init: state_set) (l: transition list): transition list=
    match l with
	[] -> []
      | t::rem -> 
	  if State_set_type.mem (Automata_type.rhs t) init then suppress_trans_to init rem 
	  else t::(suppress_trans_to init rem)

  (* pretty print *)

  let rule_to_string norm_rule=
    ("[ "^(TRS_type.rule_to_string norm_rule.pat)^"] ->\n[ "^
     (TRS_type.to_string norm_rule.modifs)^" ]")

  let norm_rules_to_string norm_rules= 
    (List.fold_right (function x -> function y -> (rule_to_string x)^"\n\n"^y)
		  norm_rules "")

  let to_string (g: gamma_content)=
    let states= (Alphabet_type.to_string (get_new_states g)) in
    let rules= norm_rules_to_string (get_norm_rules g) in
    let equations= equations_to_string (get_equations g) in
      (if states = "" then "" else "States "^states^"\n\n")^
      (if equations= "" then "" else "Equations "^equations^"\n\n")^
      (if rules= "" then "" else "Rules "^ rules^"\n\n")



  (* parsing of gamma content in a specification *)

  (* We check that rules are well formed w.r.t. [alphabet] and [state_ops], and moreover that 
     in the transition table of the rhs of the norm rule [nrule], that every rhs is either a variable
     occurring in the rule of the lhs of [nrule] or a state *)

  let check_norm_rule (nrule: norm_rule) alphabet state_ops = 
(* extended syntax discarded 
     let lhs_vars= List.append (Term.list_variables (TRS_type.lhs nrule.pat)) 
		    (Term.list_variables (TRS_type.rhs nrule.pat)) in *)
    let rhs_vars= (Term.list_variables (TRS_type.rhs nrule.pat)) in
    let all_vars= Common.clean (List.append rhs_vars 
				  (Term.list_variables (TRS_type.lhs nrule.pat))) in
    let list_modifs= TRS_type.to_list nrule.modifs in
    let _= List.for_all (function x -> 
			   let rhs= TRS_type.rhs x in
			   let lhs= TRS_type.lhs x in
			   let _= Term.check_special alphabet state_ops lhs in
			   let _= Term.check_special alphabet state_ops rhs in
			     match rhs with
				 Special(t) -> 
				   let varr= (Term.list_variables t) in
				     if Common.subeq_list varr all_vars then true
				     else 
				       raise (Error_in_parsing ("Right-hand side of rule "^(TRS_type.rule_to_string x)^" has a variable that does not occur in "^(TRS_type.rule_to_string nrule.pat)))
			       | Var(v) -> 
				   if List.mem v rhs_vars 
				   then true
				   else raise (Error_in_parsing ("Variable "^(Term.to_string rhs)^" does not occur in the right-hand side of "^(TRS_type.rule_to_string nrule.pat)))
			       | _ ->  raise (Error_in_parsing ("Right-hand side of rule "^(TRS_type.rule_to_string x)^" is neither a state nor a variable!"))) list_modifs in nrule
																						 
	  
  let rec parse_equations alphabet variable_set=
    parser
	[<lhs= Term.parse alphabet variable_set;
	  'Genlex.Kwd "=";
	  rhs= Term.parse alphabet variable_set;
	  rest_of_equations= parse_equations alphabet variable_set>] ->
	  if Term.is_variable lhs 
	  then raise (Error_in_parsing ("Left-hand side of an approximation equation cannot be reduced to a variable: "^(Term.to_string lhs)^" (but right hand side can ...)"))
	  else {lhs= lhs; rhs= rhs}::rest_of_equations
      | [< >] -> []
								
  let rec parse_import (lstate: (string * Alphabet_type.t) list) = parser
      [< 'Genlex.Ident s; rem= parse_import lstate>] ->
	(try (Alphabet_type.union (List.assoc s lstate) rem)
	with Not_found -> raise (Error_in_parsing ("cannot import automaton "^s^" because it is not defined or is defined after the import directive")))
    | [< >] -> Alphabet_type.new_alphabet



  let parse_one_rule alphabet state_ops variable_set= parser
      [< 'Genlex.Kwd "[";
	 patrn = TRS_type.parse_special_rule alphabet state_ops variable_set;
	 'Genlex.Kwd "]"; 'Genlex.Kwd "->"; 'Genlex.Kwd "[";
	 rules= TRS_type.parse_special alphabet state_ops variable_set;
	 'Genlex.Kwd "]" >] -> {pat=patrn; modifs= rules}


  let rec parse alphabet variable_set (lstate: (string * Alphabet_type.t) list) = parser
      [< 'Genlex.Kwd "Import"; 
	 state_ops= parse_import lstate; 
	 rem= parse_aux alphabet variable_set state_ops>] -> rem
    | [<rem= parse_aux alphabet variable_set Alphabet_type.new_alphabet>] -> rem

  and parse_aux alphabet variable_set impstateop= parser
      [< 'Genlex.Kwd "States"; 
	 state_ops = State_set_type.parse_ops;
	 (norm_rules, equations)= 
	   parse_rules alphabet (Alphabet_type.union state_ops impstateop) variable_set>]  ->
	let new_state_ops= (Alphabet_type.union state_ops impstateop) in
	if Alphabet_type.disjoint alphabet new_state_ops
	then set_equations equations (set_new_states new_state_ops (set_norm_rules norm_rules empty))
	else raise (Multiply_defined_symbol "states and symbols are not disjoint in the specification")
    | [< 'Genlex.Kwd "Equations"; 
	 equations= parse_equations alphabet variable_set>]  ->
	(set_equations equations empty)
    | [< 'Genlex.Kwd "Rules";
	 rules= parse_rules_aux alphabet impstateop variable_set;
	 (r,e)= parse_rules alphabet impstateop variable_set>] -> 
	set_equations e (set_new_states impstateop (set_norm_rules (List.append rules r) empty))
    | [< >] -> raise (Error_in_parsing ("Approximation description should begin by keyword States, Equations, Import or Rules"))

  and parse_rules alphabet state_ops variable_set=
    parser
	[< 'Genlex.Kwd "Equations"; 
	 equations= parse_equations alphabet variable_set;
	 (r,e)= parse_rules alphabet state_ops variable_set>] -> (r, (List.append equations e))
      | [< 'Genlex.Kwd "Rules";
	 rules= parse_rules_aux alphabet state_ops variable_set;
	  (r,e)= parse_rules alphabet state_ops variable_set>] -> ((List.append rules r), e)
      | [< >] -> ([],[])

  and parse_rules_aux alphabet state_ops variable_set =
    parser
	[< rule= parse_one_rule alphabet state_ops variable_set; 
	   remainder= parse_rules_aux alphabet state_ops variable_set>] ->
	  (check_norm_rule rule alphabet state_ops)::remainder
      | [< >] -> []


  (* parsing of user additionnal norm rules *)

  let rec parse_norm_aux alpha state_ops variable_set= 
    parser 

      | [< 'Genlex.Kwd "States"; add_state_ops= State_set_type.parse_ops;
	   (top, bot, sops)= parse_norm_aux alpha (Alphabet_type.union state_ops add_state_ops) variable_set >] -> 
	  (top, bot, (Alphabet_type.union sops add_state_ops))
      | [< 'Genlex.Kwd "Rules"; (top,bot,ops)= parse_norm_rules_aux alpha state_ops variable_set >] ->
	  (top, bot, ops)
      | [<'Genlex.Kwd "." >] -> ([], [], Alphabet_type.new_alphabet)
      | [< >] -> raise (Stream.Error "Keyword 'States' or 'Rules' expected!\n")

  and parse_norm_rules_aux alpha state_ops variable_set= 
    parser
	[< 'Genlex.Kwd "Top"; rule= parse_one_rule alpha state_ops variable_set; (top, bot, sops)= 
	     parse_norm_rules_aux alpha state_ops variable_set>] ->  ((check_norm_rule rule alpha state_ops)::top, bot, sops)
      | [< rule= parse_one_rule alpha state_ops variable_set; (top, bot, sops)= 
	     parse_norm_rules_aux alpha state_ops variable_set >] ->  (top, (check_norm_rule rule alpha state_ops)::bot, sops)
      | [<'Genlex.Kwd "." >] -> ([], [], Alphabet_type.new_alphabet)



  let rec parse_norm_rules (a: alphabet) (state_ops: alphabet)(variables: Term.variable_set) (g: gamma_content): (norm_rule list * alphabet)=

    let current_state_ops= Alphabet_type.union (get_new_states g) state_ops in
      
    let _= Printf.fprintf !out_chan "%s" ("Current normalisation rules are: \n"^(norm_rules_to_string (get_norm_rules g))^"\n\nAlphabet="^(Alphabet_type.to_string a)^"\nand Variables= "^(Variable_set_type.to_string variables)^"\nand States= "^(Alphabet_type.to_string current_state_ops)^"\n\nType additionnal normalization rules using the 'States' and 'Rules' keyword and end by a dot '.': \n\n(use keyword 'Top' before a rule to place it at the beginning of the rule list)\n\n"); flush !out_chan in 
      
      try (let (top, bot, sops)= parse_norm_aux a current_state_ops variables 
				   (lexer (Stream.of_channel !in_chan)) in
	     ((List.rev top)@(get_norm_rules g)@bot, sops))
      with 
	| Stream.Error s -> 
	    begin
	      Printf.fprintf !out_chan "%s" ("\n\nSyntax error, try again\n"^s); 
	      flush !out_chan;
	      parse_norm_rules a state_ops variables g
	    end
	| Term.Undefined_symbol(f) -> 
	    begin Printf.fprintf !out_chan "%s" ("\n\nError: Symbol "^f^" is undefined, try again\n"); 
	      flush !out_chan;
	      parse_norm_rules  a state_ops variables g
	    end
	| Term.Badly_formed_term(f) -> 
	    begin
	      Printf.fprintf !out_chan "%s" ("\n\nError: Bad term syntax! "^f^", try again\n"); 
	      flush !out_chan;
	      parse_norm_rules  a state_ops variables g
	    end
	| TRS_type.Badly_formed_rule(f) -> 
	    begin
	      Printf.fprintf !out_chan "%s" ("\n\nError: Bad rule syntax! "^f^", try again \n");
	      flush !out_chan;
	      parse_norm_rules  a state_ops variables g
	    end
	| Error_in_parsing(f) -> 
	    begin
	      Printf.fprintf !out_chan "%s" ("\n\nError: Bad rule syntax! "^f^", try again \n");
	      flush !out_chan;
	      parse_norm_rules  a state_ops variables g
	    end
	| _ -> 
	    begin
	      Printf.fprintf !out_chan "%s" "Syntax error, try again!\n"; 
	      flush !out_chan;
	      parse_norm_rules  a state_ops variables g
	    end


  (* The function that produces c -> q', for each new normalized transition c -> q and each epsilon transition q -> q' *)

  let rec apply_epsilon (le: transition list) (tr: transition_table): transition_table=
    match le with
	[] -> Trans_type.empty
      | eps_trans::rem -> 
	  Trans_type.union 
	    (Automata_type.normalize_epsilon 
	       (Trans_type.lhs eps_trans) (Trans_type.rhs eps_trans) tr)
	    (apply_epsilon rem tr)
	  
	    

  (* the gamma function used for approximation of new transitions obtained during completion *)
	 
  (* After an application of one step of gamma, the gamma_content is
     updated, state_ops contains all initial state operators as well as
     new state operators given by the user or constructed automatically
     as new states. 'i' has been incremented if automatic new states has
     been given *)

	 
  let gamma (ltrans: transition_table) 
    (delta: (symbol, (state, rule list) folder) folder)  gamma_content alphabet state_ops i (init_state: state_set)=
       let _ = List.iter (function l -> print_string "["; List.iter (function x -> (print_string ((Trans_type.rule_to_string x)^" "))) l) !epsilon_trans in
    let initial_strategy= get_strategy gamma_content in

    (* the general function applying normalising strategy *)

    (*      let rec norm_strat strategy (trans_to_normalise: transition_table) 
	    gamma_content state_ops i (normalised_trans: transition_table)= *)
    let rec (norm_strat: string list -> 
	       transition_table-> gamma_content-> alphabet-> int-> transition_table ->
		 (transition_table * gamma_content * alphabet * int))=
      function strategy -> function trans_to_normalise -> function gamma_content ->
	function state_ops -> function i -> function normalised_trans->
	  let first= (Trans_type.first trans_to_normalise) in
	  let lhs= Trans_type.lhs first in
	  let lrem= (Trans_type.remainder trans_to_normalise) in
	    (match strategy with 
		 [] ->  (* if strategy has been has been entirely executed, 
			   we restart from the initial strategy *)
		   norm_strat initial_strategy trans_to_normalise 
		     gamma_content state_ops i normalised_trans
		     
	       (* Normalisation with prior rules: prior strategy *)
		     
	       | "prior"::rem_strat -> 
		   let prior_normed= TRS_type.bottom_up_norm gamma_content.prior lhs in
		     if not (Term.equal lhs prior_normed) 
		     then 
		       begin
			 let the_rhs= (Trans_type.rhs first) in
			 let prior_normed_trans= Trans_type.new_rule prior_normed the_rhs in
			   Printf.fprintf !out_chan "%s" ("Prior normalisation simplifies the transition into:\n\n"^(Trans_type.rule_to_string prior_normed_trans)^"\n\n\n");
			   flush !out_chan;

			   (* if prior normalisation modifies the current non-normalised transition, we re-start from
			      the begining with [initial_strategy] *)

			   trivial initial_strategy
			     (Trans_type.add prior_normed_trans lrem)
			     gamma_content
			     state_ops i normalised_trans
		       end
		     else
		       (* if this strategy operator has no effect we use continue with the next one *)
		       norm_strat rem_strat trans_to_normalise gamma_content state_ops i 
			 normalised_trans
			 
	       | "norm_rules"::rem_strat ->
		   let (modif, new_trans)= norm_with_norm_rules first (get_norm_rules gamma_content) in
		     if modif 
		     then
		       begin
			 Printf.fprintf !out_chan "%s" ("Norm rules simplified the transition into:\n\n"^(Trans_type.to_string new_trans)^"\n\n\n");
			 flush !out_chan;
			 (* if [norm_rules] normalisation modifies the current non-normalised 
			    transition, we re-start from the begining with [initial_strategy] *)
			 
			 trivial initial_strategy (Trans_type.union new_trans lrem)
			   gamma_content 
			   (* we add the new states used in the [norm_rules] *)
			   (Alphabet_type.union (get_new_states gamma_content) state_ops) i
			   normalised_trans
		       end
		     else
		       norm_strat rem_strat trans_to_normalise gamma_content state_ops i 
			 normalised_trans

	       | "manual_norm_conf"::rem_strat -> 
		   begin
		     Printf.fprintf !out_chan "%s" 
		       "Do you want to give by hand some NORMALIZATION rules? ";
		     flush !out_chan;
		     if go() then 
		       norm_strat ("manual_norm"::rem_strat) trans_to_normalise gamma_content state_ops i 
			 normalised_trans
		     else norm_strat rem_strat trans_to_normalise gamma_content state_ops i 
		       normalised_trans
		   end

	       | "manual_norm"::rem_strat ->
		   (* Interactive addition of normalisation rules *)
		   let (new_norm, new_state_ops)= parse_norm_rules alphabet state_ops !varset gamma_content in
		   let new_gamma= set_norm_rules new_norm 
				    (set_new_states (Alphabet_type.union (get_new_states gamma_content)
						       new_state_ops)
				       gamma_content) in
		   let _=  Printf.fprintf !out_chan "%s" ("Transition to normalize: "^(Trans_type.rule_to_string first)^"\n\n"); flush !out_chan in


		     norm_strat initial_strategy trans_to_normalise new_gamma 
		       (Alphabet_type.union state_ops new_state_ops) i normalised_trans


		       
		       
	       | "manual_conf"::rem_strat -> 
		   begin
		     Printf.fprintf !out_chan "%s" 
		       "Do you want to give by hand some rules to normalize the transition? ";
		     flush !out_chan;
		     if go() then 
		       norm_strat ("manual"::rem_strat) trans_to_normalise gamma_content state_ops i 
			 normalised_trans
		     else norm_strat rem_strat trans_to_normalise gamma_content state_ops i 
		       normalised_trans
		   end

	       | "manual"::rem_strat -> 
		   (* Normalisation with interactively given user rules *)
		   begin
		     Printf.fprintf !out_chan "%s" "Use key word 'States' followed by the names of the new states ended by a dot '.'(optional)\n then give a sequence of transitions ended by a dot '.'\nAdd a star '*' before transitions you want to add to the prior set.\nThe prior transitions should be normalized!!\n"; 
		     flush !out_chan;
		     let (new_trans, new_prior, new_ops)= parse_user_transitions alphabet state_ops in
		     let user_normed= TRS_type.bottom_up_norm new_trans lhs in
		     let user_normed_trans= Trans_type.new_rule user_normed (Trans_type.rhs first) in
		     let updated_state_ops= Alphabet_type.union new_ops state_ops in
		     let new_trans_set= Trans_type.add user_normed_trans 
					  (Trans_type.union new_trans lrem) in
		     let new_gamma_content= add_prior_to_gamma new_prior gamma_content in
		       if Term.equal lhs user_normed 
		       then 
			 begin
			   Printf.fprintf !out_chan "%s" ("No change with this transition...\n\n");
			   flush !out_chan;
			   norm_strat rem_strat new_trans_set new_gamma_content updated_state_ops i 
			     normalised_trans
			 end
		       else 
			 begin
			   Printf.fprintf !out_chan "%s" ("Normalisation simplifies the transition into: "^(Trans_type.rule_to_string user_normed_trans)^"\n\n\n");
			   flush !out_chan;
			   trivial initial_strategy new_trans_set new_gamma_content 
			     updated_state_ops i normalised_trans
			 end
		   end
		   
	       | "auto_conf"::rem_strat -> 
		   begin
		     Printf.fprintf !out_chan "%s" 
		       "Do you want to use automatic normalisation by NEW states to normalise the transition? ";
		     flush !out_chan;
		     if go() then 
		       norm_strat ("auto"::rem_strat) trans_to_normalise gamma_content state_ops i 
			 normalised_trans
		     else norm_strat rem_strat trans_to_normalise gamma_content state_ops i 
		       normalised_trans
		   end
		   
	       | "auto"::rem_strat -> 
		   (* automatic normalisation with new states *)
		   let (norm_with_new, new_i, auto_new_ops) = 
		     Automata_type.normalize (Trans_type.list_to_trs [first])  
		       (Trans_type.list_to_trs (Automata_type.bi_folder_flatten delta)) "qnew" i in
		     trivial initial_strategy (Trans_type.union norm_with_new lrem) gamma_content
		       (Alphabet_type.union_fast auto_new_ops state_ops) new_i normalised_trans

	       | "auto_prior_conf"::rem_strat -> 
		   begin
		     Printf.fprintf !out_chan "%s" 
		       "Do you want to use automatic normalisation by NEW states and use the normalised\ntransitions as PRIOR transitions? ";
		     flush !out_chan;
		     if go() then 
		       norm_strat ("auto_prior"::rem_strat) trans_to_normalise gamma_content state_ops i 
			 normalised_trans
		     else norm_strat rem_strat trans_to_normalise gamma_content state_ops i 
		       normalised_trans
		   end

	       | "exact" ::rem_strat -> 
		   norm_strat ("prior"::("exact_auto_prior"::rem_strat)) trans_to_normalise gamma_content state_ops i
		     normalised_trans
		     
	       | "exact_auto_prior"::rem_strat ->
		   (* automatic normalisation with new states and construction of prior transitions 
		      in an exact way (no transition with existing state is added to prior) *)
		   let (norm_with_new, new_i, auto_new_ops)=
		     Automata_type.normalize_deterministic (Trans_type.list_to_trs [first])  
		       (Trans_type.list_to_trs (Automata_type.bi_folder_flatten delta)) "qnew" i in
		     trivial initial_strategy (Trans_type.union norm_with_new lrem) 
		       (add_prior_to_gamma 
			  (* transitions going to an existing state cannot be put in prior in the exact case *)
			  (Trans_type.list_to_trs (suppress_trans_to init_state (Trans_type.to_list norm_with_new)))
			  gamma_content) 
		       (Alphabet_type.union_fast auto_new_ops state_ops) new_i normalised_trans

	       | "auto_prior"::rem_strat ->
		   (* automatic normalisation with new states and construction of prior transitions *)
		   let (norm_with_new, new_i, auto_new_ops)=
		     Automata_type.normalize_deterministic (Trans_type.list_to_trs [first])  
		       (Trans_type.list_to_trs (Automata_type.bi_folder_flatten delta)) "qnew" i in
		     trivial initial_strategy (Trans_type.union norm_with_new lrem) 
		       (add_prior_to_gamma 
			  norm_with_new
			  gamma_content) 
		       (Alphabet_type.union_fast auto_new_ops state_ops) new_i normalised_trans

	       | x::rem_strat -> raise (Strategy_error ("Unknown normalisation operator: "^x)))
	    
	    


    (* the function retrieving transitions already normalised and epsilon transitions to 
       be automatically normalised. If the transition is not trivially normalisable, we use the 
       previous function i.e., [norm_strat] *)

    and trivial strategy (trans_to_normalise: transition_table) gamma_content state_ops i 
      (normalised_trans: transition_table)=
      
      if Trans_type.is_empty trans_to_normalise 
      then 
	let additional= (apply_epsilon (List.flatten !epsilon_trans) normalised_trans) in
	  begin
	    if not (Trans_type.is_empty additional)
	    then
	      begin 
		Printf.fprintf !out_chan "%s" ("Adding transitions obtained by epsilon normalisation:\n\n"^(Trans_type.to_string additional)^"\n\n");
		flush !out_chan
	      end;
	    ((Trans_type.union additional normalised_trans), gamma_content, state_ops, i)
	  end
      else 
	let first= (Trans_type.first trans_to_normalise) in
	let lrem= (Trans_type.remainder trans_to_normalise) in
	  begin
	    Printf.fprintf !out_chan "%s" ("Adding transition:\n\n "^
					   (Trans_type.rule_to_string first)^"\n\n");
	    flush !out_chan;
	    if Automata_type.is_normalized first 
	    then  

	      (* ------------- case of a transition already normalised --------------- *)

	      begin
		Printf.fprintf !out_chan "%s" " ... already normalised!\n\n\n";
		flush !out_chan;
		trivial strategy lrem gamma_content state_ops i
		  (Trans_type.add first normalised_trans)
	      end
	    else 
	      let lhs= Trans_type.lhs first in
       		if (Automata_type.is_state_config lhs)
		then 
		  if List.mem first (List.flatten !epsilon_trans)
		  then trivial strategy lrem gamma_content state_ops i normalised_trans
		  else
		    (* -- case of a new epsilon transition we directly normalize it -- *)
		    
		    begin
		      Printf.fprintf !out_chan "%s" " ... automatically normalized.\n\n\n";
		      flush !out_chan;
		      epsilon_trans := (first::(List.hd !epsilon_trans))::(List.tl !epsilon_trans);
		      let copy= Automata_type.normalize_epsilon lhs 
				  (Trans_type.rhs first) 
				  (Trans_type.list_to_trs 
				     (Automata_type.bi_folder_flatten delta)) in
			trivial strategy lrem gamma_content state_ops i 
			  (Trans_type.union copy normalised_trans)
		    end
		else
		  
		  (* case where the transition is not necessary i.e. it is already covered
		     by the rules of the tree automaton *)
		  if Automata_type.is_recognized_into lhs (Trans_type.rhs first) delta 
		  then
		    begin
		      Printf.fprintf !out_chan "%s" " ... covered by current automaton.\n\n\n";
		      flush !out_chan;
		      trivial strategy lrem gamma_content state_ops i normalised_trans
		    end
		  else 

		    
		    (* -------the general case where the first transition has to be normalised 
		       i.e. it is not trivial: we use the normalisation strategy --------- *)
		    norm_strat strategy trans_to_normalise gamma_content 
		      state_ops i normalised_trans
	  end

    in
      match initial_strategy with
	  [] -> raise (Strategy_error ("Cannot start gamma function an empty strategy!"))
	| _ -> trivial initial_strategy ltrans gamma_content state_ops i Trans_type.empty



end

