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

(* ATTENTION il s'agit bien de rewrite.ml *)
(* open Common;; doit etre remplace par la def en dur pour eviter 
   le stack overfloww !! *)
(* needs something here not to do a stack overflow ! *)
let a=()

open Common


(* Rewrite sytems and rewrite rules *)

module RewriteSystem
  (Alphabet_type: ALPHABET_TYPE)
  (Variable_set_type: VARIABLE_SET_TYPE)
  (Term_type: TERM_TYPE with type variable_set= Variable_set_type.t and type alphabet= Alphabet_type.t)=
struct
  type alphabet= Alphabet_type.t
  type variable_set= Variable_set_type.t
  type term = Term_type.t
  type rule = {lhs: term; rhs: term}
  type ruleSystem = rule list
  type t = ruleSystem
  exception Variable_rhs_not_included_in_lhs of string    
  exception Does_not_rewrite_on_top 
  exception Badly_formed_rule of string
    
  (* the empty trs and other constructors *)
    
  let empty = []
  let new_rule t1 t2 = {lhs= t1; rhs= t2}
  let is_empty trs = ((List.length trs) = 0)
  let first = List.hd
  let remainder = List.tl
  let nth = List.nth		    
		    
  (* right-hand side and left-hand side of a rule *)
		    
  let rhs rule = rule.rhs
  let lhs rule = rule.lhs
  let rule_equal (r1:rule) (r2:rule)= r1 = r2
    
  let is_left_linear rule = Term_type.is_linear (lhs rule)
  let is_right_linear rule = Term_type.is_linear (rhs rule)
  let is_linear rule = (is_left_linear rule) && (is_right_linear rule)
			
  let is_ground rule = 
    if (Term_type.is_ground (lhs rule))
    then 
      (Term_type.is_ground (rhs rule))
    else false


  (* get the non-linear lhs of a set of rules *)
			 
  let rec non_linear_lhs trs=
    match trs with
	[] -> []
      | first::remainder -> 
	  let rem= non_linear_lhs remainder in
	  let lhs= lhs first in
	    if Term_type.is_linear lhs then rem
	    else lhs::rem
	      
	      
  (* adding a rule in a trs, and union of two trs *)
	      
  let add e l = if List.mem e l then l else e::l
    
  let mem = List.mem
	      
  let rec union l1 l2 = match l1 with
      [] -> l2
    | e::l -> add e (union l l2)
	
  let rec inter l1 l2 = match l1 with
      [] -> []
    | e::l -> 
	if List.mem e l2 
	then e::(inter l l2)
	else (inter l l2)


  (* if the rule is not in the trs we can catenate 
     without testing membership *) 

  let add_fast e l = e::l

  (* if trs are known to be disjoint we can catenate 
     without testing membership for union *) 

  let union_fast = List.append

  let to_list l = l
  let list_to_trs l= l


  (* prettyprint *)

  let rule_to_string rule = 
    String.concat " -> " [(Term_type.to_string rule.lhs);
			  (Term_type.to_string rule.rhs)]
      
  let to_string system = 
    String.concat "\n" (List.map rule_to_string system)

  (* Replacement in special subterms of some rewrite rules *)

  let replace_special_rule subst rule = 
    {lhs= (Term_type.replace_special subst rule.lhs);
     rhs= (Term_type.replace_special subst rule.rhs)}

  let replace_special spec_subst trs = 
    List.map (replace_special_rule spec_subst) trs

  (* rename variables of a rule *) 

  let rename_rule_var (r:rule) (s: string): rule= 
    {lhs= (Term_type.rename_var r.lhs s);
     rhs= (Term_type.rename_var r.rhs s)}


  (* rename variables of a TRS *) 

  let rename_var (r:ruleSystem) (s: string): ruleSystem= 
    List.map (function rule -> rename_rule_var rule s) r

  (* Checking special rules with regards to an alphabet and a special
     alphabet: checks construction of lhs and rhs as well as inclusion
     of var(rhs) in var(lhs) *) 
      
  let check_special_rule rule alphabet alphabet_special = 
    if (subeq_list (Term_type.list_variables rule.rhs) 
	  (Term_type.list_variables rule.lhs))   
    then {lhs= (Term_type.check_special alphabet alphabet_special rule.lhs); 
	  rhs= (Term_type.check_special alphabet alphabet_special rule.rhs)}
    else raise (Variable_rhs_not_included_in_lhs (rule_to_string rule))
      
  let rec check_special system alphabet alphabet_special = match system with
      [] -> []
    | rule::remainder -> (check_special_rule rule alphabet alphabet_special) :: 
	(check_special remainder alphabet alphabet_special)

  (* Checking rules with regards to an alphabet: checks construction of
     lhs and rhs as well as inclusion of var(rhs) in var(lhs) *) 

  let check_rule rule alphabet = 
    check_special_rule rule alphabet Alphabet_type.new_alphabet

      
  (* Checking of a whole trs w.r.t. an alphabet. *)

  let check system alphabet = 
    check_special system alphabet Alphabet_type.new_alphabet


  (* Parsing of trs, rules, etc... with alphabet and special alphabet
     when necessary *)

  let parse_special_rule alphabet alphabet_special variable_set = parser
      [< lefths = Term_type.parse_special alphabet alphabet_special 
	            variable_set ; 
	 righths= parser
	     [< 'Genlex.Kwd "->" ;
		righths = parser
		    [< righths= Term_type.parse_special alphabet alphabet_special variable_set >] -> righths
		  | [< >] -> raise (Badly_formed_rule ("Expecting a term for right hand side of: "^(Term_type.to_string lefths)^" ->"))
	     >] -> righths
	   | [< >] -> raise (Badly_formed_rule ("Expecting '->' after left-hand-side: "^(Term_type.to_string lefths)))
      >] -> {lhs = lefths; rhs = righths} 


  let rec parse_special_system alphabet alphabet_special variable_set =
    parser
	[< first_rule = parse_special_rule alphabet alphabet_special variable_set ;
	   remainder = parse_special_system alphabet 
	                 alphabet_special variable_set >] ->
	  add first_rule remainder
      |	[< >] -> []
	  
  let parse_rule alphabet variable_set = 
    parse_special_rule alphabet Alphabet_type.new_alphabet variable_set

  let parse_system alphabet variable_set = 
    parse_special_system alphabet Alphabet_type.new_alphabet variable_set
      
  let parse = parse_system
		
  let parse_special = parse_special_system
			
  let parse_ground_special alphabet alphabet_special= 
    parse_special alphabet alphabet_special Variable_set_type.empty

  let parse_ground_special_rule alphabet alphabet_special= 
    parse_special_rule alphabet alphabet_special Variable_set_type.empty


  (* Rewriting of a term by a rule on top position *)

  let rewrite_top rule term = 
    let subst = Term_type.matching rule.lhs term in 
      (Term_type.apply subst rule.rhs)

      
  (* rewrite once on top position with any rule of trs *)
      
  let rec rewrite_top_once trs term = match trs with
      [] -> raise Does_not_rewrite_on_top
    | first_rule::remainder -> try 
    	(rewrite_top first_rule term) with
    	    Term_type.Terms_do_not_match (_,_) -> 
	      rewrite_top_once remainder term
		

  (* leftmost innermost normalisation of a term thanks to a trs. Of course TRS should terminate! *)
		
  let rec left_inner_norm trs term = match term with
      Const(f) -> 
	(try 
	   let norm_top= (rewrite_top_once trs term) in
	     left_inner_norm trs norm_top
	 with
	     Does_not_rewrite_on_top -> term)
    | Fsym(f, l_args) -> (
    	let norm_args = List.map (left_inner_norm trs) l_args in
	  try (let norm_top = 
		 (rewrite_top_once trs (Fsym(f, norm_args))) in
		 (left_inner_norm trs norm_top))
    	  with
	      Does_not_rewrite_on_top -> Fsym(f, norm_args))
    | x -> x


  (* Rewriting of special terms thanks to a trs *)

  let rec left_inner_norm_special trs term = match term with
      Fsym(f, l_args) ->
	Fsym(f, List.map (left_inner_norm_special trs) l_args)
    | Special(t) -> 
	Special(left_inner_norm trs t)
    | x -> x


  (* Rewriting of special rules and whole term rewriting systems 
     thanks to a trs *)

  let left_inner_norm_special_rule trs rule =
    {lhs= left_inner_norm_special trs rule.lhs;
     rhs= left_inner_norm_special trs rule.rhs}

  let rec left_inner_norm_special_system trs system =
    match system with 
	[] -> []
      | t::rem -> add (left_inner_norm_special_rule trs t) (left_inner_norm_special_system trs rem)

  (* This is a particular rewriting strategy used when the trs is a tree 
     automaton transition system: We normalise bottom-up without
     re-normalising again subterms, and rewriting only once on top (it
     is enough) *)
      
  let rec bottom_up_norm trs term = match term with
      Const(f) -> (try (rewrite_top_once trs term)
			     with Does_not_rewrite_on_top -> Const(f))
    | Fsym(f, l_args) -> (
    	let norm_args = List.map (left_inner_norm trs) l_args in
	  try (rewrite_top_once trs (Fsym(f, norm_args)))
    	  with
	      Does_not_rewrite_on_top -> Fsym(f, norm_args))
    | x -> x

end
