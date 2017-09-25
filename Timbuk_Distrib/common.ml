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

type ('sym, 'var) term_const=
    Var of 'var
  | Const of 'sym
  | Fsym of ('sym * (('sym, 'var) term_const) list)
  | Special of ('sym, 'var) term_const

    
module type PRINTABLE_TYPE =
  sig
    type t
    val to_string: t -> string
    val of_string: string -> t
    val equal: t -> t -> bool
  end

module type STATE_CONTENT_TYPE =
  sig
    type t
    val to_string: t -> string
    val of_string: string -> t
    val equal: t -> t -> bool
    val empty: t
    val inter: t -> t -> t
  end

module type ALPHABET_TYPE =
  sig
    type t
    type symbol

    exception Symbol_not_in_alphabet of string
    val new_alphabet: t
    val union_fast : t -> t -> t
    val union: t -> t -> t
    val disjoint: t -> t -> bool
    val add_symbol: symbol -> int -> t -> t
    val get_arity: symbol -> t -> int
    val occur: symbol -> t -> bool
    val to_string: t -> string
    val to_string_list: t -> string list
    val to_list: t -> (symbol * int) list
    val parse: Genlex.token Stream.t -> t
  end


module type VARIABLE_SET_TYPE =
  sig
    type t
    type variable
    val empty: t
    val is_empty: t -> bool
    val mem: variable -> t -> bool
    val to_string: t -> string
    val to_string_list: t -> string list 
    val parse: Genlex.token Stream.t -> t
  end


module type TERM_TYPE= 
sig

  type symbol
  type variable
  type alphabet
  type variable_set
  type term= (symbol, variable) term_const

  type t= term

  type substitution= (variable * term) list
			
  exception Terms_do_not_match of string * string
  exception Terms_do_not_unify of string * string
  exception Badly_formed_term of string
  exception Parse_error of string
  exception Undefined_symbol of string 
  exception Bad_operation_on_special_term of string
  exception Bad_operation_on_var of string
  
			
  val equal : t -> t -> bool
  val depth : t -> int
  val to_string : t -> string
  val top_symbol : t -> symbol
  val list_arguments : t -> t list
  val is_variable : t -> bool
  val is_constant : t -> bool
  val is_special : t -> bool
  val get_special : t -> t
  val map : (symbol -> symbol) -> (t -> t) -> t -> t
  val map_special : (symbol -> symbol) -> (t -> t) -> t -> t
  val var_change : variable -> string -> variable
  val rename_var : t -> string -> t
  val list_leaves : t -> t list
  val list_variables : t -> variable list
  val list_non_linear_variables : t -> variable list
  val linearize: term -> (term * (variable * (variable list)) list)
  val is_ground : t -> bool
  val is_linear : t -> bool
  val list_special : t -> t list
  val check_special : alphabet -> alphabet -> t -> t
  val check : alphabet -> t -> t
  val replace_special : ((t * t) list) -> t -> t
  val apply : substitution  -> t -> t
  val apply_special : substitution  -> t -> t
  val apply_several : (substitution list) -> t -> t list
  val apply_substs_on_terms : substitution list -> t list -> t list
  val parse_special :
    alphabet ->
        alphabet ->
        variable_set -> Genlex.token Stream.t -> t
  val parse :
      alphabet ->
        variable_set -> Genlex.token Stream.t -> t
	
  val parse_ground :
    alphabet ->
        Genlex.token Stream.t -> t

  val parse_ground_term_set :
    alphabet ->
        Genlex.token Stream.t -> t list
	
  val parse_ground_special :
    alphabet ->
        alphabet ->
	Genlex.token Stream.t -> t
	
  val coherent : substitution -> substitution
  val unify : t -> t -> substitution
  val matching : t -> t -> substitution
  val matching_special : t -> t -> substitution
end 


module type STATE_SET_TYPE =
  sig
    type alphabet
    type symbol
    type state_content
    type t
    type state
    val is_structured: t -> bool
    val default_prod_symbol: symbol
    val state_product: state -> state -> state
    val empty: t
    val is_empty: t -> bool
    val first: t -> state
    val remainder: t -> t
    val add: state -> t -> t
    val add_verb: state -> state_content -> t -> t
    val add_all: state list -> t -> t
    val add_all_verb : state list -> t -> t -> t
    val mem: state -> t -> bool
    val inter: t -> t -> t
    val union: t -> t -> t
    val union_disjoint: t -> t -> t
    val minus: t -> t -> t
    val all_mem: state list -> t -> bool
    val list_to_set: state list -> t
    val to_list: t -> state list
    val to_string: t -> string
    val state_description : state -> t -> state_content
    val symbolic_product : t -> t -> t
    val to_string_verb: t -> string
    val parse_ops: Genlex.token Stream.t -> alphabet
    val parse: alphabet -> alphabet -> Genlex.token Stream.t -> t
    val parse_verb: alphabet -> alphabet -> Genlex.token Stream.t -> t
  end



module type TRS_TYPE=
sig
  type variable_set
  type alphabet
  type term
  type ruleSystem
  type t= ruleSystem
  type rule

  exception Badly_formed_rule of string
  val empty : t
  val new_rule : term -> term -> rule
  val is_empty : t -> bool
  val first : t -> rule
  val remainder : t -> t
  val nth : t -> int -> rule
  val rhs : rule -> term
  val lhs : rule -> term
  val rule_equal : rule -> rule -> bool
  val is_left_linear : rule -> bool
  val is_right_linear : rule -> bool
  val is_linear : rule -> bool
  val is_ground : rule -> bool
  val non_linear_lhs : t -> term list
  val add : rule -> t -> t
  val mem : rule -> t -> bool
  val union : t -> t -> t
  val inter : t -> t -> t
  val add_fast : rule -> t -> t
  val union_fast : t -> t -> t
  val to_list : t -> rule list
  val list_to_trs : rule list -> t
  val rename_rule_var : rule -> string -> rule
  val rename_var : ruleSystem -> string -> ruleSystem
  val rule_to_string : rule -> string
  val to_string : t -> string

  val check_special_rule :
    rule -> alphabet -> alphabet -> rule
  val check_special :
    t -> alphabet -> alphabet -> t
  val check_rule : rule -> alphabet -> rule
  val check : t -> alphabet -> t
  val parse_special_rule :
    alphabet ->
      alphabet ->
        variable_set -> Genlex.token Stream.t -> rule

  val parse_rule :
    alphabet ->
      variable_set -> Genlex.token Stream.t -> rule
  
  val parse :
      alphabet ->
        variable_set -> Genlex.token Stream.t -> t
  val parse_special :
    alphabet ->
      alphabet ->
        variable_set -> Genlex.token Stream.t -> t

  val parse_ground_special :
    alphabet ->
      alphabet -> Genlex.token Stream.t -> t
  val parse_ground_special_rule :
    alphabet -> alphabet -> Genlex.token Stream.t -> rule

  val rewrite_top_once : t -> term -> term
  val left_inner_norm : t -> term -> term
  val left_inner_norm_special :
    t -> term -> term

  val left_inner_norm_special_system :
    t -> t -> t
  val bottom_up_norm : t -> term -> term
end 

  
module type AUTOMATA_TYPE=
sig 
  exception Not_a_state of string
  exception Not_in_folder
  exception Multiply_defined_symbol of string
  exception Linearity_problem of string
  exception Normalisation_problem of string
    
  type symbol
  type alphabet
  type term
  type rule
  type substitution
  type state
  type state_set

  type transition_table
  type tree_automata

  type t = tree_automata
  type ('a, 'b) folder
  type mini_subst= (term * term)
  type sol_filt=  
    | Empty
    | Bottom
    | S of mini_subst   
    | Not of sol_filt
    | And  of sol_filt * sol_filt  
    | Or of sol_filt * sol_filt       

  val get_alphabet : t -> alphabet
  val get_state_ops : t -> alphabet
  val get_states : t -> state_set
  val get_final_states : t -> state_set
  val get_transitions : t -> transition_table
  val get_prior : t -> transition_table
  val make_automaton:
    alphabet -> alphabet -> state_set -> state_set -> transition_table -> transition_table -> t

  val term_set_to_automaton: alphabet -> term list ->  string ->  int -> (t * int) 

  val modify_final : t -> state_set -> t
  val modify_prior : t -> transition_table -> t
  val modify_state_ops : t -> alphabet -> t
  val modify_transitions : t -> transition_table -> t
  val modify_states : t -> state_set -> t
  val is_empty : t -> bool
  val make_state : symbol -> state
  val make_state_config : state -> term
  val new_trans : symbol -> state list -> state -> rule
  val is_state_config : term -> bool
  val lhs : rule -> term
  val rhs : rule -> term
  val top_symbol :
    rule -> symbol
  val state_label : term -> state
  val is_normalized : rule -> bool
  val list_state : rule -> state list
  val check_subst : substitution list -> substitution list
  val simplify_sol : sol_filt -> sol_filt
  val dnf : sol_filt -> sol_filt
  val to_string : t -> string
  val states_of_transitions :
    transition_table -> state_set
  val parse : alphabet -> Genlex.token Stream.t -> t

  val accessibility_cleaning : t -> t
  val utility_cleaning : t -> t
  val clean : t -> t
  val rewrite_state_labels :
    t -> transition_table -> t
  val simplify_equivalence_classes : rule list -> rule list
  val automatic_renum : t -> t
  val union : t -> t -> t
  val simplify : t -> t

  val inter : t -> t -> t
  val is_language_empty : t -> bool 

  val normalize_epsilon :
    term ->
      term ->
	transition_table -> transition_table

  val normalize :
    transition_table ->
      transition_table ->
        string -> int -> transition_table * int * alphabet

  val normalize_deterministic :
    transition_table ->
      transition_table ->
        string -> int -> transition_table * int * alphabet

  val matching :
    term ->
      term ->
        (symbol, (state, rule list) folder) folder ->
          substitution list

  val disjointness_constraint :
    term list ->
      (symbol, (state, rule list) folder) folder ->
        term list list 

  val is_recognized_into :
    term ->
      term ->
        (symbol, (state, rule list) folder) folder -> bool

  val run : 
    term ->
      state ->
	t -> bool
    
  val is_covered :
    term ->
      term ->
        transition_table -> bool 

  val determinise : t -> t

  val make_complete : t -> t

  val make_red_automaton :
    alphabet -> transition_table -> t

  val inverse : t -> t
  val subtract : t -> t -> t
  val is_included : t -> t -> bool 
  val nf_automaton :
    alphabet -> transition_table -> t

  (* functions for folders of transitions *)
  val folder_cartesian_product : (symbol, rule list) folder -> (symbol, rule list) folder -> rule list
  val folder_hd : ('a, 'b) folder -> ('a * 'b)
  val folder_tail : ('a, 'b) folder -> ('a, 'b) folder 
  val is_empty_folder : ('a, 'b) folder -> bool
  val folder_assoc : 'a -> ('a, 'b) folder -> 'b
  val folder_add : 'a -> 'b -> (('b , 'a list) folder) -> ('b , 'a list) folder
  val folder_replace : 'a -> 'b -> ('b , 'a) folder -> ('b , 'a) folder
  val bi_folder_add :'a -> 'b -> 'c -> ('b , ('c , 'a list) folder) folder -> ('b , ('c , 'a list) folder) folder
  val bi_folder_mem :
    rule ->
      (symbol ,
       (state , rule list) folder) folder -> bool
  val bi_folder_add_trans_list :
    rule list ->
      (symbol ,
       (state , rule list) folder) folder ->
        (symbol ,
       (state , rule list) folder) folder
  val configs_from_symbol_to_state : 'a -> 'b ->
        ('a , ('b , rule list) folder) folder ->
          term list
  val folder_flatten : ('a , 'b list) folder -> 'b list

  val bi_folder_flatten : ('a , ('b , 'c list) folder) folder -> 'c list
  val transitions_by_symbol :
    rule list ->
      (symbol , rule list) folder
  val transitions_by_state :
    rule list ->
      (state , rule list) folder
  val transitions_by_state_by_symbol :
    rule list ->
      (symbol ,
       (state , rule list) folder) folder
  val make_fast_union: t -> t -> t
end 


module type AUTOMATON_SAVING_TYPE=
sig 
  type automaton
  type alphabet
  type variable_set
  type trs
  type gamma_content
  type spec={alphabet: alphabet; variables: variable_set;
	       trs_list: (string * trs) list;
	       automata_list: (string * automaton) list;
	       gamma_list: (string * gamma_content) list}
  val write_to_disk : spec -> string -> unit
  val save_automaton : automaton -> string ->  string -> unit
  val file_parse : string -> spec
  val get_list_automata : spec -> (string * automaton) list
end


module type GAMMA_TYPE=
sig
  type alphabet
  type variable
  type symbol
  type term= (symbol, variable) term_const
  type substitution= (variable * term) list
  type sol_filt
  type automaton
  type transition_table
  type transition
  type gamma_content
  type variable_set
  type equation
  type ('a, 'b) folder
  type state
  type value_table 
  type norm_rule
  type state_set
  type var_link= (variable list) list
		   
  type rhs_data= {trans: transition list; non_linked_vars: variable list; 
		  linked_vars: var_link; rhs_vars: variable list; 
		  const: sol_filt; vt: (state * value_table) list}
		   
  type rhs_table= rhs_data list
  exception Normalisation_error of string
  exception Error_in_parsing of string
  val out_chan : out_channel ref
  val in_chan : in_channel ref
  val reinit_epsilon : unit -> unit 
  val previous_epsilon : unit -> unit 
  val next_epsilon : unit -> unit 
  val variable_top_state_string : string 
  val varset : variable_set ref
  val is_empty : gamma_content -> bool
  val empty : gamma_content
  val get_new_states: gamma_content -> alphabet
  val set_new_states: alphabet -> gamma_content -> gamma_content
  val add_prior_to_gamma :
    transition_table -> gamma_content -> gamma_content
  val set_prior_in_gamma :
    transition_table -> gamma_content -> gamma_content
  val get_prior : gamma_content -> transition_table
  val get_norm_rules : gamma_content -> norm_rule list
  val set_norm_rules : norm_rule list -> gamma_content -> gamma_content
  val get_equations : gamma_content -> equation list
  val set_equations : equation list -> gamma_content -> gamma_content
  val equations_to_string : equation list -> string
  val norm_rules_to_string:  norm_rule list -> string
  val parse_equations :
    alphabet -> variable_set -> Genlex.token Stream.t -> equation list
  val parse_one_rule:
    alphabet -> alphabet -> variable_set -> Genlex.token Stream.t -> norm_rule
  val eq_lhs : equation -> term
  val eq_rhs : equation -> term
  val new_norm_rule : transition -> transition_table -> norm_rule

  val static_norm : transition_table -> norm_rule list -> (transition list * rhs_table)
  val const_find : variable list -> sol_filt -> (variable * term) list
  val eq_solve : sol_filt -> sol_filt 
  val go: unit -> bool

  val gamma :
    transition_table ->
      (symbol , (state, transition list) folder) folder ->
        gamma_content ->
          alphabet ->
            alphabet ->
              int -> 
		state_set -> transition_table * gamma_content * alphabet * int
		  
  val produce_new_transition : variable ->  state -> substitution -> rhs_data -> (transition_table * rhs_data)

  val parse :
    alphabet ->
      variable_set -> 
	(string * alphabet) list -> Genlex.token Stream.t -> gamma_content

  val to_string :
    gamma_content -> string
end

  
(* <= for lists *)

let subeq_list l1 l2 = 
  List.for_all (function a -> List.mem a l2) l1


let add e l= if List.mem e l then l else e::l


(* Union of l1 and l2 without repetitions (l2 supposed to be without several occurrence of
   the same element *)

let rec union l1 l2=
  match
    l1
  with
      [] -> l2
    | a::l1' -> 
	if List.mem a l2 
	then union l1' l2 
	else union l1' (a::l2) 

(* Intersection of lists *)

let rec inter l1 l2=
  match l1 with
      [] -> []
    | a::rem -> 
	if List.mem a l2 
	then a::(inter rem l2)
	else inter rem l2


(* retrieves repetitions in a list *)
    
let clean l= union l [] 
 
(* remove all occurrence of a given element*)
let delete_all a l =
  let rec aux a l acc=
    match
      l
    with
	[] -> acc
      | b::ll -> if a=b then aux a ll acc else aux a ll (acc@[b])
  in aux a l [] 
      

(* same as map but tail recursive*)
let my_map f l= List.rev (List.rev_map f l)


(* flatten of map (tail recursive)*)
let flat_map f l=
  let rec  aux list acc= 
    match
      list
    with
	[] -> acc
      | fx::llist -> aux llist (acc@(fx))
in   aux  (my_map f l) []   


let my_fold_left f init list=
  let rec aux f  list acc=
    match
      list
    with 
	[] -> acc
      | b::llist -> aux f llist (f acc b)
  in 
  aux f list init

let my_find_all f l=
  let rec aux f  list acc=
    match
      list
    with 
	[] -> acc
      | b::llist ->if (f b) then  aux f llist (acc@[b]) else  aux f llist acc
  in 
  aux f l []

let rec list_make e i=
  if i<=0 then []
  else e::(list_make e (i-1))


