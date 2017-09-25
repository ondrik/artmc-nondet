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

(*i Be careful! Some comments of this file are formatted for ocamlweb. *)

(*i*)
open Common
(*i*)
   (* This is the interface for the gamma approximation module. The role
      of the gamma function is to realize an approximate normalisation of
      new transition in order to make completion terminate as often as
      possible. This function is defined thanks to a database called
      [gamma_content] which can be enriched during completion. The role of
      this database is to store rules of normalisation, events encountered
      during the completion, ... or anything necessary for making good
      heuristical choices for normalisation of new critical pairs. The gamma
      content as well as the gamma function itself can be defined by
      the user. However we propose one simple gamma function here
      which is very simple and only take into account a set of
      prior transitions (see [tutorial_compl.mlml] for more
      details on prior transitions) in the [gamma_content]
      database. This set of prior transitions is being enriched
      by the user during completion and used for normalising
      transitions before giving them to an interactive normalisation process.

 *)


module Gamma 
  (Symbol_type: PRINTABLE_TYPE)
  (Alphabet_type: ALPHABET_TYPE with type symbol= Symbol_type.t)
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
							and type state_set= State_set_type.t):
sig
  type alphabet= Alphabet_type.t
  type automaton= Automata_type.t
  type state = Automata_type.state
  type transition_table= TRS_type.t
  type transition= TRS_type.rule
  type variable_set= Variable_set_type.t
  type variable= Variable.t
  type substitution= Term.substitution
  type gamma_content
  type state_set= State_set_type.t
  type ('a, 'b) folder= ('a, 'b) Automata_type.folder
  type symbol= Symbol_type.t
  type rule= TRS_type.rule
  type term= (symbol, variable) term_const
  type sol_filt= Automata_type.sol_filt
  type value_table 
  type norm_rule
  type equation
  type var_link= (variable list) list
  type rhs_data= {trans: transition list; non_linked_vars: variable list; 
		  linked_vars: var_link; rhs_vars: variable list; 
		  const: sol_filt; vt: (state * value_table) list}
		   
  type rhs_table= rhs_data list

  exception Normalisation_error of string
  exception Error_in_parsing of string

  (* a variable set for parsing of interactively typed norm rules *)
  val varset : variable_set ref

  val reinit_epsilon : unit -> unit 
  val previous_epsilon : unit -> unit 
  val next_epsilon : unit -> unit 

  val variable_top_state_string : string 

  (*s the empty gamma content of gamma approximation *)
  val empty : gamma_content

  (*s is a gamma content empty *)
  val is_empty : gamma_content -> bool

  (*s set and get new states *)
  val get_new_states: gamma_content -> alphabet
  val set_new_states: alphabet -> gamma_content -> gamma_content

  (*s adding a prior transition table to the gamma content *) 
  val add_prior_to_gamma :
    transition_table -> gamma_content -> gamma_content

  (*s setting the gamma content to a new prior transition table *)
  val set_prior_in_gamma :
    transition_table -> gamma_content -> gamma_content

  (*s getting back the transition table from the gamma content *)
  val get_prior : gamma_content -> transition_table

  (*s getting the current strategy of gamma *)
  val get_strategy : gamma_content-> string list
      
  (*s setting the strategy in the gamma content *)    
  val set_strategy : string list -> gamma_content -> gamma_content

  (*s getting the norm rules of a gamma content *)
  val get_norm_rules : gamma_content -> norm_rule list

  (*s setting the norm rules of a gamma content *)
  val set_norm_rules : norm_rule list -> gamma_content -> gamma_content

  (*s creating a new [norm_rule] *)
  val new_norm_rule : transition -> transition_table -> norm_rule

  (*s obtaining or setting approximation equations *)

  val get_equations : gamma_content -> equation list
      
  val set_equations : equation list -> gamma_content -> gamma_content
      
  (* equations parsing and pretty printing *) 

  val equations_to_string : equation list -> string
      
  val parse_equations :
    alphabet -> variable_set -> Genlex.token Stream.t -> equation list

  val parse_one_rule:
    alphabet -> alphabet -> variable_set -> Genlex.token Stream.t -> norm_rule

  val norm_rules_to_string:
    norm_rule list -> string

  (*s respectively left and right hand side of equations *)

  val eq_lhs : equation -> term
  val eq_rhs : equation -> term

  val get_new_states : gamma_content -> alphabet

  (*s the parsing function for gamma content *)
  val parse :
    alphabet ->
      variable_set ->
	(string * alphabet) list -> Genlex.token Stream.t -> gamma_content

  (*s static normalisation of a transition table with variables w.r.t. a norm rule list, produces a list
      of rules (with renamed variables) and the corresponding rhs statically normalised *)
  val static_norm : transition_table -> norm_rule list -> (transition list * rhs_table)

  (*s simplification of [sol_filt] constraint *)
  val eq_solve : sol_filt -> sol_filt 

  (* Finding all positive (and not under a disjunction) constraints (associated to variables given in a list)
     into a more general constraint *)

  val const_find : variable list -> sol_filt -> (variable * term) list

  (*s the function that given a state variable, a state, a substitution
      and a rhs\_table produces a list of new transition and an updated rhs\_table *)	  
  val produce_new_transition : variable ->  state -> substitution -> rhs_data -> (transition_table * rhs_data)

  (*s the pretty printing function for gamma content *)
  val to_string :
    gamma_content -> string

  (*s The gamma function used for approximation of new transitions
  obtained during completion.  The [new_trans] are the new transitions
  to be normalised, [delta] is the transition table of the current
  completion step (stored into a folder for a better efficiency), 
  [a] is the alphabet and [stops] are the state 
  operators set on which transitions are defined, and finally [i] is
  the index of the lastly created new state. After an application of
  one step of gamma, the gamma content is updated, the new state
  operators contains all initial state operators as well as new state
  operators given by the user or constructed automatically as new
  states. The index has been incremented if automatic new states have been
  constructed *)

  val gamma :
    transition_table ->
      (symbol , (state, transition list) folder) folder ->
        gamma_content ->
          alphabet ->
            alphabet ->
              int -> 
		state_set -> transition_table * gamma_content * alphabet * int

  (*i*)
  val go: unit -> bool

(*i*)

  (*s the in and out channel used for user interaction *)
  val out_chan : out_channel ref
  val in_chan : in_channel ref


end
