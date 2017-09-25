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

(* This is the interface for rewrite rules and rewrite systems
   constructed on an alphabet $\F$, a set of variables $\X$ and a set
   of terms $\TFX$ *)

module RewriteSystem
  (Alphabet_type: ALPHABET_TYPE)
  (Variable_set_type: VARIABLE_SET_TYPE)
  (Term_type: TERM_TYPE with type variable_set= Variable_set_type.t 
			and type alphabet= Alphabet_type.t):
sig
  type alphabet= Alphabet_type.t
  type variable_set= Variable_set_type.t
  type term = Term_type.t
  type ruleSystem
  type t = ruleSystem
  type rule

  exception Variable_rhs_not_included_in_lhs of string
  exception Does_not_rewrite_on_top
  exception Badly_formed_rule of string 
    
  (*s the empty trs and other constructors *)
  val empty : t
  val new_rule : term -> term -> rule
  val is_empty : t -> bool
  val mem : rule -> t -> bool

  (*s adding a rule in a trs, and union of two trs *)
  val add : rule -> t -> t
  val union : t -> t -> t
      
  (*s if the rule is not in the trs we can catenate 
     without testing membership *) 
  val add_fast : rule -> t -> t
      
  (*s if trs are known to be disjoint we can catenate 
     without testing membership for union *) 
  val union_fast : t -> t -> t


  (*s first rule of a ruleSystem and remainder of the system *)
  val first : t -> rule
  val remainder : t -> t

  (* nth rule of the system (in the parsing order) *)
  val nth : t -> int -> rule

  (*s right-hand side and left-hand side of a rule *)
  val rhs : rule -> term
  val lhs : rule -> term

  (*s equality on rules *)
  val rule_equal : rule -> rule -> bool

  (*s is a rule left or right or left and right linear ?*)

  val is_ground : rule -> bool
  val is_left_linear : rule -> bool
  val is_right_linear : rule -> bool
  val is_linear : rule -> bool
      
  (*s list of non linear lhs of a ruleSystem *)

  val non_linear_lhs : t -> term list


  (*s intersection of two trs *)

  val inter : t -> t -> t

  (*s moving from list to ruleSystem and conversely *)

  val to_list : t -> rule list
  val list_to_trs : rule list -> t
      
  (*s prettyprint *)
  val rule_to_string : rule -> string
  val to_string : t -> string

  (*s renaming every variable of a rule: adding a string to the end of every variable label *)
  val rename_rule_var : rule -> string -> rule

  (*s renaming every variable of a rewrite system: adding a string to the end of every variable label *)
  val rename_var : t -> string -> t

  (*s Checking one rule with regards to an alphabet: checks construction of
     lhs and rhs as well as inclusion of var(rhs) in var(lhs) *) 
  val check_rule : rule -> alphabet -> rule
    
  (*s Checking a trs with regards to an alphabet: checks construction of
     lhs and rhs as well as inclusion of var(rhs) in var(lhs) *) 
  val check : t -> alphabet -> t

  (*s parsing of a rule, given an alphabet [a] variable set [varset] *)
  val parse_rule :
    alphabet ->
      variable_set -> Genlex.token Stream.t -> rule
	

  (*s parsing of a trs given an alphabet [a] variable set [varset] *)
						      
  val parse :
      alphabet ->
        variable_set -> Genlex.token Stream.t -> t

  (*s rewrite once on top position of term [t1] with any rule of trs [r] *)

  val rewrite_top_once : t -> Term_type.t -> Term_type.t


  (*s leftmost innermost normalisation of the term [t1] thanks to a trs [r]. Of course TRS should terminate!*)
  val left_inner_norm : t -> Term_type.t -> Term_type.t

  (*s bottom up normalisation of term [t1] thanks to trs [r]. Useful
     when the trs is a transition table of an automaton *)

  val bottom_up_norm : t -> Term_type.term -> Term_type.t


  (*s similar functions but for rules and trs built on special terms ... *)

  val check_special_rule :
    rule -> alphabet -> alphabet -> rule
  val check_special :
    t -> alphabet -> alphabet -> t
  val parse_special_rule :
    alphabet ->
      alphabet ->
        variable_set -> Genlex.token Stream.t -> rule
  val parse_special :
    alphabet ->
      alphabet ->
        variable_set -> Genlex.token Stream.t -> t

  val parse_ground_special :
    alphabet ->
      alphabet -> Genlex.token Stream.t -> t
  val parse_ground_special_rule :
    alphabet -> alphabet -> Genlex.token Stream.t -> rule

  val left_inner_norm_special :
    t -> Term_type.t -> Term_type.t

  val left_inner_norm_special_system :
    t -> t -> t

end 
