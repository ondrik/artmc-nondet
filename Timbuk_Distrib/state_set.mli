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

(* This is the interface for state sets. See the automaton module for
   a detailed description of the representation of states. State sets
   are sets of states associated with a state content which can be of
   various form: formulas, text, automaton (why not?)
*)

module State_set
  (Symbol_type: PRINTABLE_TYPE)
  (Alphabet_type: ALPHABET_TYPE with type symbol=Symbol_type.t)
  (State_type: TERM_TYPE with type symbol= Symbol_type.t 
			 and type alphabet= Alphabet_type.t)
  (State_content: STATE_CONTENT_TYPE):
sig
  type alphabet= Alphabet_type.t
  type symbol= Symbol_type.t
  type state_content= State_content.t
  type state= State_type.t
  type t

  exception State_not_in_state_set of string
  exception Not_a_state of string
  exception Structured_state_sets of string

  (*s Is a state set structured? *)

  val is_structured: t -> bool

  (*s The empty state set *)  
  val empty : t

  (*s Add a state with no state content to a state set *)
  val add : state -> t -> t

  (*s Add a state with its content *)
  val add_verb : state -> state_content -> t -> t

  (*s Transform a list of state into a state set *)
  val list_to_set : state list -> t

  (*s Extract the list of states from a state set *)
  val to_list : t -> state list 

  (*s Add all states of a list to a state set *)
  val add_all : state list -> t -> t

  (*s Adds a list of states to a set [s1], using their description coming from 
     another set [s2] *)

  val add_all_verb : state list -> t -> t -> t

  (*s Is a state set empty? and is a state member of a state set? *)
  val is_empty : t -> bool
  val mem : state -> t -> bool

  (*s The first element of a state set and the remainder *)
  val first : t -> state
  val remainder : t -> t

  (*s pretty print *)
  val to_string : t -> string

  (*s pretty print in verbose mode, where the content is also
    printed in front of its corresponding state *)
  val to_string_verb : t -> string

  (*s get the state content associated to a state in a state set *)
  val state_description : state -> t -> state_content    


  (*s The default binary symbol used for representing product of
    states *)
  val default_prod_symbol : symbol

  (*s construction of a product state from two states *)
  val state_product: state -> state -> state

  (*s construction of the cartesian product of two state sets (in a
    symbolic way i.e. the cartesian product is not computed *)

  val symbolic_product : t -> t -> t

  (*s boolean operations on state sets *)

  val inter : t -> t -> t
  val union : t -> t -> t
  val minus : t -> t -> t
  val union_disjoint : t -> t -> t

  (*s are all states from the list member of the state set *) 
  val all_mem : state list -> t -> bool

 (*s produce and add to a state operator alphabet [s1] all symbols labeled
     by [str^"k"] where [k] takes the values from [i] to [j] *)

  val produce :
    int -> int -> string -> Alphabet_type.t ->
      Alphabet_type.t

  (*s Parsing of symbols of state set *)
  val parse_ops : Genlex.token Stream.t -> Alphabet_type.t

  (*s Parsing of a state set *)
  val parse :
      alphabet ->
        alphabet -> Genlex.token Stream.t -> t

  (*s Parsing of a state set with associated state contents *)
  val parse_verb:
    alphabet ->
      alphabet -> Genlex.token Stream.t -> t
end
