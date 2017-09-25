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

(* This is the interface for specifications. What we call a
   specification is a collection of term rewriting systems and bottom-up
   tree automata all defined on a common alphabet. 
   Consequenlty, this module is defined thanks to an alphabet
   type, a variable set type (used to define rewrite rules), a term
   rewriting system type and an automata type. Term rewriting system
   and tree automata are all assigned with a name (a
   string) in the specification. The simplest way to construct a
   specification is to write it in a file and parse it thanks to the
   [file_parse] function. For a {\bf sample specification file}, please look at the
   file [example.txt] contained is the distribution. *) 


module Specification
  (Alphabet_type: ALPHABET_TYPE)
  (Variable_set_type: VARIABLE_SET_TYPE)
  (Term_type: TERM_TYPE with type alphabet= Alphabet_type.t)
  (TRS_type: TRS_TYPE with type alphabet= Alphabet_type.t 
		      and type variable_set= Variable_set_type.t)
  (Automata_type: AUTOMATA_TYPE with type alphabet= Alphabet_type.t
				and type term= Term_type.t)
  (Gamma_type: GAMMA_TYPE with type variable_set= TRS_type.variable_set
			  and type alphabet= TRS_type.alphabet):
sig
  type alphabet = Alphabet_type.t
  type variable_set = Variable_set_type.t
  type trs = TRS_type.t
  type automaton = Automata_type.t
  type gamma_content = Gamma_type.gamma_content
  type spec = {alphabet: alphabet; variables: variable_set;
	       trs_list: (string * trs) list;
	       automata_list: (string * automaton) list;
	       gamma_list: (string * gamma_content) list}

  type t = spec
  exception Name_used_twice of string
  exception No_TRS_of_that_name of string
  exception No_automaton_of_that_name of string
  exception No_approximation_of_that_name of string
  exception No_name of string


  (*s Parsing of a specification in a file of name [file_name]. *)
  val file_parse :  string -> spec

  (*s Lexer for specifications *)

  val lexer : char Stream.t -> Genlex.token Stream.t 

  (*s Get the alphabet of a specification [s]. *)

  val get_alphabet : spec -> alphabet


  (*s Get the set of variables of a specification [s]. *)
  
  val get_variables : spec -> variable_set

      
  (*s Get the term rewriting system named [name] in the specification [s]. *) 
  
  val get_trs :  string -> spec -> trs
   
   
  (*s Get the list of named term rewriting systems of a specification [s]. *) 

  val get_list_trs : spec -> (string * trs) list

  (*s Get the automaton named [name] in the specification [s]. *) 

  val get_automaton :  string -> spec -> automaton


 (*s Get the list of named automata of a specification [s]. *) 

  val get_list_automata : spec -> (string * automaton) list


  (*s Get the approximation named [name] in the specification [s]. *) 

  val get_approximation:  string -> spec -> gamma_content
      
  
  (*s Get the list of named approximation of a specification [s]. *) 

  val get_list_approximation : spec -> (string * gamma_content) list 

      
  (*s Pretty print of a specification [s].*)

  val to_string : spec -> string


  (*s Writing a specification [s] to a file named [file_name].*)

  val write_to_disk : spec ->  string -> unit


  (*s Saving an automaton [a] under the name [aut_name] in a
    specification file named [file_name]. *)

  val save_automaton : automaton ->  string ->  string -> unit
end


