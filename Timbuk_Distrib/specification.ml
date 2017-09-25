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

module Specification
  (Alphabet_type: ALPHABET_TYPE)
  (Variable_set_type: VARIABLE_SET_TYPE)
  (Term_type: TERM_TYPE with type alphabet= Alphabet_type.t)
  (TRS_type: TRS_TYPE with type alphabet= Alphabet_type.t and type variable_set= Variable_set_type.t)
  (Automata_type: AUTOMATA_TYPE with type alphabet= Alphabet_type.t 
				and type term= Term_type.t)
  (Gamma_type: GAMMA_TYPE with type variable_set= TRS_type.variable_set
			  and type alphabet= TRS_type.alphabet)=
struct
  type alphabet = Alphabet_type.t	
  type variable_set = Variable_set_type.t
  type trs = TRS_type.t
  type automaton= Automata_type.t
  type gamma_content= Gamma_type.gamma_content

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

(* obtain the alphabet of the specification *)

  let get_alphabet spec= spec.alphabet


(* obtain the variables of the specification *)

  let get_variables spec= spec.variables

(* obtain a trs from a specification thanks to its name (string) *)

  let get_trs name spec = 
    try List.assoc name spec.trs_list
    with Not_found -> raise (No_TRS_of_that_name (name^" in the specification"))

(* obtain the list of named trs a specification *)

  let get_list_trs spec = spec.trs_list

(* obtain an automaton from a specification thanks to its name (string) *)

  let get_automaton name spec = 
    try List.assoc name spec.automata_list
    with Not_found -> raise (No_automaton_of_that_name (name^" in the specification"))


(* obtain the list of named automata of a specification *)

  let get_list_automata spec = spec.automata_list


(* obtain an approximation from a specification thanks to its name (string) *)

  let get_approximation name spec = 
    try List.assoc name spec.gamma_list
    with Not_found -> raise (No_approximation_of_that_name (name^" in the specification"))


(* obtain the list of named approximation of a specification *)

  let get_list_approximation spec = spec.gamma_list


(* The lexer for the specification langage *)

  let lexer = Genlex.make_lexer [",";"(";")";"Ops";"Vars";":";
				 "TRS";"->";"Automaton";"States";
				 "Final";"Transitions";"Description"; "Set";
				 "--";"[";"]";"Prior";"Rules"; "Approximation";"=";"Equations";"Import"]

(* Prettyprint functions *)
		
  let rec named_trs_to_string l = match l with
      [] -> "\n"
    | (name, trs)::l2 -> "TRS "^name^"\n\n"^
	(TRS_type.to_string trs)^
	"\n\n"^
	(named_trs_to_string l2)
	
  let rec named_automaton_to_string l = match l with
      [] -> "\n"
    | (name, aut)::l2 -> "Automaton "^name^"\n\n"^
	(Automata_type.to_string aut)^
	"\n\n"^
	(named_automaton_to_string l2)

  let rec named_approximation_to_string l = match l with
      [] -> "\n"
    | (name, aut)::l2 -> 
	if Gamma_type.is_empty aut then (named_approximation_to_string l2)
	else "Approximation "^name^"\n\n"^
	  (Gamma_type.to_string aut)^
	  "\n\n"^
	  (named_approximation_to_string l2)


  let to_string spec = "Ops "^
		       (Alphabet_type.to_string spec.alphabet)^
		       (if (Variable_set_type.is_empty spec.variables)
			then "" 
			else "\n\nVars "^
			  (Variable_set_type.to_string spec.variables))^
		       "\n\n"^
		       (named_trs_to_string spec.trs_list)^
		       "\n\n"^
		       (named_automaton_to_string spec.automata_list)^
		       "\n\n"^
		       (named_approximation_to_string spec.gamma_list)


(* General Parsing of a specification *)
(* a specification may contain or not a variable declaration and 
   any number of named TRS and named automata in any order *)

(* Example of specification:  in spec.txt *)

  let rec parse = parser 
      [< 'Genlex.Kwd "Ops" ; 
	 new_alpha = Alphabet_type.parse;
	 vars = parse_var_part;
	 spec = parse_trs_and_aut new_alpha vars [] [] [] >] -> 
	let lsymb= Alphabet_type.to_string_list new_alpha in
	let lvar= Variable_set_type.to_string_list vars in
	let symb_var= Common.inter lsymb lvar in
	  if symb_var = [] then spec
	  else raise (Name_used_twice (String.concat " " symb_var))
	  
  and parse_var_part = parser
      [< 'Genlex.Kwd "Vars" ;
	 new_var_set = Variable_set_type.parse >] -> new_var_set
    |	[< >] -> Variable_set_type.empty
	  
  and parse_trs_and_aut alpha var_set 
    (l_trs : (string * trs) list)
    (l_aut : (string * automaton) list) 
    (l_approx : (string * gamma_content) list)
    = parser
	
	[< 'Genlex.Kwd "TRS"; 
	   name= parse_name "TRS" alpha var_set;
	   a_trs = TRS_type.parse alpha var_set;
	   spec = parse_trs_and_aut alpha var_set 
	            ((name, TRS_type.check a_trs alpha)::l_trs) l_aut l_approx
	>] -> 
	  if ((List.mem_assoc name l_trs) or
	      (List.mem_assoc name spec.automata_list) ||
	      (List.mem_assoc name spec.gamma_list))
	  then raise (Name_used_twice name)
	  else spec
	    
      | [< 'Genlex.Kwd "Set";
	   name= parse_name "Set" alpha var_set;
	   term_list= Term_type.parse_ground_term_set alpha;
	   spec= parse_trs_and_aut alpha var_set
		   l_trs
		   ((name, fst (Automata_type.term_set_to_automaton alpha term_list "qterm" 0))::l_aut)
		   l_approx
	>] ->  
	  if ((List.mem_assoc name l_aut)  or
	      (List.mem_assoc name spec.trs_list) ||
	      (List.mem_assoc name spec.gamma_list))
	  then raise (Name_used_twice name)
	  else spec  

      |	[< 'Genlex.Kwd "Automaton"; 
	   name= parse_name "Automaton" alpha var_set;
	   an_aut = Automata_type.parse alpha;
	   spec = parse_trs_and_aut alpha var_set 
	            l_trs 
	            ((name, an_aut)::l_aut)
		    l_approx
	>] -> 
	  
	  if ((List.mem_assoc name l_aut)  or
	      (List.mem_assoc name spec.trs_list) ||
	      (List.mem_assoc name spec.gamma_list))
	  then raise (Name_used_twice name)
	  else spec   
	    
      | [< 'Genlex.Kwd "Approximation";
	   name= parse_name "Approximation" alpha var_set;
	   an_approx = Gamma_type.parse alpha var_set (List.map (function (x, y) -> (x,Automata_type.get_state_ops y))l_aut);
	   spec= parse_trs_and_aut alpha var_set
		   l_trs l_aut
		   ((name, an_approx)::l_approx) >] ->
	  if ((List.mem_assoc name spec.automata_list)  or
	      (List.mem_assoc name spec.trs_list) ||
	      (List.mem_assoc name l_approx))
	  then raise (Name_used_twice name)
	  else spec   


      |	[< >] -> {alphabet = alpha; variables = var_set ;
		  trs_list = (List.rev l_trs); automata_list = (List.rev l_aut);
		  gamma_list = (List.rev l_approx)}

  and parse_name (kwd: string) alpha varset= parser
      [< 'Genlex.Ident name >] -> 
	if List.mem name (Alphabet_type.to_string_list alpha) or
	  List.mem name (Variable_set_type.to_string_list varset) 
	then raise (No_name ("Missing or bad name after keyword "^kwd))
	else name
    | [< >] -> raise (No_name ("Missing or bad name after keyword "^kwd))
	  
	  
(* Parsing a specification in a given file (string) *)

	    
  let file_parse (filename:string) =
    let inchan = open_in filename in
    let instream = Stream.of_channel inchan in
      try(
	let specif = parse (lexer instream) in 
	let _ = close_in inchan in specif)
      with x -> let _ = close_in inchan in 
	raise x
		
(* Writing a specification into a given file (string) *)			 
	
  let write_to_disk (s: spec)(filename: string)=
    let outchan = open_out filename in
      try(
	let _= Printf.fprintf outchan "%s" (to_string s) in
	  close_out outchan)
      with x -> let _= close_out outchan in
	raise x

(* Writing a tree automaton with its assigned name into a given file (string) *)			 
	
  let save_automaton (a: automaton) (name: string)(filename: string)=
    let checked_name= if name="" then "NO_NAME" else name in
    let temp_spec= {alphabet= (Automata_type.get_alphabet a);
		    variables= Variable_set_type.empty;
		    trs_list= [];
		    gamma_list= [];
		    automata_list= [(checked_name, a)]} in
    let outchan = open_out filename in
      try(
	let _= Printf.fprintf outchan "%s" (to_string temp_spec) in
	  close_out outchan)
      with x -> let _= close_out outchan in
	raise x


end
	


