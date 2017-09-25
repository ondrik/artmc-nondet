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

open Common;;
open Term;;

module State_set(Symbol_type: PRINTABLE_TYPE)(Alphabet_type: ALPHABET_TYPE with type symbol=Symbol_type.t)
  (State_type: TERM_TYPE with type symbol= Symbol_type.t and type alphabet= Alphabet_type.t)
  (State_content: STATE_CONTENT_TYPE)=
struct
  type alphabet= Alphabet_type.t
  type symbol= Symbol_type.t
  type state_content= State_content.t
  type state = State_type.t

  (* A set of state is either a list of states (with their description)
     or a "structured" state set, i.e. the cartesian product between
     two state_sets.

     Be careful, structured state_sets are only a temporary
     representation, and we only define few operations on them
     (membership for example) On the contrary, prettyprint, parsing, first
     element, emptyness test, etc... are not defined (and not necessary)
     and raise an exception. 
  *)

  type t = Set of ((state * state_content) list) | Prod of t * t

  exception  Bad_interval of string
  exception  State_not_in_state_set of string
  exception  Not_a_state of string
  exception  Structured_state_sets of string


  (* is a state set structured? *)

  let is_structured (s: t): bool=
    match s with
	Set(_) -> false
      | Prod(_,_) -> true


  (* The default binary symbol used for representing product of states.
     ex: product of states q1 and q2, become #prod(q1, q2) *)

  let default_prod_symbol = Symbol_type.of_string "#prod"

  let state_product s1 s2 = 
    Fsym(default_prod_symbol, [s1; s2])

  (* The empty state_set *)

  let empty = Set([])

  let is_empty s = match s with
      Set(list) -> list = []
    | _ -> raise (Structured_state_sets "don't know if they are empty")


  (* The first element of a state_set *)
	
  let first set = match set with
      Set(list) -> (match List.hd list with (a,b) -> a)
    | _ -> raise (Structured_state_sets "don't know how to get first element")

  let remainder set = match set with
      Set(list) -> Set(List.tl list)
    | _ -> raise (Structured_state_sets "don't know how to get remainder")


  (* member of a state in a set *)

  let rec mem s set = match set with
      Set(list) -> List.mem_assoc s list

    | Prod(s1,s2) -> 
	if State_type.top_symbol s = default_prod_symbol 
	then 
	  let l_args = State_type.list_arguments s in
	    if (List.length l_args) = 2
	    then 
	      if mem (List.hd l_args) s1
	      then mem (List.hd (List.tl l_args)) s2
	      else false
	    else raise (Structured_state_sets ("mem: Wrong number of arguments in state product term: "^(string_of_int (List.length l_args))))
	else raise (Structured_state_sets ("mem: Bad product symbol name: "^
					   (Symbol_type.to_string 
					      (State_type.top_symbol s))))
	  
	  
  (* Pretty print *)

  let to_string_verb stateset = match stateset with
      Set(list) -> List.fold_right 
	  (function state,content -> function b -> 
	     let descr = (State_content.to_string content) in
	       if (String.length descr) <> 0 
	       then (State_type.to_string state)^": \""^descr^"\"\n"^b
	       else b)
	  list ""
    | _ -> "STATE SET PRODUCT: UNPRINTABLE!!"


  let to_string stateset =  match stateset with
      Set(list) -> List.fold_right 
	  (function state,content -> function b -> 
	     (State_type.to_string state)^" "^b)
	  list ""
    | _ -> "STATE SET PRODUCT: UNPRINTABLE!!"


  let rec state_description s set = match set with
      Set(list) -> 
	(try List.assoc s list
       	 with Not_found -> 
	   raise (State_not_in_state_set ( (State_type.to_string s)^" not in "^
					   (to_string set))))
    | Prod(s1,s2) -> 
	if State_type.top_symbol s = default_prod_symbol 
	then 
	  (let l_args = State_type.list_arguments s in
	     if List.length l_args = 2
	     then 
	       State_content.inter 
		 (state_description (List.hd l_args) s1)
		 (state_description (List.hd (List.tl l_args)) s2)
	     else raise (Structured_state_sets ("state_description: Wrong number of arguments in state product term: "^(string_of_int (List.length l_args)))))
	else raise (Structured_state_sets ("state_description: Bad product symbol name: "^(Symbol_type.to_string (State_type.top_symbol s))))
	  

  let symbolic_product set1 set2 = Prod(set1, set2)


  (* intersection that keeps description part of s1 *)
				     
  let rec inter s1 s2 = match s1 with
      Set([]) -> Set([])
    | Set((state,descr)::liste) -> 
	let reste_inter = inter (Set liste) s2 in
	  (match reste_inter with
	       Set(l_reste) -> 
		 if (mem state s2) 
		 then Set((state,descr)::l_reste)
		 else reste_inter
	     | _ -> raise (Structured_state_sets "inter: cannot have a structured result"))
    | _ -> raise (Structured_state_sets "inter: cannot have a structured first arg")


  (* union that keeps description part of s2 *)

  let rec union s1 s2 = match s1 with
      Set([]) -> s2
    | Set((state,descr)::liste) -> 
	let reste_union = union (Set liste) s2 in
	  (match reste_union with 
	       Set(l_reste) -> 
		 if (mem state reste_union) 
		 then reste_union
		 else Set((state,descr)::l_reste)
	     | _ -> raise (Structured_state_sets "union: cannot have a structured result"))
    | _ -> raise (Structured_state_sets "union: cannot have a structured first argument")


  (* adds all states of two disjoint state_sets *)

  let union_disjoint s1 s2 = match s1,s2 with
      Set(l1),Set(l2) -> Set(List.append l1 l2)
    | _-> raise (Structured_state_sets "union_disjoint: cannot be applied on structured sets")


  (* minus operation on state sets *)

  let minus s1 s2 = 
    let rec aux l1 s2=
      match l1 with
	  [] -> []
	| (state,descr)::l -> 
	    if (mem state s2) then (aux l s2)
	    else (state,descr)::(aux l s2)

    in match s1 with
	Set(l1) -> Set(aux l1 s2)
      | _ -> raise (Structured_state_sets "minus: cannot have a structured first parameter")


  (* tests if all states of a list are in a state set *)

  let all_mem l1 s = List.fold_right
		       (function a -> function b -> (b && mem a s))
		       l1 true
		       

  (* add a state with its description into a state set *)

  let add_verb state description stateset = match stateset with
      Set(list) -> 
      	if mem state stateset then stateset 
      	else Set((state, description)::list)
    | _-> raise (Structured_state_sets "add_verb: cannot be applied on structured sets")


  (* add a state without description into a state set *)

  let add state stateset = match stateset with
      Set(list) -> 
	if mem state stateset then stateset 
      	else Set((state, State_content.empty)::list)
    | _-> raise (Structured_state_sets "add: cannot be applied on structured sets")
	
	
  let list_to_set l = 
    let rec aux l1 l2= 
      match l1 with
	  [] -> l2
	| s::rem -> 
	    if List.mem s l2 
	    then aux rem l2
	    else aux rem (s::l2)
    in Set(List.map (function x -> (x, State_content.empty)) (aux l []))


  let to_list s= 
    match 
      s 
    with  
	Set(l) -> List.map (function a -> match a with (x,y) -> x) l
      | _ -> failwith "not a set -- error in State_set.to_list" 



  (* adds a list of states to a set *)

  let add_all l set = union (list_to_set l) set


  (* adds a list of states to a set, using their description coming from 
     an old_set *)

  let rec add_all_verb l set old_set = match l with
      [] -> set
    | s::rem -> 
	let rest = (add_all_verb rem set old_set) in
      	  (match rest with
	       Set(l_rest) -> 
		 if mem s rest then rest
		 else Set((s,(state_description s old_set))::l_rest)
	     | _ -> raise (Structured_state_sets "add_all_verb: cannot give a structured set as result"))



  (* This function produces and adds to a state_set all states labeled
     by str^"k" where k takes the values from i to j.

     This is used for producing states described by shortcuts of the
     form q[3--20] in the specification *)


  let produce  i j str (set : Alphabet_type.t) = 
    if (i > j) 
    then raise 
      (Bad_interval("["^(string_of_int i)^"--"^
		    (string_of_int j)^"]"))
    else let rec prod_aux i j = 
      if (i > j) 
      then set
      else Alphabet_type.add_symbol 
	(Symbol_type.of_string (str^(string_of_int i))) 0
	(prod_aux (i + 1) j)

    in prod_aux i j
	 

  (* Parsing of symbols of state_set *)
	 (* parsed symbols are either of the form "bob" representing the state
	    bob, or q[3--20] representing states q3, ..., q20, or state
	    operators "trans:2" for example defining an operator on states. In
	    this setting trans(q4,q15) is also a state, build using this
	    operator and states q4 and q15. *)


  let rec parse_ops = parser
      [< 'Genlex.Ident x ; reste= parse_ops_remainder x >] -> reste
	  
    | [< >] -> Alphabet_type.new_alphabet
	
	
  and parse_ops_remainder str = parser
      
      [<'Genlex.Kwd "["; 'Genlex.Int i; 
	'Genlex.Kwd "--"; 'Genlex.Int j ;  'Genlex.Kwd "]";
	(remaining_set : Alphabet_type.t)= parse_ops >] -> produce i j str remaining_set
    | [<'Genlex.Kwd ":"; 'Genlex.Int i;
	(remaining_set : Alphabet_type.t)= parse_ops >] -> 
	Alphabet_type.add_symbol (Symbol_type.of_string str) i remaining_set
	  
    | [<remaining_set = parse_ops >] ->  
	Alphabet_type.add_symbol (Symbol_type.of_string str) 0 remaining_set
	  
    | [< >] ->  Alphabet_type.new_alphabet

	
  let rec parse alphabet alphabet_special = parser
      [< first_state  = 
	   State_type.parse_ground_special alphabet alphabet_special; 
	 remaining_set = parse alphabet alphabet_special>] ->
	(match first_state with
	     Special(q) -> add q remaining_set
	   | x -> raise (Not_a_state ((State_type.to_string x)^
				      " is not a valid state")))
    |	[< >] -> empty


  (* For parsing states with their description *)

  let rec parse_verb alphabet alphabet_special = parser
      [< first_state  = 
	   State_type.parse_ground_special alphabet alphabet_special; 
	 'Genlex.Kwd ":";
	 'Genlex.String descr;
	 remaining_set = parse_verb alphabet alphabet_special>] ->
	(match first_state with
	     Special(q) -> 
	       add_verb q (State_content.of_string descr) remaining_set
		 
	   | x -> raise (Not_a_state ((State_type.to_string x)^
				      " is not a valid state")))
    |	[< >] -> empty

end

