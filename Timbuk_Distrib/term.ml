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

open Variable_set
open Variable
open Common

module Term(Symbol_type: PRINTABLE_TYPE)(Alphabet_type: ALPHABET_TYPE with type symbol= Symbol_type.t)
  (Variable_type: PRINTABLE_TYPE)(Variable_set_type: VARIABLE_SET_TYPE with type variable= Variable_type.t)=
struct

  (* A term is either a variable, a constant, a functionnal symbol with a
     list of subterms, or a special term.
     A special term is build on a union of the alphabet and a
     special alphabet.
     
     For example, let F={f:2, g:1, a:0} an alphabet and F'={prod:2, q:0, 
     h:2} a special alphabet.

     Then f(g(a),g(prod(q,h(g(q),q)))) is a term where prod(q,h(g(q),q)) is a
     special subterm. The Special() constructor used in the
     implementation to separate the special subterms in a term.
  *)

  type symbol= Symbol_type.t
  type variable= Variable_type.t
  type alphabet= Alphabet_type.t
  type variable_set= Variable_set_type.t
  type term = (Symbol_type.t, Variable_type.t) term_const
  type t= term
	    (*
	      type term =  
	      Var of Variable_type.t
	      | Const of Symbol_type.t
	      | Fsym of (Symbol_type.t * term list)
	      | Special of term
	    *)

  (* substitution of special terms *)

  type special_subst = (term * term) list

  type substitution = (Variable_type.t * term) list

  exception Terms_do_not_match of string * string
  exception Terms_do_not_unify of string * string

  exception Badly_formed_term of string
  exception Undefined_symbol of string 
  exception Bad_operation_on_special_term of string
  exception Bad_operation_on_var of string
  exception Parse_error of string

  let linearize_string= ":lin_"

  let equal = (=)
		
  (* Depth of a term *)

  let rec depth t= 
    let rec max l= 
      match l with
	  [] -> 0
	| e::lrem -> 
	    let mxrem = (max lrem) in
	      if e>mxrem then e else mxrem
		
    in
      match t with
	  Const(_) -> 0
	| Special(_) -> 0
	| Var(_) -> 0
	| Fsym(_, largs) -> 1+ (max (Common.my_map depth largs))


  (* Pretty print *)

  let rec to_string term = match term with 
      Fsym(symbol, l_subterms) -> 
    	String.concat "" [(Symbol_type.to_string symbol); "(";
			  String.concat "," (Common.my_map to_string l_subterms);
			  ")"] 
    | Const(c) -> (Symbol_type.to_string c)
    | Special(t) -> (to_string t)
    | Var(x) -> (Variable_type.to_string x)


  (* Top symbol of a term *)

  let top_symbol term = match term with
      Fsym(f,_) -> f
    | Const(f) -> f
    | Special(x) -> raise (Bad_operation_on_special_term 
			     ("top_symbol applied on "^(to_string x)))
    | Var(x) -> raise (Bad_operation_on_var ("top_symbol applied on "^
					     (Variable_type.to_string x)))

  (* List of arguments *)

  let list_arguments term = match term with
      Fsym(_,l) -> l
    | Const(_) -> []
    | Special(x) -> raise (Bad_operation_on_special_term 
			     ("list_arguments applied on "^(to_string x)))
    | Var(x) -> raise (Bad_operation_on_var ("list_arguments applied on "^(Variable_type.to_string x)))


  (* is a term a variable ?*)

  let is_variable term = match term with
      Var(x) -> true |
	_ -> false

  (* is a term a constant ?*)

  let is_constant term = match term with
      Const(a) -> true |
	_ -> false
			  
  (* is a term special? *)

  let is_special term = match term with
      Special(x) -> true |
	_ -> false

  (* get the special content of a special term *)

  let get_special term= match term with
      Special(t) -> t
    | t -> failwith ("Trying to get special content of non special term: "^
		     (to_string t))
	

  (* the map combinator on terms *)

  let rec map f1 f2 term = match term with
      Fsym(symbol, l_subterms) -> Fsym(f1 symbol, 
				       Common.my_map (map f1 f2) l_subterms) 
    | x -> f2 x

  (* the map combinator on special terms *)

  let rec map_special f1 f2 term = match term with
      Fsym(symbol, l_subterms) -> Fsym(f1 symbol, 
				       Common.my_map (map_special f1 f2) l_subterms) 
    | Special(t) -> Special((map_special f1 f2 t)) 
    | x -> f2 x


  let id x = x


  (* get the list of the leaves of a term *)

  let rec list_leaves term = match term with
      Fsym(symbol, l_subterms) -> 
    	List.fold_left List.append [] 
	  (Common.my_map (list_leaves) l_subterms) |
	    x -> [x]


  (* get the list of variables of a term (with possible redundancy) *)

  let rec list_variables term = match term with
      Fsym(symbol, l_subterms) -> 
    	List.fold_left List.append [] 
	  (Common.my_map (list_variables) l_subterms) 
    | Var(x) -> [x]
    | _ -> []


  (* get the list of non linear variables of a term (with no redundancy) *)
	
  let list_non_linear_variables (t: term): variable list=
    let rec var_aux (l: variable list) (found: variable list): variable list=
      match l with 
	  [] -> found
	| v::rem -> 
	    if List.mem v rem 
	    then 
	      if List.mem v found 
	      then var_aux rem found
	      else var_aux rem (v::found)
	    else var_aux rem found
    in
    let variables= list_variables t in
      var_aux variables []


  (* rename variables of a term: add a string [s] to the end of every variable name *)
  let var_change (v: variable) (s: string): variable= 
    Variable_type.of_string (s ^ (Variable_type.to_string v))

  let rename_var term (s: string): term= 
      map id (function t -> match t with Var(x) -> Var((var_change x s)) | a -> a) term

  (* linearize a term: produces a linear version of a term [t] associated with the variable 
     renamings that have been operated in order to make the term linear. *)

  let linearize (t: term): (term * (variable * (variable list)) list)=
    let non_lin= list_non_linear_variables t in
    let rec make_list (x: variable) (i: int): variable list=
      match i with
	  0 -> []
	| _ -> (var_change x (linearize_string^(string_of_int i)))::(make_list x (i - 1))
    in
    let rec aux (t: term) (occurrences: (variable * int) list): (term * ((variable * int) list))=
      (match t with 
	  Const(_) | Special(_) -> (t, occurrences)
	| Var(x) -> 
	    if List.mem x non_lin 
	    then 
	      let current_nb= List.assoc x occurrences in
		((Var(var_change x (linearize_string^(string_of_int current_nb)))),
		  ((x, current_nb + 1)::(List.remove_assoc x occurrences)))
	    else (t, occurrences)
	| Fsym(f, largs) -> 
	    let (new_args, new_occ)= aux_list largs occurrences in
	      (Fsym(f, new_args), new_occ))

    and aux_list (lt: term list) (occurrences: (variable * int) list): (term list * ((variable * int) list))=
      match lt with 
	  [] -> ([], occurrences)
	| t::rem ->
	    let (new_t, new_occ)= aux t occurrences in
	    let (new_rem, new_occ2)= aux_list rem new_occ in
	      (new_t::new_rem, new_occ2)
      
    in
      if non_lin= [] then (t,[])
      else 
	let (new_t, occurrences)= 
	  aux t (List.map (function x -> (x, 1)) non_lin) 
	in
	  (new_t, List.map (function (x, i) -> (x, (make_list x i))) occurrences)
	

  (* is a term ground ? *)

  let is_ground term = (list_variables term) = []


  (* is a term linear? i.e. there is only one occurence of each variable in the term *)

  let is_linear term= 
    let rec aux l=
      match l with 
	  [] -> true
	| t::lrem -> if List.mem t lrem then false else aux lrem
    in aux (list_variables term)

  (* list special subterms of a term *)

  let rec list_special term = match term with
      Fsym(symbol, l_subterms) -> 
    	List.fold_left List.append [] 
	  (Common.my_map list_special l_subterms) 
    | Special(t) -> [t]
    | _ -> []


  (* Check the consistency of a term with regards to an alphabet and a
     special alphabet *)

  let rec check_special alphabet alphabet_special term = match term with
      Var(x) -> Var(x) 
    | Const(f) -> (try 
		     (if ((Alphabet_type.get_arity f alphabet) = 0) then Const(f)
      		      else raise (Badly_formed_term (to_string term))) with 
			 Alphabet_type.Symbol_not_in_alphabet(_) -> raise (Undefined_symbol 
					       (String.concat " " ["symbol"; 
								   (Symbol_type.to_string f);
								   "undefined in term";
								   (to_string term)])))
    | Fsym(f,l_args) -> (try 
			   (if ((Alphabet_type.get_arity f alphabet) = (List.length l_args))
			    then Fsym(f, (Common.my_map (check_special alphabet alphabet_special) l_args))
			    else raise (Badly_formed_term (to_string term))) with 
			       Alphabet_type.Symbol_not_in_alphabet(_) -> raise (Undefined_symbol 
						     (String.concat " " ["symbol";
									 (Symbol_type.to_string f);
									 "undefined in term";
									 (to_string term)])))
    | Special(t) -> Special(check_special 
			      (Alphabet_type.union_fast alphabet_special 
				 alphabet)
			      Alphabet_type.new_alphabet t)


  (* Check the consistency of a term with regards to an alphabet *)
	
  let check alphabet term = 
    check_special alphabet Alphabet_type.new_alphabet term


  (* replacement in special terms *)

  let replace_special spec_subst term = 
    map id (function 
		Special(t) -> (try List.assoc t spec_subst with
				   Not_found -> Special(t))
	      | x -> x) term


  (* Application of a substitution to a term of depth  1 *)

  let apply_depth1 subst term = match term with
      Var(x) -> (try List.assoc x subst with
		     Not_found -> Var(x)) |
	x -> x


  (* Generalisation of substitution to terms with any depth thanks to 
     the combinator on terms: Term.map *)

  let apply subst term = map id (apply_depth1 subst) term

  (* Generalisation of substitution to special terms with any depth thanks to 
     the combinator on terms: Term.map_special *)

  let apply_special subst term = map_special id (apply_depth1 subst) term


  (* Application of a list of substitution to a term *)

  let apply_several lsubst term = Common.my_map (function s -> apply s term) lsubst


  (* Application of a list of substitution to a list of terms *)

  let apply_substs_on_terms lsubst lterm = List.flatten (Common.my_map (apply_several lsubst) lterm)


  (* Parsing of a term with special subterms *)

  let rec parse_special alphabet alphabet_special variable_set = 
    parser
	[< 'Genlex.Ident f; a_term = parse_args f alphabet 
				       alphabet_special variable_set >] -> a_term
      |	[< 'Genlex.Int i >] -> raise (Parse_error ("Parse error on int: "^(string_of_int i))) 
	

  and parse_args f alphabet alphabet_special variable_set = 
    let symb= Symbol_type.of_string f in
      if Alphabet_type.occur symb alphabet
      then 
	parser
    	    [< 'Genlex.Kwd "("; 
	       l_terms = parse_list_terms f alphabet 
			   alphabet_special variable_set >] -> Fsym(symb, l_terms)
	  | [< >] -> 
	      if Alphabet_type.get_arity symb alphabet = 0 
	      then Const(symb)
	      else raise (Undefined_symbol ("No arguments given to non-constant symbol "^f))
      else 
	if Alphabet_type.occur symb alphabet_special
	then 
	  parser
    	      [< 'Genlex.Kwd "("; 
		 l_terms = parse_list_terms f 
			     (Alphabet_type.union_fast alphabet alphabet_special)
			     Alphabet_type.new_alphabet variable_set >] -> Special(Fsym(symb, l_terms))
	    | [< >] -> 
	      	if Alphabet_type.get_arity symb alphabet_special = 0 
	      	then Special(Const(symb))
	      	else raise (Undefined_symbol 
			      ("No arguments given to special non-constant symbol "^f))
	else let var1= Variable_type.of_string f in 
	  parser
	      [< >] -> if Variable_set_type.mem var1 variable_set 
	      then  Var(var1)
	      else raise (Undefined_symbol f)
		

  (* We chose not to accept variables in special terms but... why not? *)

  and parse_list_terms f alphabet alphabet_special variable_set = parser
      [< a_term = parse_special alphabet alphabet_special variable_set ; 
	 l_term = parse_list_term_remainder f alphabet 
	            alphabet_special variable_set >] ->
	a_term::l_term
  and parse_list_term_remainder f alphabet alphabet_special variable_set = parser
      [< 'Genlex.Kwd ","; 
	 l_term = parse_list_terms f alphabet alphabet_special variable_set>] -> l_term
    | [< 'Genlex.Kwd ")" >] -> []
    | [< >] -> raise (Badly_formed_term ("'(' unmatched in the term "^f^"(..."))
	

  (* Parsing of non-special terms *)

  let parse alphabet varset = 
    parse_special alphabet Alphabet_type.new_alphabet varset

  (* Parsing of ground non-special terms *)

  let parse_ground alphabet =
    parse_special alphabet Alphabet_type.new_alphabet Variable_set_type.empty


  let rec parse_ground_term_set alphabet = parser 
      [< t= parse_ground alphabet; rem= parse_ground_term_set alphabet >] -> t::rem
    | [< >] -> []

  (* Parsing of special ground terms *)

  let parse_ground_special alphabet alphabet_special =
    parse_special alphabet alphabet_special Variable_set_type.empty


  (* Verify the coherence of a substitution: a variable must not be mapped 
     to distinct terms *)

  let rec coherent list = match list with
      [] -> []
    | (a_var,elt)::l -> try (if ((List.assoc a_var l) = elt)
			     then (coherent l)
			     else raise 
			       (Terms_do_not_match (("Non linear variable "^(Variable_type.to_string a_var)^" mapped to distinct terms",""))))
      with Not_found -> (a_var,elt)::(coherent l)


  (* Applying matching of term1 on term2, such that term2 is ground 
     or at least with disjoint set of variables. *)

    	  
  let rec matching term1 term2 = 
    let rec matching_aux term1 term2 = match (term1,term2) with
    	(Const(a), Const(b)) -> 
	  if Symbol_type.equal a b 
	  then [] 
	  else raise (Terms_do_not_match ((to_string term1),(to_string term2)))
	    
      | (Fsym(f, l1),Fsym(g, l2)) -> 
	  if Symbol_type.equal f g 
	  then matching_list l1 l2
	  else raise (Terms_do_not_match ((to_string term1),(to_string term2)))

      (* Once more, we assume that special terms do not contain variables *)
	    
      |	(Special(t1), Special(t2)) ->
	  if t1 = t2 
	  then []
	  else raise (Terms_do_not_match ((to_string t1),(to_string t2)))

      | (Var(x), t1) -> [(x, t1)]
      | x       -> raise (Terms_do_not_match ((to_string term1),(to_string term2)))
	  
    and matching_list l1 l2 = match (l1, l2) with
    	([], []) -> []
      | (t1::reste1, t2::reste2) -> (matching_aux t1 t2)
	  @(matching_list reste1 reste2)
      | x -> raise (Terms_do_not_match ("Not the same number of arguments!", ""))
								 
    in let subst = matching_aux term1 term2 in
      (coherent subst)	



  (* Applying matching of term1 on term2, such that term2 is ground 
     or at least with disjoint set of variables. *)

    	  
  let rec matching term1 term2 = 
    let rec matching_aux term1 term2 = match (term1,term2) with
    	(Const(a), Const(b)) -> 
	  if Symbol_type.equal a b 
	  then [] 
	  else raise (Terms_do_not_match ((to_string term1),(to_string term2)))
	    
      | (Fsym(f, l1),Fsym(g, l2)) -> 
	  if Symbol_type.equal f g 
	  then matching_list l1 l2
	  else raise (Terms_do_not_match ((to_string term1),(to_string term2)))

      (* Once more, we assume that special terms do not contain variables *)
	    
      |	(Special(t1), Special(t2)) ->
	  if t1 = t2 
	  then []
	  else raise (Terms_do_not_match ((to_string t1),(to_string t2)))

      | (Var(x), t1) -> [(x, t1)]
      | x       -> raise (Terms_do_not_match ((to_string term1),(to_string term2)))
	  
    and matching_list l1 l2 = match (l1, l2) with
    	([], []) -> []
      | (t1::reste1, t2::reste2) -> (matching_aux t1 t2)
	  @(matching_list reste1 reste2)
      | x -> raise (Terms_do_not_match ("Not the same number of arguments!", ""))
								 
    in let subst = matching_aux term1 term2 in
      (coherent subst)	



  (* Unification of term1 on term2. No unification on Special terms. Variables of term1 and term2 
     are to be disjoint *)


  let rec unify term1 term2 = 
    match (term1,term2) with
    	(Const(a), Const(b)) -> 
	  if Symbol_type.equal a b 
	  then [] 
	  else raise (Terms_do_not_unify ((to_string term1),(to_string term2)))
	    
      | (Fsym(f, l1),Fsym(g, l2)) -> 
	  if Symbol_type.equal f g 
	  then 
	    if l1=[] then failwith ("Empty list of args under an Fsym symbol in term: " ^ 
				    (to_string term1))
	    else 
	      let partial_subst= unify (List.hd l1) (List.hd l2) in
		partial_subst@(unify_list 
				 (apply_substs_on_terms [partial_subst] (List.tl l1))
				 (apply_substs_on_terms [partial_subst] (List.tl l2)))

	  else raise (Terms_do_not_unify ((to_string term1),(to_string term2)))

      (* We only unify Special if they are equal: no var in them *)
	    
      |	(Special(t1), Special(t2)) -> 
	  if equal t1 t2
	  then []
	  else raise (Terms_do_not_unify ((to_string term1),(to_string term2)))
	  

      | (Var(x), t1) -> [(x, t1)]
      | (t1, Var(x)) -> [(x, t1)]
      | x       -> raise (Terms_do_not_unify ((to_string term1),(to_string term2)))
	  
    and unify_list l1 l2 = match (l1, l2) with
    	([], []) -> []
      | (t1::reste1, t2::reste2) -> 
	  let partial_subst= unify t1 t2 in
	    partial_subst@(unify_list 
			     (apply_substs_on_terms [partial_subst] reste1)
			     (apply_substs_on_terms [partial_subst] reste2))

      | x -> raise (Terms_do_not_unify ("Not the same number of arguments!", ""))



  (* Applying matching of term1 on term2, such that term2 is ground 
     or at least with disjoint set of variables. Special terms may contain variables *)

  let rec matching_special term1 term2 = 
    let rec matching_aux term1 term2 = match (term1,term2) with
    	(Const(a), Const(b)) -> 
	  if Symbol_type.equal a b 
	  then [] 
	  else raise (Terms_do_not_match ((to_string term1),(to_string term2)))
	    
      | (Fsym(f, l1),Fsym(g, l2)) -> 
	  if Symbol_type.equal f g 
	  then matching_list l1 l2
	  else raise (Terms_do_not_match ((to_string term1),(to_string term2)))

      (* Special terms may contain variables *)
	    
      |	(Special(t1), Special(t2)) -> matching_aux t1 t2

      | (Var(x), t1) -> [(x, t1)]
      | x       -> raise (Terms_do_not_match ((to_string term1),(to_string term2)))
	  
    and matching_list l1 l2 = match (l1, l2) with
    	([], []) -> []
      | (t1::reste1, t2::reste2) -> (matching_aux t1 t2)
	  @(matching_list reste1 reste2)
      | x -> raise (Terms_do_not_match ("Not the same number of arguments!", ""))
								 
    in let subst = matching_aux term1 term2 in
      (coherent subst)	
end



