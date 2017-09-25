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

(* This is the interface for terms of $\TFX$ constructed on an alphabet $\F$ and a set of 
   variables $\X$ *)

module Term
  (Symbol_type: PRINTABLE_TYPE)
  (Alphabet_type: ALPHABET_TYPE with type symbol= Symbol_type.t)
  (Variable_type: PRINTABLE_TYPE)
  (Variable_set_type: VARIABLE_SET_TYPE with type variable= Variable_type.t):
sig
  
(*s A term is either a variable, a constant, a functionnal symbol with a
   list of subterms, or a special term.
   A special term is build on a union of the alphabet and a
   special alphabet.
   
   For example, let $\F=\{f:2, g:1, a:0\}$ an alphabet and $\F'=\{prod:2, q:0, 
   h:2\}$ a special alphabet.

   Then $f(g(a),g(prod(q,h(g(q),q))))$ is a term where $prod(q,h(g(q),q))$ is a
   special subterm. The [Special()] constructor is used in the
   implementation to separate the special subterms in a term.
*)

  type symbol= Symbol_type.t
  type variable= Variable_type.t
  type alphabet= Alphabet_type.t
  type variable_set= Variable_set_type.t
  type term = (Symbol_type.t, Variable_type.t) term_const	
  type t= term

  type substitution = (Variable_type.t * term) list
  exception Terms_do_not_match of string * string
  exception Terms_do_not_unify of string * string
  exception Badly_formed_term of string
  exception Parse_error of string
  exception Undefined_symbol of string 
  exception Bad_operation_on_special_term of string
  exception Bad_operation_on_var of string
    
  val equal : t -> t -> bool
	
  (*s Depth of a term, where depth of Special terms, variables and constant is 0 *)
  val depth : t -> int

  (*s Pretty printing of terms into strings *)
  val to_string : t -> string

  val top_symbol : t -> Symbol_type.t

  (*s the direct subterms of a term *)
  val list_arguments : t -> t list

  (*s is a term a variable? *)
  val is_variable : t -> bool

  (*s is a term a constant? *)
  val is_constant : t -> bool

  (*s is a term special: its top constructor is a Special constructor  *)
  val is_special : t -> bool

  (*s get the term t from Special(t) *)
  val get_special : t -> t

  (*s mapping function f1 on every symbol of term t1 and f2 on every constant, variable or special term *)
 
  val map : ((Symbol_type.t -> Symbol_type.t)) -> ((t -> t)) -> (t) -> t

  (*s get the list of the leaves of a term *)
  val list_leaves : t -> t list

  (*s get the list of variables of a term *)
  val list_variables : t -> Variable_type.t list

  (*s get the list of non linear variables of a term (with no redundancy) *)
  val list_non_linear_variables: t -> variable list

  (*s rename a variable: add a string to the end of the variable *)
  val var_change: variable -> string -> variable 

  (*s rename variables of a term: add a string to the end of every variable name *)
  val rename_var: term -> string -> term

  (*s linearize a term: produces a linear version of a term [t] associated with the variable 
     renamings that have been operated in order to make the term linear. *)
  val linearize: term -> (term * (variable * (variable list)) list)

  (*s is a term ground? i.e. with no variables. Note that a special term can be ground *)
  val is_ground : t -> bool

  (*s is a term linear? i.e. there is only one occurence of each variable in the term *)
  val is_linear : t -> bool

  (*s get the list of all terms [t] such that [Special(t)] is a subterm of [t1] *)
  val list_special : t -> t list

  (*s Check the consistency of a term with regards to an alphabet. i.e. checks that for every 
     subterm $f(s1, ..., sn)$ of [t1], $f$ has an arity $n$ in the alphabet [a]. This function
     returns the term itself if it is correct, raise a [Badly_formed_term] exception if arity of the 
    symbol does not correspond to its number of arguments, and raise a [Undefined_symbol] exception
    if the term contains a symbol that does not belong to the alphabet. *)

  val check : Alphabet_type.t -> t -> t

  (*s apply a substitution to a term (at every variable position in it) *)
  val apply : substitution  -> t -> t
	
  (*s returns the list of terms ([s t1]) (substitution [s] applied to [t1]) for every substitution [s] of l *)
  val apply_several : (substitution list) -> t -> t list

  (*s returns the list of terms ([s t1]) (substitution [s] applied to [t1]) for every substitution [s] of l and every term t1 of lt *)

  val apply_substs_on_terms : (substitution list) -> t list -> t list

  (*s Parsing of terms w.r.t. an alphabet [a] and a set of variable [varset] *)
  val parse :
      Alphabet_type.t ->
        Variable_set_type.t -> Genlex.token Stream.t -> t
	
  (*s Parsing of ground terms w.r.t. an alphabet [a] *)
  val parse_ground :
    Alphabet_type.t ->
        Genlex.token Stream.t -> t

  (*s Parsing of ground terms sets w.r.t. an alphabet [a] *)
  val parse_ground_term_set :
    Alphabet_type.t ->
        Genlex.token Stream.t -> t list 
	
  (*s Verify the coherence of a substitution: a variable must not be mapped 
     to distinct terms. Otherwise a [Term_do_not_match] exception is raised *)
  val coherent : substitution -> substitution
	
  (*s matching of [term1] on [term2], such that [term2] is ground 
     or at least with variables disjoint from those of [term1]. *)
  val matching : t -> t -> substitution
 
  (*s unification of [term1] on [term2]. No unification on Special terms. Variables of term1 and term2 
     are to be disjoint *)

  val unify: t -> t -> substitution


(*s similar functions for special terms *)

(* Check the consistency of a term with regards to an alphabet [a] and a
   special alphabet [spa] i.e. checks that for every subterm $f(s1, ..., sn)$ of [t1], $f$ 
   has an arity n in the alphabet if $f(s1, ..., sn)$ is a term or in [spa] if $f(s1, ..., sn)$ 
   is below a Special constructor.This function
     returns the term itself if it is correct, raise a [Badly_formed_term] exception if arity of the 
    symbol does not correspond to its number of arguments, and raise a [Undefined_symbol] exception
    if the term contains a symbol that does not belong to the alphabets.
   *)

  val check_special : Alphabet_type.t -> Alphabet_type.t -> t -> t


  (* replacement in special terms: for every pair [(t1, t2)] of [l], replace every [Special(t1)] by [Special(t2)]
     at every Special position in [t3] *)
  val replace_special : ((t * t) list) -> t -> t

  (* the map combinator on special terms *)
  val map_special: (Symbol_type.t -> Symbol_type.t) -> (t -> t) -> t -> t

  (* Generalisation of substitution to special terms with any depth thanks to 
     the combinator on terms: Term.map\_special *)

  val apply_special: substitution -> term -> term


  (* Parsing of a term with special subterms w.r.t. alphabet [a] and special alphabet [spa]. *)
  val parse_special :
    Alphabet_type.t ->
        Alphabet_type.t ->
          Variable_set_type.t -> Genlex.token Stream.t -> t

  (* Parsing of ground special terms w.r.t. alphabet [a] and special alphabet [spa].*)
  val parse_ground_special :
    Alphabet_type.t ->
        Alphabet_type.t ->
	  Genlex.token Stream.t -> t

 (* Applying matching on [term1] and [term2], such that term2 is ground 
     or at least with disjoint set of variables. Special terms may contain variables *)

  val matching_special: t -> t -> substitution 

end 
