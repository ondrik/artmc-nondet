(* Taml - Tree Automata for Ocaml
   Copyright (C) 2004 Thomas Genet

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

(* Taml - Tree Automata for Ocaml
   Copyright (C) 2004 Thomas Genet

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

(* This is the front-end interface to use tree automata in taml (caml
   toplevel with tree automata functions.
*)

open Symbol
open Alphabet
open Variable
open Variable_set
open Term
open State_set
open State_content
open Rewrite
open Automaton
open Gamma
open Specification
open Completion

(*IFDEF TABI THEN open Visu END*)
(* ifdef TABI then open Specifs *)

(* module instanciation *)

module Symbol= Symbol
module Variable= Variable
module Alphabet= Alphabet(Symbol)
module Variable_set= Variable_set(Variable)
module Term=Term(Symbol)(Alphabet)(Variable)(Variable_set)
module Rewrite= RewriteSystem(Alphabet)(Variable_set)(Term)
module State_set= State_set(Symbol)(Alphabet)(Term)(State_content)
module Automaton= TreeAutomata(Symbol)(Alphabet)(Variable)(Term)(State_content)(Rewrite)(State_set)
module Gamma= Gamma(Symbol)(Alphabet)(Variable)(Variable_set)(Term)(Rewrite)(State_set)(Automaton)
module Specification= Specification(Alphabet)(Variable_set)(Term)(Rewrite)(Automaton)(Gamma)
module Completion = Completion(Variable)(Symbol)(Alphabet)(Variable_set)(Term)(Rewrite)(State_set)(Automaton)
		  (Specification)(Gamma)

(* configuration of the garbage collector for lowest memory usage *)

let new_gc_control= {Gc.minor_heap_size=32768; Gc.major_heap_increment=63488;
 Gc.space_overhead=42; Gc.verbose=0; Gc.max_overhead=10;
 Gc.stack_limit=262144; Gc.allocation_policy=0};;
Gc.set new_gc_control;;


(*
let variable_printer ff s= Format.fprintf ff "%s@." (Variable.to_string s)
let symbol_printer ff s= Format.fprintf ff "%s@." (Symbol.to_string s)
let alphabet_printer ff a= Format.fprintf ff "%s@." (Alphabet.to_string a)
let variable_set_printer ff s= Format.fprintf ff "%s@." (Variable_set.to_string s)
let state_set_printer ff s= Format.fprintf ff "%s@." (State_set.to_string s)
let term_printer ff t= Format.fprintf ff "%s@." (Term.to_string t)
let trs_printer ff trs= Format.fprintf ff "%s@." (Rewrite.to_string trs)
let automaton_printer ff a= Format.fprintf ff "%s@." (Automaton.to_string a)
let approximation_printer ff a= Format.fprintf ff "%s@." (Gamma.to_string a)
let specification_printer ff s= Format.fprintf ff "%s@." (Specification.to_string s)
*)

(*
IFDEF TABI THEN
  let browse (a: Automaton.t)=  let _= Visu.tabi_call (Completion.convert_automaton a) in ()
ELSE*)
  let browse (a: Automaton.t)= print_string "Tabi not installed...\n" 
(*END*)




let alphabet s= Alphabet.parse (Specification.lexer (Stream.of_string s))
let varset s= Variable_set.parse (Specification.lexer (Stream.of_string s))
let term a v s= Term.check a (Term.parse a v (Specification.lexer (Stream.of_string s)))
let state s = Automaton.make_state (Symbol.of_string s)
let tree_state a sops s = Term.parse_ground_special a sops (Specification.lexer (Stream.of_string s))
let trs a v s= Rewrite.check (Rewrite.parse a v (Specification.lexer (Stream.of_string s))) a

let automaton a s= Automaton.parse a (Specification.lexer (Stream.of_string s))
let finite_set a s= fst (Automaton.term_set_to_automaton a (Term.parse_ground_term_set a (Specification.lexer (Stream.of_string s))) "qnew" 0)
let inter= Automaton.inter
let union= Automaton.union
let inverse= Automaton.inverse
let subtract= Automaton.subtract
let is_included= Automaton.is_included
let is_language_empty= Automaton.is_language_empty
let is_finite= Automaton.finite_recognized_language
let run= Automaton.run  
let determinise= Automaton.determinise
let irr= Automaton.nf_opt
let clean= Automaton.clean
let simplify= Automaton.simplify
let save= Specification.save_automaton

let read_alphabet s= Specification.get_alphabet (Specification.file_parse s)
let read_spec s= Specification.file_parse s

let read_automaton name filename= Specification.get_automaton name (Specification.file_parse filename)
let read_automaton_list filename= List.map Pervasives.snd (Specification.get_list_automata (Specification.file_parse filename))
let read_trs name filename= Specification.get_trs name (Specification.file_parse filename)
let read_trs_list filename= List.map Pervasives.snd (Specification.get_list_trs (Specification.file_parse filename))


let help ()= print_string 
"\nTaml functions:            

- alphabet: (s: string) -> Alphabet.t ---- Builds an alphabet from a string

- varset: (s: string) -> Variable_set.t ---- Builds a variable set from a string

- term: (a: Alphabet.t) (v: Variable_set.t) (s: string) -> Term.t ---- Builds a 
  term on alphabet a and variable set v from a string s

- state: (s: string) -> State.t ---- Builds a state from string s

- tree_state: (a: Alphabet.t) (sop: Alphabet.t) (s: string) -> State.t ---- 
  Builds a state on alphabet a, state operators sop and from a string s

- trs: (a: Alphabet.t) (v: Variable_set.t) (s: string) -> Rewrite.t ---- Builds a 
  TRS on alphabet a and variable set v from a string s

- automaton: (a: Alphabet.t) (s: string) -> Automaton.t ---- Builds an automaton
  on alphabet from a string s

- finite_set: (a: Alphabet.t) (s: string) -> Automaton.t ---- Builds an automaton
  on alphabet from a string representing the finite set of terms to be recognized 
  by the automaton.
 
- browse: (a: Automaton.t) -> unit ---- Browse in automaton a (if Tabi is 
  installed)

- inter: (a1: Automaton.t) -> (a2: Automaton.t) -> Automaton.t ---- Builds the 
  intersection automaton between a1 and a2. Sets of states are not explicitely 
  built. To obtain them explicitely use cleaning afterwards.

- union: (a1: Automaton.t) -> (a2: Automaton.t) -> Automaton.t ---- Builds the 
  union automaton for a1 and a2.

- inverse: Automaton.t -> Automaton.t ---- The complement operation.

- subtract: (a1: Automaton.t) -> (a2: Automaton.t) -> Automaton.t ---- Builds an 
  automaton recognizing L(a1) - L(a2).
 
- is_included: (a1: Automaton.t) -> (a2: Automaton.t) -> bool ---- Is L(a1) 
  included in L(a2)?

- is_language_empty: (a: Automaton.t) -> bool ---- Is L(a) empty?

- is_finite: (a: Automaton.t) -> bool ---- Is L(a) finite?

- run: (t: Term.t) -> (q: State.t) -> (a: Automaton.t) -> bool ---- Is t 
  recognized into state q in [a]?

- determinise: Automaton.t -> Automaton.t ---- Determinisation of tree automata

- irr: (a: Alphabet.t) -> (t: Rewrite.t) -> Automaton.t ---- Builds a tree 
  automaton recognising the set of terms irreducible by TRS t.

- clean: Automaton.t -> Automaton.t ---- Accessibility cleaning followed by 
  utility cleaning.

- simplify: Automaton.t -> Automaton.t ---- Accessibility cleaning followed by 
  utility cleaning and renumbering.

- save: (a: Automaton.t) -> (n: string) -> (f: string) -> unit ---- Save 
  automaton a with name n in file named f.

- read_alphabet: (s: string) -> Alphabet.t ---- Reads an alphabet in a timbuk 
  specification file

- read_spec: (s: string) -> Specification.t ---- Reads a full timbuk 
  specification in file of name s

- read_automaton: (n: string) -> (f: string) -> Automaton.t ---- Reads an 
  automaton of name n in a specification file f

- read_automaton_list: (f: string) -> Automaton.t list ---- Reads all the 
  automaton in specification file f

- read_trs: (n: string) -> (f: string) -> Rewrite.t ---- Reads a TSR of name n 
  in a specification file f

- read_trs_list: (f: string) -> Rewrite.t list ---- Reads all the TRS in 
  specification file f

- help: unit -> unit ---- Prints this help message

"

(*
let _= print_string "
 Taml:  Tree Automata for                   Type 'help();;' 
                                            for help on taml functions\n"
                                            *)
