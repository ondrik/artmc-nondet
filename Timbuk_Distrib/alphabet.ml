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

module Alphabet =
  functor (Symbol_type:PRINTABLE_TYPE) ->
  struct
    type symbol = Symbol_type.t	  
    type t = (symbol * int) list
    exception Symbol_not_in_alphabet of string
    exception Multiply_defined_symbol of string

    let new_alphabet = []
    let occur symbol alphabet = List.mem_assoc symbol alphabet

    let add_symbol symbol arity alphabet = 
      if occur symbol alphabet then alphabet
      else (symbol, arity)::alphabet

    let get_arity symbol alphabet = 
      try (List.assoc symbol alphabet)
      with Not_found -> 
	raise (Symbol_not_in_alphabet (Symbol_type.to_string symbol))

    let to_list alphabet = alphabet

    let to_string_list alphabet= List.map (function x -> Symbol_type.to_string (fst x)) alphabet

(* Test if two alphabet are disjoint *)

    let rec disjoint a1 a2 = match a1 with
      [] -> true
    | (symb,arity)::rem -> 
	if occur symb a2 then false
	else disjoint rem a2

(* union for disjoint alphabets *)

    let union_fast = List.append

(* union for possibly non disjoint alphabets *)

    let rec  union a1 a2 = match a1 with 
	[] -> a2
      |(symb, arity)::rem -> 
	 if occur symb a2 
	 then union rem a2
	 else (symb, arity)::(union rem a2)


(* Parsing and pretty printing of alphabets *)

    let rec to_string alphabet = match alphabet with
      [] -> ""
    | (sym, arity)::alpha -> 
	(Symbol_type.to_string sym)^":"^(string_of_int arity)^" "^
	(to_string alpha)

    let rec parse = parser
	[< 'Genlex.Ident f ; 'Genlex.Kwd ":"; 'Genlex.Int i ;
	  new_alpha = parse >] ->
	    let symbol = Symbol_type.of_string f in
	    if occur symbol new_alpha 
	    then raise (Multiply_defined_symbol f)
	    else add_symbol symbol i new_alpha
      |	[< >] -> new_alphabet
  end

