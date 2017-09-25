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
(* This is the interface for alphabets which are sets of symbols associated with their
   arity i.e. their number of arguments *)

module Alphabet :
  functor (Symbol_type : PRINTABLE_TYPE) ->
sig
  type symbol = Symbol_type.t
  type t

  exception Symbol_not_in_alphabet of string
  exception Multiply_defined_symbol of string

  (*s One alphabet constructor *)
  val new_alphabet: t

  (*s Parsing of alphabets (another constructor) *)
  val parse : Genlex.token Stream.t -> t

  (*s Testing the occurrence of a symbol in an alphabet *)
  val occur : symbol -> t -> bool

  (*s Adding a symbol with its arity in an alphabet *)
  val add_symbol : symbol -> int -> t -> t

  (*s Getting the arity of a symbol in an alphabet. This function 
   raises the exception [Symbol_not_in_alphabet(s)] where [s] is the
  string associated with the symbol if it is not in the alphabet *)
  val get_arity : symbol -> t -> int
       
  val to_list : t -> (symbol * int) list
      
  val to_string_list: t -> string list

  (*s Testing disjointness of two alphabets *)
  val disjoint : t -> t -> bool

  (*s Construct the union of two disjoint alphabets *)
  val union_fast : t -> t -> t

  (*s Construct the union of two alphabets, possibly non-disjoint *)
  val union : t -> t -> t
      
  (*s Pretty print *)
  val to_string : t -> string

end
