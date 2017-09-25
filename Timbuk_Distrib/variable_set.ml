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

(* variable sets *)

module Variable_set= 
  functor (Variable_type: PRINTABLE_TYPE) ->
struct
  type variable = Variable_type.t
  type t = variable list
  let empty = []
  let is_empty s = (s = [])
  let mem = List.mem	  
  let add var varset = 
    if mem var varset then varset else var::varset

  (* Pretty print *)

  let to_string varset = 
    List.fold_right 
      (function a -> function b -> (Variable_type.to_string a)^" "^b)
      varset ""

  let to_string_list varset= List.map Variable_type.to_string varset

  (* Parsing *)

  let rec parse = parser
      [< 'Genlex.Ident x ; remaining_set= parse >] ->
	add (Variable_type.of_string x) remaining_set
    | [< >] ->  empty
end

