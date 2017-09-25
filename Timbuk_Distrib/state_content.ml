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

(* States contents *) 
(* The state content we use here is simply a description (string)
   associated to a state, for an information purpose only: i.e. give the
   intuition hidden behind a particular state. *)



module State_content = 
  struct
    type t = string
    let to_string s = s
    let of_string str = str
    let equal = (=)
    let empty = ""

(* This is the intersection of two state contents *)
(* Description of two states description is their concatenation *)
(* not used ! *)

    let inter s1 s2 = ""
(*       if s1 ="" then s2 else if s2 ="" then s1 else s1^" and "^s2 *)

end;;


