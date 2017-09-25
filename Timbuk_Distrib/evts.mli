(* Tabi - A Tree Automata Browsing Interface
   Copyright (C) 2004 Thomas Genet and [Boinet Matthieu, Brouard Robert, 
        Cudennec Loic, Durieux David, Gandia Sebastien, Gillet David, 
        Halna Frederic, Le Gall Gilles, Le Nay Judicael, Le Roux Luka, 
        Mallah Mohamad-Tarek, Marchais Sebastien, Martin Morgane, 
        Minier François, Stute Mathieu] -- aavisu project team for
        french "maitrise" level (4th University year) 2002-2003 at
	IFSIC/Universite de Rennes 1. 


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

(* Tabi - A Tree Automata Browsing Interface
   Copyright (C) 2004 Thomas Genet and [Boinet Matthieu, Brouard Robert, 
        Cudennec Loic, Durieux David, Gandia Sebastien, Gillet David, 
        Halna Frederic, Le Gall Gilles, Le Nay Judicael, Le Roux Luka, 
        Mallah Mohamad-Tarek, Marchais Sebastien, Martin Morgane, 
        Minier François, Stute Mathieu] -- aavisu project team for
        french "maitrise" level (4th University year) 2002-2003 at
	IFSIC/Universite de Rennes 1. 


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

open Specifs;;

exception Erreur of string

val canvas_height: int ref
val canvas_width: int ref
val zoom_auto: bool ref 
val default_term: term ref
val init_term: term 
val get_coord_unfold: (term -> font -> return_code) -> 
  (ident -> term list -> int -> int -> return_code) -> int -> int-> unit
val get_coord_fold: (term -> font -> return_code) -> 
  (ident -> term list -> int -> int -> return_code) -> int -> int-> unit
val main: unit -> unit
val file_open: (term -> font -> return_code) -> string -> unit
val automaton_open: (term -> font -> return_code) -> automaton -> unit
val undo: (term->font->return_code) ->int->unit
val redo: (term->font->return_code) ->int->unit
val get_coord_in_box: (term->font->return_code) -> int -> unit
val history:((term*ident) list->return_code) -> unit
val random: (term list->return_code)->int->float->int -> unit
val change_mod_arbre: unit -> unit
val change_mod_lin: unit -> unit
val get_fromstate: int -> int-> (string* zone* term* font) 
val get_symbol: int -> int-> string
val change_mod_zoom: (term->font->return_code) -> bool -> unit
val change_to_one_level: (term -> font -> return_code) -> int -> int ->unit
val change_total_linearisation: (term -> font -> return_code) -> int -> int ->unit
val change_total_arborisation: (term -> font -> return_code) -> int -> int ->unit
val change_font: (term -> font -> return_code) -> font ->unit
val restart: (term -> font -> return_code) -> unit
