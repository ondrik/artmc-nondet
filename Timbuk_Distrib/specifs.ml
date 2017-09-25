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

type font = string;; (* A MODIFIER PAR UN INCLUDE *)

(**************Types used for automatons manipulation*************)

(*
///////////////////////////////////////
//Bottom-up Tree Automaton and Termes//
///////////////////////////////////////

A = {Q;Qf;F;T}

with:
Q: set of states
Qf: set of final states (Qf is include in Q)
F: set of the used symbols
T: a set of transitions

ex:
A = 	{
		{q0,qf};
		{qf};	
		{+(,),-(),n};
		{	
			n -> q0,
			-(q0) -> q0,
			+(q0,q0) -> qf
		}
	}

An exemple of recognizable terme:

+(n,-(-(n)))
	n -> q0
+(q0,-(-(n)))
	n -> q0	
+(q0,-(-(q0)))
	-(q0) -> q0
+(q0,-(q0))
	-(q0) -> q0
+(q0,q0)
	+(q0,q0) -> qf
qf

We will have to define bottom-up tree automatons and termes in O'Caml. Some informations will be added or forgoten in order to be used for the project (graphic representation of bottom-up tree automaton termes). 

The set of final states won't be encoded.

A tree is composed with elements. An element is defined with a symbol (and only with a symbol for the trees used in transitions), the state it came from, an interval (used in the coordinates module) and an ident.

A postion ident is used. It means that the functions used to find or edit an element in a tree will directly depend on the one which has been chosen.

*)

type ident = int list;;

(*

The root has the [] ident (empty list).
With iAncestor (int list) the ident of the ancestor of the current element
and nElement (int) the succesor number of the current element (from 1, left to right),
the ident of the current element is iAncestor@[nElement]

Exemple:


tree:
root - A - C
         - D - H
         - E
     - B - F
         - G

symbol , ident:
root   , []
   A   , [1]
   B   , [2]
   C   , [1,1]
   D   , [1,2]
   E   , [1,3]
   F   , [2,1]
   G   , [2,2]
   H   , [1,2,1]

*)


(* --------------------zone------------------------ *)
(* Coordonates of the two corners delimiting a clickable zone...
   Upper left (x,y) Lower Right (x,y)
*)

type zone = int * int * int * int;;


(* --------------------element--------------------- *)
(* symbol : name of the element
   fromstate : original state
   zone : association of the zone with the element
   ident : unique ident of the element
   linear : this element is displayed in tree mode or linear mode (true -> linear mode)
*)

type element = {symbol: string; fromstate: string; zone: zone; ident: ident; linear : bool};;


type simple_element = string;;

type 'a tree = State of 'a
	| Node of 'a * 'a tree list;;

(* a tree can be an element tree or a simple_element tree *)

type term = element tree;;
type simple_term = simple_element tree;;

type transition = simple_element tree * simple_element tree;;

type automaton = {q: string list; f: string list; t: transition list};;
type res_det =  
    State_elt of element 
  | Node_elt of element * element tree list 
  | Vide ;;

(*******CAML types used for communication between different parts************)

type order =    (* ordres recus *)
               Undo of int                     (* int-> number of actions we undo *)
             | Redo of int                     (* int-> number of actions we redo *)
             | Fold of ident * term            (* substitution of the ident by its original state *)
             | Selection of ident * term       (* list of possible derivations for the ident *)
             | Unfold of ident * term * term * bool   
                                               (* substitution of the ident in the first term*)
		                               (* by the second term *)
                                               (* bool : true for linear *)
             | GetHistory                      (* explicit request of the history *)
	     | GetRandom of ident * term * int * float * int
      (* explicit request for random terms, the ident must be a state 
         int -> max depth of the random terms
         1st float -> max time of the calcul
         2nd float -> >0 & <=1 , rate of terms kept each step of the calcul 
       *)
             | Open of string                  (* opening of a file *)
             | OpenDirect of automaton                  (* opening of a file *)
             | Choices of ident * term list * int * int   (* sending of the result of the selection to the Visu part *)             
             | SendHistory of                 
                (term * ident) list            (* sending of the result of the history to Visu *)
	     | SendRandom of term list         (* sending of the result of the random to Visu *)
             | Refresh of term * font          (* refreshing of the display in the main window *)

                               (* Update     : order to use when the tree doesn't change
                                  Cote       : otherwise (zoom change or mode change)
                                  parameters : term -> the tree to process
		                               font -> the lablTk font (string)
		                               bool -> true for Auto Zoom (the size will be adapted
				                       to the width of the screen
		                               int -> width of the screen (pixel) 
	                                       int -> eight if the screen*)
             | Cote of term * font * bool * int * int
             | Update of term * font * bool * int * int

	                    (* change the mode from linear to tree or tree to linear
                               parameters : term -> the tree to process
                                            ident -> element to process
                                            bool -> if true then the switching is done only for the current element
                            *)
	     | Update_Font_DB
		           (* updates the font sizes database for the current tree *)
	     | SwitchToTree of term * ident * bool
                                               (* if true then the successors of the ident are switched as well *)
  
             | SwitchToLinear of term * ident * bool
                                               (* if true then the successors of the ident are switched as well *)
             | Send_error of string            (* sending of an error message to a part *)
             | Refresh_without_autozoom of term * font (* refreshing of the display without autozoom in the main window *);;

type code_error =
                     Error_Undo                      (* impossible : first step *)
                   | Error_Redo                      (* impossible : we can not redo it *) 
                   | Error_Selection                 (* impossible : we can not drivate the ident *)
                   | Error_Open_cant_find_the_file   (* impossible : we can not find the file *)
                   | Error_Open_cant_read_the_file   (* impossible : we can not read the file *)
                   | Error_Open_wrong_type_of_file   (* impossible : we can not open this type of file *)
                   | Error_Open_parse_error          (* use the string of the error code to go over the parser error *)
                   | Error_cotes                     (* error when there is a problem w/ LablTK *)
                   | Error_update;;                  (* the same *)

type return_code =
                     Return_Undo of term               (* the modified term *)
                   | Return_Redo of term               (* the modified term *)
                   | Return_Fold of term               (* the modified term *)
                   | Return_Selection of term list     (* the list of the possible choices *)
                   | Return_Unfold of term             (* the modified term *)
                   | Return_GetHistory of (term*ident) list    (* the list of the terms from the history *)
		   | Return_GetRandom of term list     (* a list of random terms *)
                   | Return_Open of term               (* term 'start' in a new window *)
                   | Return_SendHistory 
		   | Return_SendRandom
                   | Return_Choices                    (* return choices*)
                   | Return_Refresh                    (* ok return *)
                   | Return_SwitchMode of term         (* the modified term *)
		   | Return_Update_Font_DB             (* no problem *)
                   | Return_Cote of term * font        (* when the order Update or Cote succeeded *)
                   | Return_Update of term * font      (* it gives back the font to use and the
                                                          tree with the placements *)
                   | Return_No_Autozoom of term * font (* when the autozoom can't reach the size
                                                          required. In this case, the smallest font
                                                          is used *)
                   | Error of code_error * string      (* error code of the action *);;
