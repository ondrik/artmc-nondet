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

(*-----------------------------------------------*)
(*                MODULE COTES                   *)
(*                                               *)
(*        This module calculate areas used       *)
(*             by elements of a tree             *)
(*                                               *)
(*        2 functions : cotes et update          *)
(*-----------------------------------------------*)

(* common structures *)

open Specifs;;
open Tk;;

(*-----------------------------------------------*)
(*        Array of fonts: local Variable         *)
(*          used by autozoom functions           *)
(*-----------------------------------------------*)

let numFonts = ref 3;;

let nbFonts = 4;;

let lesFonts = Array.make 4 "";;

Array.set lesFonts 0 "Arial 9" ;;
Array.set lesFonts 1 "Arial 18";;
Array.set lesFonts 2 "Arial 36";;
Array.set lesFonts 3 "Arial 72";;



(*------------------------------------------------*)
(*          functions to know the size            *)
(*             in pixels of strings               *)
(*------------------------------------------------*)

let lfont_tab= ref [];;


let rec fill_table (t: (string, int) Hashtbl.t) (lsymb: string list) (f: font): unit=
  match lsymb with 
    [] -> ()
  | e::rem -> Hashtbl.add t e (Font.measure f e); fill_table t rem f;;


(* Initially the font measure table should contain at least the Start symbol *)

let table_init ()=  
  let lsymb= ["Start"] in  
  let size= List.length lsymb in
  begin
    lfont_tab:=[];
    for i=0 to nbFonts-1 do 
      let tab= Hashtbl.create size in
	begin
	  fill_table tab lsymb (Array.get lesFonts i);
	  lfont_tab:= ((Array.get lesFonts i), tab)::!lfont_tab;
	end
    done
  end;;



(* Creation of the hash table list of symbol size: for each symbol of the 
   automaton, for each font we compute the size in pixel and store it in 
   a related database *)

let update_font_db ()=
(* additional symbols for terms*)
  let add_symb= ["Start";"(";")";",";"_";""] in  

  let lsymb= List.append add_symb (Gest.get_symbs ()) in
  let size= List.length lsymb in
  begin
    lfont_tab:=[];
    for i=0 to nbFonts-1 do 
      let tab= Hashtbl.create size in
      begin
	fill_table tab lsymb (Array.get lesFonts i);
	lfont_tab:= ((Array.get lesFonts i), tab)::!lfont_tab;
      end
    done;
    Return_Update_Font_DB
  end;;


(* function that returns the width in pixels of a string depending on its font *) 

let largPixelsString (s: string) (f: font) : (int) =
  try (let tab= (List.assoc f !lfont_tab) in
	 try (Hashtbl.find tab s)
	 with Not_found -> failwith ("Symbol "^s^" not found in table"))
  with Not_found -> failwith ("Font "^f^" not found in font_tab")


(* let largPixelsString (s: string) (f: font) : (int) =
 Font.measure f s ;; *)



(* function that returns the height in pixels of a string depending on its font *)
(*  it doesn't take care of the string for now *) 
let hautPixelsString (s: string) (f: font) : (int) =
  let hautCar =
    match f with
    | "Arial 9"  -> 16
    | "Arial 18" -> 24
    | "Arial 36" -> 52
    | "Arial 72" -> 100
    | _ -> failwith "largPixelsString: unknown font"
  in
  hautCar;;


(*-----------------------------------------------*)
(*               PARSERS FUNCTIONS               *)
(*                                               *)
(* parcFils  : function that go trough           *)
(*             sons list for a non linear        *)
(*             term (in tree mode)               *)
(*                                               *)
(* parcFils2 : function that go through a term   *)
(*                                               *)
(* parcours  : function that go through a term   *)
(*                                               *)
(*-----------------------------------------------*)


let rec parcFils (l: term list) (x:int) (y:int) (font : font) : (term list * int * int) =   
  match l with 
  | []    ->
      ([], x + largPixelsString (")") (font) , y)
  | l::[] ->
      let (tnew, xnew, ynew) = parcours (l) (x) (y) (font) in
      let xfinal = xnew + largPixelsString (")") (font) in         (* largeur du sous arbre l et ')' *)
      let yfinal = ynew in                                       
      (tnew::[], xfinal, yfinal)
  | l::s  ->
      let (tnew, xnew, ynew) = parcours (l) (x) (y) (font) in      (* largeur du sous arbre l et ',' *)
      let (liste, xfinal, yfinal) = parcFils (s) (xnew + largPixelsString (",") (font) ) (y) (font) in
      (tnew::liste, xfinal, max yfinal ynew)

and
    
    parcFils2 (l: term list) (x:int) (y:int) (font : font): (term list * int * int) =  
  match l with 
  | []    ->
      ([], x, y)
  | l::[] ->
      let (tnew, xnew, ynew) = parcours (l) (x) (y) (font) in
      let xfinal = xnew in                                      
      let yfinal = ynew in                                                          
      (tnew::[], xfinal, yfinal)
  | l::s  ->
      let (tnew, xnew, ynew) = parcours (l) (x) (y) (font)  in  
      let (liste, xfinal, yfinal) = parcFils2 (s) (xnew + largPixelsString ("_") (font)) (y) (font)in              (* décalage *)
      (tnew::liste, xfinal, (max yfinal ynew))

and

    parcours (t:term) (x:int) (y:int) (font :font) : (term * int * int) =
  match t with
  | State elem ->
      let xnew = x + largPixelsString (elem.symbol)(font) in               (* largeur de elem.symbol *)
      let ynew = y + hautPixelsString (elem.symbol) (font) in              (* pas de décalage*)
      (State {symbol = elem.symbol;
	      fromstate = elem.fromstate;
	      zone = (x, y, xnew, ynew);
	      ident = elem.ident;
	      linear = elem.linear},
       xnew,
       ynew
      )
	
  | Node (elem, l) ->
      if elem.linear 
      then
	let xnew = x + largPixelsString (elem.symbol) (font) + largPixelsString ("(")(font)  in       (* largeur de elem.symbol et '(' *)
	let ynew = y +  hautPixelsString (elem.symbol) (font) in                                                     (* pas de décalage*)
	let (newL, xnewFils, ynewFils) = parcFils l xnew y font in       (* lance les calculs pour la liste des fils *)
	let xmax = if (l != []) then (max xnewFils xnew) else (x + largPixelsString (elem.symbol) (font)) in
	let ymax = (max ynew ynewFils) in
	Node ({symbol = elem.symbol;
	       fromstate = elem.fromstate;
	       zone = (x, y, xmax, ymax);
	       ident = elem.ident;
	       linear = elem.linear}, newL),
	xmax,
	ymax
      else
	let xnew = x in                                                     (* pas de largeur de elem.symbol et '(' *)
	let ynew = y +  2 * hautPixelsString (elem.symbol) (font)  in           (* saut de ligne *)
	let (newL, xnewFils, ynewFils) = parcFils2 l xnew ynew font in      (* lance les calculs pour la liste des fils *)
	  begin
	    let pere = (xnew + largPixelsString  (elem.symbol) (font)) in
	    if (xnewFils < pere)
	    then
	      let (newL, xnewFils, ynewFils) = parcFils2 l (xnew+ ((pere - xnewFils)/2))  ynew font in  
	      let xmax = max (xnewFils) (xnew + largPixelsString  (elem.symbol) (font)) in
	      let ymax = (max ynew ynewFils) in
	      Node ({symbol = elem.symbol;
		     fromstate = elem.fromstate;
		     zone = (x, y, xmax,ymax);
		     ident = elem.ident;
		     linear = elem.linear}, newL),
	      xmax,
	      ynewFils
		
	    else

	      let xmax = max (xnewFils) (xnew + largPixelsString  (elem.symbol) (font)) in
	      let ymax = (max ynew ynewFils) in
	      Node ({symbol = elem.symbol;
		     fromstate = elem.fromstate;
		     zone = (x, y, xmax,ymax);
		     ident = elem.ident;
		     linear = elem.linear}, newL),
	      xmax,
	      ynewFils
	  end
;;


(*-----------------------------------------------*)
(*       Functions to proceed the autozoom       *)
(*                                               *)
(*            cote1 : to lower the font          *)
(*            cote2 : to higher the font         *)
(*                                               *)
(*-----------------------------------------------*)
	  
let rec cote1 (t:term) (f:font) (autoz:bool) width height : (term * font) =
  begin
    let (term , b, c) = parcours t 0 0 (Array.get lesFonts !numFonts) in
    if autoz
    then
      match term with
	| State elmt
	| Node (elmt,_) ->
	    let (x1,y1,x2,y2) = elmt.zone in 
	      begin
		if (((x2 > width) or (y2 > height)) & ((!numFonts) > 0))
		then
		  begin
		    numFonts:= !numFonts - 1;
		    cote1 t (Array.get lesFonts !numFonts) autoz width height
		  end
		else
		  (term , f)
	      end     
    else 
      (term , (Array.get lesFonts !numFonts))
  end
;;

let rec cote2 (t:term) (f:font) (autoz:bool) width height : (term * font) =
  begin    
    let (term , b, c) = parcours t 0 0 (Array.get lesFonts !numFonts) in
    if autoz
    then
      match term with
	| State elmt 
	|  Node (elmt,_) ->
	     let (x1,y1,x2,y2) = elmt.zone in 
	       begin
		 if ((x2 < width) && (y2 < height))
		 then
		   begin
		     if ((!numFonts) < nbFonts-1)
		     then
		       begin
			 numFonts:= !numFonts + 1;
			 cote2 t (Array.get lesFonts !numFonts) autoz width height
		       end
		     else
		       let (term, _,_) = parcours t 0 0 (Array.get lesFonts (!numFonts)) in
			 (term , (Array.get lesFonts (!numFonts)))
		   end
		 else
		   let (term, _,_) = parcours t 0 0 (Array.get lesFonts (!numFonts-1)) in
		     (term , (Array.get lesFonts (!numFonts-1)))
	       end
    else 
      (term , (Array.get lesFonts !numFonts))
  end
;;



(*-----------------------------------------------*)
(*           FUNCTION achievedAutozoom           *)
(*                                               *)
(*                  t : term                     *)
(*              width : int                      *)
(*             height : int                      *)
(*                                               *)
(*         Was the cote function able to         *)
(*            achieve the autozoom ?             *)
(*-----------------------------------------------*)

let achievedAutozoom (t:term) (width: int) (height: int) : bool =
   match t with 
     | State elmt
     | Node(elmt, _) ->
	 let (x1,y1,x2,y2) = elmt.zone in
	   (x2 < width) && (y2 < height)


(*-----------------------------------------------*)
(*                 FUNCTION COTE                 *)
(*                                               *)
(*               t : term (tree)                 *)
(*               f : string (font)               *)
(*           autoz : bool (Autozoom ?)           *)
(*  width , height : int * int                   *)
(*                   (size of the window)        *)
(*                                               *)
(*-----------------------------------------------*)

let cote (t:term) (f:font) (autoz:bool) width height : return_code =
  (* Check that the font f is in the font table (autorized) *)
  numFonts:=3;
  while ((!numFonts > 0) & (f <> (Array.get lesFonts !numFonts))) do
    numFonts := !numFonts - 1;
  done; 
  let (term , b, c) = parcours t 0 0 (Array.get lesFonts !numFonts) in
  if autoz then
    match term with
    | State elmt
    | Node (elmt,_)->
	let (x1,y1,x2,y2) = elmt.zone in 
	begin
	  if ((x2 > width) or (y2 > height)) then
	    (* the window is too small ? *)
	    let (term,f) = cote1 term (Array.get lesFonts !numFonts) autoz width height in
	    if achievedAutozoom (term)(width) (height) then
	      Return_Cote(term,f)
	    else
	      Return_No_Autozoom(term,f)
	  else if ((x2 <= width) && (y2 <= height)) then
	    (* the window is too big ? *)
	    let (term,f) = cote2 term (Array.get lesFonts !numFonts) autoz width height in
	    if achievedAutozoom (term)(width) (height) then
	      Return_Cote(term,f)
	    else
	      Return_No_Autozoom(term,f)
	  else failwith "Cas d'autozoom non prévu\n"
	end
  else
    Return_Cote(term,(Array.get lesFonts !numFonts));;




(*-----------------------------------------------*)
(*               FUNCTION UPDATE                 *)
(*                                               *)
(*               t : term (tree)                 *)
(*               f : string (font)               *)
(*           autoz : bool (Autozoom ?)           *)
(*  width , height : int * int                   *)
(*                   (size of the window)        *)
(*                                               *)
(*-----------------------------------------------*)

let update (t:term) (f:font) (autoz:bool) width height : return_code =
  match cote t f autoz width height with
  | Return_Cote(t, newf) -> Return_Update(t, newf)
  | Return_No_Autozoom(t, newf) -> Return_No_Autozoom(t, newf)
  | Error (Error_cotes,s) -> Error (Error_update,s)
  | _ -> failwith("Not an autorized return code");
;;






(*-----------------------------------------------*)
(*             FUNCTION SEND_ORDER               *)
(*                                               *)
(*   param : parameter of the function           *)
(*                                               *)
(*   this is the function that is called         *)
(*            by an other module                 *)
(*                                               *)
(*-----------------------------------------------*)


let send_order (param : order) : return_code = 
  match param with
  | Cote   (t, f, b, w, h) -> cote   t f b w h
  | Update (t, f, b, w, h) -> update t f b w h 
  | Update_Font_DB -> update_font_db ()
  | _ -> failwith "Unknown code" 
;;






(*-----------------------------------------------*)
(*             Tree print functions              *)
(*            used by others modules             *)
(*-----------------------------------------------*)

(* function that prints the zone of an element *)
let print_zone z = match z with (a,b,c,d) ->
  begin 
    print_string "[" ;
    print_int a ;
    print_string "," ;
    print_int b ;
    print_string "," ;
    print_int c ;
    print_string "," ;
    print_int d ;
    print_string "]"
  end ;;

(* function that prints an element (but only the symbol and the zone) *)
let print_elmt elmt = 
  begin
    print_string (elmt.symbol);
    print_string " ";
    print_zone elmt.zone
  end ;;

(* tree1 & tree2 :
   functions that print elements of a tree *)

let rec print_tree1 tree = match tree with
| State elmt -> print_elmt elmt
| Node (elmt,tree_list) ->
    print_elmt elmt;
    print_string("\n");
    let rec print_intern tree_list = match tree_list with
    | [] -> print_string("")
    | h::t ->
	print_tree1 h;
	print_string("\n");
	print_intern t
    in print_intern tree_list;;

let rec print_tree2 tree = match tree with
| State elmt -> print_string (elmt.symbol)
| Node (elmt,tree_list) ->
    print_string (elmt.symbol);
    print_string "(";
    let rec print_intern tree_list = match tree_list with
    | []    -> print_string ")"  
    | h::t  ->
	print_tree2 h;
	if (t=[])
	then print_string ")"
	else 
	  begin 
	    print_string ",";
	    print_intern t
	  end
    in print_intern tree_list;;

