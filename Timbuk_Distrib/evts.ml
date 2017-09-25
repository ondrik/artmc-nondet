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

(*********************************************************************************************
*                                                                                           *
*  Evts group : -> Martin Morgane                                                          *
*                -> Marchais Sébastien                                                      *
*                -> Stute Mathieu                                                           *
*                -> Le Gall Gilles                                                          *  
*                                                                                           *
*  Organization of events in the project aavisu
                                            
*                                                                                           *
*                                                                                           *
*                                                                                           *
**********************************************************************************************)
open Specifs;;
open Gest;;
open Visu;;
open Cotes;;

exception Erreur of string;;

(******************************************************************
*******************************************************************
**                              REFERENCES                       **
*******************************************************************
*******************************************************************)

let default_font = ref "Helvetica 18";;
let zoom_auto = ref true;;
let canvas_height = ref 5000;;
let canvas_width = ref 5000;;
let init_term= (State {symbol = ""; fromstate = ""; zone = (0,0,0,0); ident = []; linear = true});;
let default_term = ref init_term;;
let is_linear = ref true;;  
let list_term = ref [];;
let default_ident = ref [];;

let main () = ();;


(***********************************************************************
This function refreshes the term given in parameter
cote_refresh function:
input: -->function call_back_refresh calls Visu.send_order(Refresh)
       -->t:term = term to refresh
*************************************************************************)
let cote_refresh (call_back_refresh:term->font->return_code)(t:term):unit =

  let ret_cote=
  match Cotes.send_order(Cote (t,!default_font,!zoom_auto,!canvas_width,!canvas_height)) with
  | Return_Cote (r,f) -> r,f
  | Return_No_Autozoom(r,f) -> 
      zoom_auto:=false;
      r,f
  | Error(ce,s)-> raise (Erreur "There is a problem with Labltk in Cote module")
  | _ -> failwith "Return_order not allowed"
  in
  let (r,f) = ret_cote in
  default_font:=f;
  default_term:=r;
  let ret_visu = match call_back_refresh r f with 
  | Return_Refresh  -> () (* return Refresh is OK *)
  | _ -> raise (Erreur "There is a problem with Refresh in Visu module")
  in ()
;;
(**********************************************************************************
This function unables to open a file.
It ends by calling cote_refresh to refresh the new term. 
file_open function:
input:  --> call_back_refresh
        --> file_name:string =name of the file
output: --> unit
***********************************************************************************)
let automaton_open (call_back_refresh:term->font->return_code)(a:automaton) :unit =  
  let ret_gest = match Gest.send_order(OpenDirect a) with
    | Return_Open t -> 
	(match Cotes.send_order(Update_Font_DB)with
	   |Return_Update_Font_DB -> t
	   |_ -> raise(Erreur "Erreur avec Update_Font_DB")
	)
    | _ -> failwith "Return_order not allowed for Gest !"
  in
    cote_refresh call_back_refresh ret_gest;;
(**********************************************************************************
This function unables to open a file.
It ends by calling cote_refresh to refresh the new term. 
file_open function:
input:  --> call_back_refresh
        --> file_name:string =name of the file
output: --> unit
***********************************************************************************)
let file_open (call_back_refresh:term->font->return_code)(file_name:string) :unit =  
  let ret_gest = match Gest.send_order(Open file_name) with
  | Return_Open t -> 
      (match Cotes.send_order(Update_Font_DB)with
      |Return_Update_Font_DB -> t
      |_ -> raise(Erreur "Erreur avec Update_Font_DB")
      )
  | Error(ce,s) -> 
      (
       match ce with
       | Error_Open_cant_find_the_file -> 
	   raise (Erreur "impossible : we can't find the file")
       | Error_Open_cant_read_the_file -> 
	   raise (Erreur "impossible : we can't read the file")
       | Error_Open_wrong_type_of_file -> 
	   raise (Erreur "impossible : we can't open this type of file")
       | Error_Open_parse_error -> raise (Erreur s)

       | _ -> raise (Erreur "impossible : we can't open this type of file")
      )
    | _ -> failwith "Return_order not allowed for Gest !"
  in
  cote_refresh call_back_refresh ret_gest 
;;
(******************************************************************************************
unfold function:
input: --> call_back_refresh
           --> ident gives the term to replace
           --> term = global term
           --> term = replacing term
           --> bool= true for linear
output: unit
*****************************************************************************************)
let unfold (call_back_refresh:term->font->return_code)(i:ident)(t1:term)(t2:term)(b:bool):unit =
  let ret_gest=match Gest.send_order(Unfold(i,t1,t2,b)) with
  | Return_Unfold t -> t
  | _ -> raise (Erreur "Unfold error in Gest module")
  in 
  cote_refresh call_back_refresh ret_gest;
;;

(*fold*******************************************************************************************)
let fold (call_back_refresh:term->font->return_code)(i:ident)(t:term):unit =


  let ret_gest = match Gest.send_order(Fold(i,t)) with
  | Return_Fold t -> t
  | _ -> raise (Erreur "Fold error in Gest module")
  in

  cote_refresh call_back_refresh ret_gest;;
(*********************************************************************************
This function says if the position of the mouse is in the box specified.
is_in_box function:
**********************************************************************************)

let is_in_box (z:zone)(i1:int)(i2:int):bool = 
  
  let (x1,y1,x2,y2) = z in ((i1>=x1)&& (i1<=x2) && (i2>=y1) && (i2<=y2))
;;
(*determine_elt*********************************************************************************)
(*gives the element linked to the clicked zone*)
let rec determine_elt (t:term)(i1:int)(i2:int):(res_det) = 
  match t with
  | State e ->  
      if is_in_box e.zone i1 i2 
      then State_elt e 
      else Vide 
  | Node (elt,[]) ->  
      if (is_in_box elt.zone i1 i2)  
      then Node_elt (elt,[]) 
      else Vide  
  | Node (elt, (a::l:element tree list)) ->  
      match a with 
      | State e -> 
	  if (is_in_box e.zone i1 i2)
	  then State_elt e
	  else determine_elt (Node (elt,l)) i1 i2
      | Node(e,l1) ->  
	  if is_in_box e.zone i1 i2  
	  then determine_elt (Node (e,l1)) i1 i2 
	  else determine_elt (Node (elt,l)) i1 i2 
;;
(*function get_term_in_tl    *****************************************************) 
(*This function gives the term of number i which is in the list of terms tl.******)
(*********************************************************************************)
let rec get_term_in_tl (tl:term list)(i:int):term = 
  match tl with
  | [] ->raise (Erreur "impossible to find the term")
  | a::[] -> a(*raise (Erreur "no corresponding term")*)
  | a::l  -> 
      if i=0
      then a
      else let j = i-1 in
      get_term_in_tl l j
;;
(*******************************************************************************
get_coord_in_box**********)
let get_coord_in_box  (call_back_refresh:term->font->return_code)(i:int):unit =
  let te = get_term_in_tl !list_term i in
  unfold call_back_refresh !default_ident !default_term te !is_linear ;
;;
(****aff *********************************************************************)
(* this function print the tree **********************************************)
let rec aff (tl:term list):unit = 
match tl with
| [] -> ()
| a::l-> 
    begin 
      Cotes.print_tree1 a ;
	aff l
    end
;;
(*selection*******************************************************************************)
let selection (call_back_choice :ident->term list->int->int->return_code)
    (call_back_refresh:term->font->return_code)
    (id:ident)(t:term)(i1:int)(i2:int):unit=
  let ret_gest = match Gest.send_order(Selection(id,t)) with
  |Return_Selection tl -> tl
  |Error(ce,s) -> raise( Erreur "Impossible : we can't derivate the ident ")
  | _ ->  failwith "Return_order not allowed"
  in
  list_term:=ret_gest;
  default_ident:=id;
  let ret_visu=match call_back_choice id ret_gest i1 i2 with
  |Return_Choices  ->  () (*return choices ok*)
  |_ -> failwith "error of Choice in visu"
  in
    ()
;;
(*get_coor_unfold  **********************************************************************)
(*** this function determine the element which has been clicked and call selection*******)

let get_coord_unfold (call_back_refresh:term->font->return_code)
    (call_back_choices:ident->term list->int->int->return_code)(x:int)(y:int):unit  =

  let elt = determine_elt !default_term x y in
  match elt with 
  | State_elt e -> selection call_back_choices call_back_refresh e.ident !default_term x y
  | Node_elt(e,l) -> ()
  | Vide -> ()
;;
(*get_coord_fold***********************************************************************************)
let get_coord_fold (call_back_refresh:term->font->return_code)
    (call_back_choices:ident->term list->int->int->return_code)(x:int)(y:int):unit  =

  let elt = determine_elt !default_term x y in
  match elt with 
  | State_elt e -> ()
  | Node_elt(e,l) -> fold call_back_refresh e.ident !default_term 
  | Vide -> ()

;;
(*Undo**********************************************************************************)
let undo (call_back:term->font->return_code)(i:int):unit  =

let ret_gest = match Gest.send_order(Undo i) with
|Return_Undo t -> t
|Error(ce,s) ->raise (Erreur "Undo for i times impossible")
|_ ->failwith "Return_order not allowed"
in cote_refresh call_back ret_gest;;

(*redo**********************************************************************************)

let redo (call_back :term->font->return_code)(i:int):unit  =
  let ret_gest = match Gest.send_order(Redo i) with
  |Return_Redo t -> t
  |Error(ce,s) ->raise (Erreur "Impossible : we can't redo it")
  |_ ->failwith "Return_order not allowed"
  in cote_refresh call_back ret_gest
;;
(*history*******************************************************************)
 let history (call_back_history:(term*ident) list->return_code):unit=   
   let ret_hist = match Gest.send_order(GetHistory) with
   | Return_GetHistory (til:(term*ident) list) -> til
   | _ -> raise (Erreur "error in the history request")
   in 
   let ret_visu= match call_back_history ret_hist with 
   |Return_SendHistory -> ()
   |_ -> raise (Erreur "error in return_SendHistory")
   in
   ()
;;


(*random*********************************************************************)
 let random (call_back_random:term list->return_code)(i:int)(j:float)(k:int):         unit=   
   let ret_rand = match Gest.send_order(GetRandom( !default_ident, !default_term, i, j, k))with
   | Return_GetRandom (tl:term list) -> tl
   | _ -> raise (Erreur "error in the random request")
   in
   (
    list_term:=ret_rand;
    let ret_visu= match call_back_random ret_rand with 
    |Return_SendRandom -> ()
    |_ -> raise (Erreur "error in return_SendRandom")
    in
    ()
   )
;;
(*map2**********************************************************************************)
let rec map2 (elt:res_det)f (l:'a list):'a list = 
  match l with
  | [] -> []
  | h::t -> (f h elt)::(map2 elt f t)
;;

(*****************************************************************************************)
(* map function                                                                          *)
(*The map function unables to apply one function to every elements of a list.            *)       
(*****************************************************************************************)
let rec map (f:'a -> 'a) (l:'a list):'a list = match l with
| [] -> []
| h::t -> (f h)::(map f t)
;;
(*****************************************************************************************)
(*                                                                                       *)
(*change_true function : t:the term to change                                            *)
(*                       term : the result term                                          *)
(*   switches every linear attributes of the elements of the t term to true.             *)
(*****************************************************************************************)  
let rec change_true (t:term):term=   
  match t with
  |State e ->  
      let res_mod = 
	{symbol= e.symbol;fromstate= e.fromstate;zone= e.zone;ident= e.ident;linear= true} in
      State res_mod
  |Node (e,termlist) ->
      let res_mod = 
	{symbol= e.symbol;fromstate= e.fromstate;zone= e.zone;ident= e.ident;linear= true} 
      in
      let res_list = map change_true termlist
      in
      Node (res_mod,res_list)
;;
(*****************************************************************************************)
(*                                                                                       *)
(*change_false function : t:the term to change                                           *)
(*                       term : the result term                                          *)
(*   switches every linear attributes of the elements of the t term to false.            *)
(*****************************************************************************************)  
let rec change_false (t:term):term=   
  match t with
  |State e ->  
      let res_mod = 
	{symbol= e.symbol;fromstate= e.fromstate;zone= e.zone;ident= e.ident;linear= false} in
      State res_mod
  |Node (e,termlist) ->
      let res_mod = 
	{symbol= e.symbol;fromstate= e.fromstate;zone= e.zone;ident= e.ident;linear= false} 
      in
      let res_list = map change_false termlist
      in
      Node (res_mod,res_list)
;;
(*****************************************************************************************)
(*linearisation                                                                           *)
(*****************************************************************************************)
let rec linearisation (t:term)(elt:res_det):term = 
 match elt with 
  |State_elt e -> t
  |Node_elt (e,treelist) -> 
      (      
	     match t with
	     |State t_e -> State t_e
	     |Node ((t_e:element), (l:term list)) -> 
		 if t_e.ident = e.ident
		 then 
		   let ar = Node(t_e,l) in
		   change_true ar
		 else
		   let res_mod = map2 elt linearisation l in 
		   Node (t_e,res_mod)
	    )	
  |Vide -> t 

(*****************************************************************************************)
(*arborisation                                                                           *)
(*****************************************************************************************)
let rec arborisation (t:term)(elt:res_det):term = 
  match elt with 
  |State_elt e -> t
  |Node_elt (e, treelist) -> 
      (      
	     match t with
	     |State t_e -> State t_e
	     |Node ((t_e:element), (l:term list)) -> 
		 if t_e.ident = e.ident
		 then 
		   let ar = Node(t_e,l) in
		   change_false ar
		 else
		   let res_mod = map2 elt arborisation l in 
		   Node (t_e,res_mod)
	    )	
  |Vide -> t 
;;
(*****************************************************************************************)
(*change_total_arborisation                                                              *)
(*****************************************************************************************)
let change_total_arborisation (call_back_refresh:term->font->return_code)
    (x:int)(y:int):unit =

  let elt = determine_elt !default_term x y in
  let res = arborisation !default_term elt in
  cote_refresh call_back_refresh res
;;
(*****************************************************************************************)
(*change_total_linear                                                                    *)
(*****************************************************************************************)
let change_total_linearisation (call_back_refresh:term->font->return_code)
    (x:int)(y:int):unit =

  let elt = determine_elt !default_term x y in
  let res = linearisation !default_term elt in
  cote_refresh call_back_refresh res
;;
(*****************************************************************************************)
let rec change_part  (b: bool)(t:term)(elt:res_det):term =
  match elt with (* we are looking at the different types of the clicked element*) 
  |State_elt e -> t
  |Node_elt (e, treelist) -> 
      (      
	     match t with
	     |State t_e -> State t_e
	     |Node ((t_e:element), (l:term list)) -> 
		 if t_e.ident = e.ident
		 then 
		   let res_mod = 
		     {symbol = t_e.symbol;
		      fromstate= t_e.fromstate;
		      zone= t_e.zone;
		      ident= t_e.ident;
		      linear= b}
		   in
		     Node (res_mod,l)
		 else
		   let res_mod = map2 elt (change_part b) l in 
		   Node (t_e,res_mod)
	    )	
  |Vide -> t 
;;

(*****************************************************************************************)
(*                                                                                       *)
(* change_to_one_level function is called by the visu module to turn the term into       *)
(* tree mode or linear mode. it depend on the boolean linear of the elt click            *)
(*****************************************************************************************)
let change_to_one_level (call_back_refresh:term->font->return_code)
    (x:int)(y:int):unit =

  let elt = determine_elt !default_term x y in
  match elt with
  | State_elt e -> ()
  | Node_elt (e, l) ->
      (
       match e.linear with
       | true -> 
	   let res = change_part false !default_term elt in
	   cote_refresh call_back_refresh res
       | false ->
	   let res = change_part true !default_term elt in
	   cote_refresh call_back_refresh res
      )
  | Vide -> ()
;;

(*****************************************************************************************)
(*                                                                                       *)
(* change_mod_lin function is called by the visu module to turn the term into linear mode*)
(*****************************************************************************************)
let change_mod_lin (unit):unit = 
  is_linear:=true;
;;
(*****************************************************************************************)
(*                                                                                       *)
(* change_mod_arbre function is called by the visu module to turn the term into tree mode*)
(*****************************************************************************************)
let change_mod_arbre (unit):unit = 
  is_linear:=false
;;

(*****************************************************************************************)
(*                                                                                       *)
(* change_mod_zoom function is called by the visu module to change the zoom to true      *)
(*****************************************************************************************)

let change_mod_zoom (call_back_refresh:term->font->return_code)(b:bool):unit =
  zoom_auto:=b;
  if !default_term= init_term then () else  (* if no automaton has been loaded no need to update *)
  let ret_cote = 
    match 
      Cotes.send_order(Update (!default_term,!default_font,!zoom_auto,!canvas_width,!canvas_height)) 
    with
    | Return_Update (r, f) -> r,f
    | Return_No_Autozoom  (r, f) -> 
	zoom_auto:=false;
	r,f
    | Error (ce, s)-> raise (Erreur "There is a problem with Labltk in Cote module")
    | _ -> failwith "Return_order not allowed"
  in
  let (r,f) = ret_cote in
  default_font:=f;
  default_term:=r;
  let ret_visu = match call_back_refresh r f with 
  | Return_Refresh  -> () (* return Refresh is OK *)
  | _ -> raise (Erreur "There is a problem with Refresh in Visu module")
  in ();;


(*****************************************************************************************)
(*                                                                                       *)
(* restart from the start symbol                                                         *)
(*****************************************************************************************)

let restart (call_back_refresh:term->font->return_code):unit =
  if !default_term= init_term then ()  (* if no automaton has been loaded no need to update *)
  else  
    begin
      zoom_auto:=true;
      default_term:= Gest.init_state();
      let ret_cote = 
	match 
	  Cotes.send_order(Update (!default_term,!default_font,!zoom_auto,!canvas_width,!canvas_height)) 
	with
	  | Return_Update (r, f) -> r,f
	  | Return_No_Autozoom (r, f) -> 
	      zoom_auto:=false;
	      r,f
	  | Error(ce, s) -> raise (Erreur "There is a problem with Labltk in Cote module")
	  | _ -> failwith "Return_order not allowed"
      in
      let (r,f) = ret_cote in
	default_font:=f;
	default_term:=r;
	let ret_visu = match call_back_refresh r f with 
	  | Return_Refresh  -> () (* return Refresh is OK *)
      | _ -> raise (Erreur "There is a problem with Refresh in Visu module")
	in ()
    end;;
    

(*****************************************************************************************)
(*                                                                                       *)
(*get_fromstate function :    x : first coords of the click                              *)
(*                            y : second coords of the click                             *)
(*                             string : the fromstate correspond to the element          *)
(*   determine the element which corresponds to (x,y) and call the linearisation function*)
(*****************************************************************************************)  
let get_fromstate (x:int)(y:int):(string*zone*term*font)= 
  let elt = determine_elt !default_term x y in
  match elt with
  | State_elt e -> (*the fromstate is absent*)
      ("",e.zone,!default_term,!default_font) 
  | Node_elt (e, (l:element tree list)) -> 
      (e.fromstate,e.zone,!default_term,!default_font) 
  | Vide -> ("",(0,0,0,0),!default_term,!default_font) 


let get_symbol (x:int)(y:int):string= 
  let elt = determine_elt !default_term x y in
  match elt with
  | State_elt e 
  | Node_elt (e, _) -> e.symbol
  | Vide -> "";;


(*****************************************************************************************)
let change_font (call_back_refresh:term->font->return_code)(f:font):unit =
  default_font:=f;
  change_mod_zoom call_back_refresh false;
  cote_refresh call_back_refresh !default_term
;;

