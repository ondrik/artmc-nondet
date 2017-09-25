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


(* ************************************************************************************************
 *                                                                                                *
 *                                AUTOMATON'S MANAGEMENT MEMBERS:                                 *
 *                                                                                                *
 **************************************************************************************************
 *                                                                                                *
 *                                   Le Roux Luka alias "K_lu"                                    *
 *                                   Durieux David alias "Duvudu"                                 *
 *                                   Brouard Robert alias "Bob"                                   * 
 *                                                                                                *
 *                          Management of automatons in the Aavisu Project                        *
 *                                                                                                *
 *                                          2002 - 2003                                           *
 *                                                                                                *
 ************************************************************************************************ *)

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

open Specifs  (* Specification of types for visualization *)
open Random
Random.self_init();; 

exception Exn_error of string;;
exception Local_read_error of string;;



module MyF= Alphabet(Symbol)
module MyX= Variable_set(Variable)
module Myterm=Term(Symbol)(MyF)(Variable)(MyX)
module Mytrs= RewriteSystem(MyF)(MyX)(Myterm)
module MyQ= State_set(Symbol)(MyF)(Myterm)(State_content)
module Myautomaton= TreeAutomata(Symbol)(MyF)(Variable)(Myterm)(State_content)(Mytrs)(MyQ)
module MyGamma= Gamma(Symbol)(MyF)(Variable)(MyX)(Myterm)(Mytrs)(MyQ)(Myautomaton)
module Myspec= Specification(MyF)(MyX)(Myterm)(Mytrs)(Myautomaton)(MyGamma)

type timbuk_automaton= Myautomaton.t
type timbuk_state_set= MyQ.t

let rec convert_config (t: Myterm.t): simple_term=
  (match t with 	  
  | Common.Special(t) -> (State (Myterm.to_string t))
  | Common.Fsym(f, largs) -> (Node ((Symbol.to_string f), (convert_l_config largs)))
  | Common.Const(a) -> (Node ((Symbol.to_string a), []))
  | _ -> failwith "No constants nor variables in configurations!")
and convert_l_config (lt: Myterm.t list): simple_term list= List.map convert_config lt


let convert_transition (trans: Mytrs.rule): transition=
  ((convert_config (Mytrs.lhs trans)),(convert_config (Mytrs.rhs trans)))
  

let rec convert_state_set (sts: MyQ.t): string list=
  if MyQ.is_empty sts then []
  else 
    let first= MyQ.first sts in
    let rem= MyQ.remainder sts in
    (Myterm.to_string first)::(convert_state_set rem)
			

let convert_automaton (aut: Myautomaton.t): automaton=
  {q= convert_state_set (Myautomaton.get_states aut);
   f= convert_state_set (Myautomaton.get_final_states aut);
   t= List.map convert_transition (Mytrs.to_list (Myautomaton.get_transitions aut))}





(* ********************************************************************************************** *)
(*                                     Textual screenplays                                        *)
(* ********************************************************************************************** *)


(* ------------------------------------ cls () :unit -------------------------------------------- *)
(* Function which empties the screenplay's buffer *)
let cls () :unit = flush stdout;;


(* ------------------------------------ println () :unit ---------------------------------------- *)
(* Function which displays a new line on the screen *)
let println () :unit = print_newline();;


(* --------------------------------- print_elmt (elmt:element) :unit ---------------------------- *)
(* Function which displays an object of type "element" on screen *)
let print_elmt (elmt:element) :unit = print_string elmt.symbol;;


(* ----------------------------- print_tree (tree:term) :unit ------------------------------------*)
(* Function which displays an object of type "term" on screen *)
let rec print_tree (tree:term) :unit = match tree with
| State elmt -> print_elmt elmt
| Node (elmt,tree_list) ->
    print_elmt elmt;
    if (tree_list <> []) then (print_string "(");
    let rec print_intern tree_list = match tree_list with
    | [] -> ()
    | h::t ->
	print_tree h;
	if (t=[])
	    then (print_string ")"; cls())
	    else (print_string ",");
	print_intern t
    in print_intern tree_list;;


(* ----------------------- print_stree (tree:simple_element tree) :unit ------------------------- *)
(* Function which displays an object of type "simple_element tree" on screen *)
let rec print_stree (tree:simple_element tree) :unit = match tree with
| State elmt -> print_string elmt
| Node (elmt,tree_list) ->
    print_string elmt;
    if (tree_list <> []) then (print_string "(");
    let rec print_intern tree_list = match tree_list with
    | [] -> ()
    | h::t ->
	print_stree h;
	if (t=[])
	    then print_string ")"
	    else (print_string ",");
	print_intern t
    in print_intern tree_list;;


(* ------------------------------- print_histo (histo:term list) :unit -------------------------- *)
(* Function which displays the history (an object of type "term list") on screen *)
let rec print_histo (histo:term list) :unit =  match histo with
| h::t -> print_tree h; println(); print_histo t
| [] -> println();;


(* ---------------------------------- print_ident (id:ident) :unit ------------------------------ *)
(* Function which displays an object of type "ident" on screen *)
let print_ident (id:ident) :unit =
  print_string "ident: [";
  let rec intern (id:ident):unit = match id with
  | [] -> print_string "]"
  | h::t -> 
      (
       print_int h;
       (if t<>[] then print_string "; ");
       intern t
      )
  in intern id;;


(* ---------------------------- print_automaton (automat:automaton) :unit ----------------------- *)
(* Function which displays an object of type "automaton" on screen *)
let print_automaton (automat:automaton) :unit =
  let rec intern f l = match l with
  | [] -> ()
  | h::t -> f h; intern f t
  in
  (
   print_string ("States: ");
   intern (function se -> print_string (se^" ")) automat.q;
   println ();
   print_string ("final states: ");
   intern (function se -> print_string (se^" ")) automat.f;
   println ();
   print_string ("transitions: ");
   println ();
   intern
     (
      function t ->
	print_stree (fst t);
	print_string (" -> ");
	print_stree (snd t);
	println ()
     )
     automat.t
  );;










(* ********************************************************************************************** *)
(*                             Computation functions on automatons                                *)
(* ********************************************************************************************** *)


(* The automaton on which this module works on: it's a reference on an object of type "automaton" *)
let auto = ref ({q=[];f=[];t=([]:transition list)}:automaton);;

(* another copy of the automaton without the transitions from the start symbol to the states *)
let auto_init = ref ({q=[];f=[];t=([]:transition list)}:automaton);;

(* the reserved symbol for root of language browsing *) 

let start_symb= ref "";;

(* NB: 'set' are initials for << simple_element tree >> *)


(* ------------------- set_to_term (simple_tree:simple_element tree) :term ---------------------- *)
(* Function which converts an object of type "simple_element tree" to an object of type "term" *)
let rec set_to_term (simple_tree:simple_element tree) :term = match simple_tree with
| State s_elmt -> State {symbol = s_elmt; fromstate = ""; zone = (0,0,0,0); ident = []; linear = true}
| Node (s_elmt,s_tree_list) -> Node (
    {symbol= s_elmt; fromstate = ""; zone = (0,0,0,0); ident = []; linear = true},
    let rec set_intern l = match l with
    | [] -> []
    | h::t -> (set_to_term h)::(set_intern t)
    in set_intern s_tree_list
   );;


(* -------------------------- get_selection (symb:string) :term list ---------------------------- *)
(* Function which returns the list of terms corresponding to the possible transitions from the
   symbol 'symb' given as argument of type "string" *)
let get_selection (symb:string) :term list =
  let rec get_intern (s:string) l = match l with
  | [] -> []
  | h::t -> match snd h with
    | State elmt -> if (elmt = s)
        then
	let mod_e =
	  (
	   match (set_to_term (fst h)) with
	   | State e -> State {symbol = e.symbol; fromstate = elmt; zone = e.zone; ident = e.ident; linear = e.linear}
	   | Node (e,termlist) -> Node ({symbol= e.symbol; fromstate= elmt; zone = e.zone; ident = e.ident; linear = e.linear}, termlist)
	  )
	in mod_e::(get_intern s t)
	else (get_intern s t)
    | Node (_,_) -> raise (Exn_error "get_selection: No selection for a not state symbol")
  in get_intern symb (!auto).t;;










(* ********************************************************************************************** *)
(*                                          Open order, tools                                     *)
(* ********************************************************************************************** *)


(* ------------------------------ getStartSymb () :simple_element ------------------------------- *)
(* Function which returns the 'Start' symbol as the only existing final state in any automaton, or
   '#Start#' or ... any time a 'Start' final state already exists in the automaton *)
let getStartSymb () :simple_element =
  let rec intern1 (sl:string list) (s:string):bool = match sl with
  | [] -> false
  | h::t -> if (h=s)
  then true
  else intern1 t s
  in
  let rec intern2 (sl:string list) (s:string):simple_element =
    if intern1 sl s
    then intern2 sl ("#"^s^"#")
    else s
  in intern2 !auto.q "Start";;


(* -------------------------------- augmentAuto () :unit ---------------------------------------- *)
(* Function which adds transitions which lead from the final states to the added state 'Start'
   which becomes the only final state.
   NB: in case where an other 'start' state already exits, such a problem is resolved by the
       getStartSymb function *)

let rec make_trans_to_start (fsl:string list):transition list = 
  let stateStart = State (!start_symb) in
    match fsl with
      | [] -> []
      | h::t -> (State h, stateStart)::(make_trans_to_start t);;


let augmentAutoFinal () :unit =
  begin
    auto:= !auto_init;
    auto := {q= !auto.q; f= [!start_symb]; t= (make_trans_to_start !auto.f) @ !auto.t}
  end;;


let augmentAutoAll () :unit =
  begin
    auto:= !auto_init;
    auto := {q= !auto.q; f= [!start_symb]; t= (make_trans_to_start !auto.q) @ !auto.t}
  end;;


let init_state(): term=
  State {symbol= !start_symb; fromstate=""; zone= (0,0,0,0); ident=[];linear=true}


type file_type= Txt|Other

(* --------------------------------- type_of_file (s:string) :file_type --------------------------------- *)
(* Function which determines file type: either Xml, Txt or Other *)
(* Text automata files begin by an "Ops" symbol (or a comment symbol, whereas Xml automata files begin by "<" *)

let type_of_file (s: string): file_type=
  let ic= open_in s in
  let c= ref 'a' in
    try (
      begin
	c:= input_char ic;
	while !c=' ' or !c='\t' or !c='\n' do
	  c:= input_char ic
	done;
	match !c with
	    'O' |'(' -> Txt   
	  | _ -> Other
      end)
    with End_of_file -> Other

(* --------------------------------- parse_file (s:string) :unit -------------------------------- *)
(* Function which stores in the 'auto' referency the automaton which is in the file which is given
   as parameter.
   Executes also the function augmentAuto() *)

let parse_file (s:string) :unit =
  let ft= type_of_file s in
    match ft with 
	Other -> raise (Local_read_error "Other type of file")
      | Txt -> 
	  let s= Myspec.file_parse s in
	  let laut= Myspec.get_list_automata s in
	    if laut=[] 
	    then raise (Local_read_error "No automaton in file")
	    else 
	      let (_, first_aut)= List.hd laut in  (* first_aut is an automaton *)
		auto := convert_automaton first_aut;
		start_symb:= getStartSymb();
		auto_init:= !auto;
		augmentAutoFinal();;


let direct_build (a: automaton): unit=
  auto := a;
  start_symb:= getStartSymb();
  auto_init:= !auto;
  augmentAutoFinal();;
    

(* ********************************************************************************************** *)
(*                           Function's applying on trees and list of trees                       *)
(* ********************************************************************************************** *)


(* ------------ apply1_list (i:int) (f:term -> term) (tree_list:term list) :term list ----------- *)
(* Function which, given an index i, a function to apply 'f' of type "tree -> tree" and a list of
   trees (for example, a list of sons), returns this list with the tree of index i, modified by 'f'.
   NB: this function is used in the function apply1_tree *)
let rec apply1_list (i:int) (f:term -> term) (tree_list:term list) :term list = match tree_list with
  | [] -> raise (Exn_error "apply1_list: No matching ident")
  | h::t -> if i=1
	     then (f h)::t
	     else h::(apply1_list (i-1) f t);;










(* ********************************************************************************************** *)
(*                                             Accessors                                          *)
(* ********************************************************************************************** *)


(* ------------------------------- get_i (i:int) (l:'a list) :'a -------------------------------- *)
(* Function which returns the ith element of a list *)
let rec get_i (i:int) (l:'a list) :'a = match i,l with
| _,[] -> raise (Exn_error "get_i: index out of bound")
| 0,(h::t) -> h
| n,(h::t) -> get_i (n-1) t;;



(* --------------------------- get_elmt (id:ident) (tree:term) :element ------------------------- *)
(* Function which, given an identifier 'id' and a term 'tree' returns the element which corresponds
   to 'id' in the term *)
let get_elmt (id:ident) (tree:term) :element =
  let rec get_intern accuVide id tree = match tree, accuVide@id with
  | Node (elmt,[]),i
  | State elmt,i ->
        if (elmt.ident=i)
	then elmt
	else raise (Exn_error "get_elmt: No matching ident")
  | Node (elmt,tree_list),i -> 
        if (i = elmt.ident)
        then elmt
        else 
          (
	   match id with
	   |  h::t -> get_intern (accuVide@[h]) t (List.nth tree_list (h-1))
	   | [] -> raise (Exn_error "get_elmt: No matching ident*")
	  )
  in get_intern [] id tree;;










(* ********************************************************************************************** *)
(*                                             History                                            *)
(* ********************************************************************************************** *)


(* The history of actions done on an automaton: it's a reference on a list of objects
   of type "term * ident" *)
let history = ref ([]:(term*ident) list);;


(* A pointer in the history:
   if the last action is neither an undo command nor a redo command, its value is zero *)
let history_pointer = ref 0;; 


(* The length of the history *)
let history_length = ref 0;;


(* ------------------------------------ undo (x:int) :unit -------------------------------------- *)
(* Function which sets the pointer on the valid term after an undo command call *)
let undo (x:int) :unit =
  if (x > !history_length - !history_pointer - 1)
  then raise (Exn_error "undo: There is not enough actions to undo")
  else history_pointer := !history_pointer + x;;


(* ------------------------------------ redo (x:int) :unit -------------------------------------- *)
(* Function which sets the pointer on the valid term after an redo command call *)
let redo (x:int) :unit =
  if (x > !history_pointer)
  then raise (Exn_error "redo: There is not enough actions to redo")
  else history_pointer := !history_pointer - x;;


(* --------------------------------- reset_histo () :unit --------------------------------------- *)
(* Functions which sets the history to empty *)
let reset_histo () :unit = history := []; history_pointer := 0; history_length := 0;;


(* ----------------------------- get_current () : (term*ident) ---------------------------------- *)
(* Function which returns the current term in the history *)
let get_current () :(term*ident) = (List.nth !history !history_pointer);;


(* --------------------------------- add_histo (t:term) :unit ----------------------------------- *)
(* Function which adds in the history the term given as parameter *)
let add_histo (t:term*ident) :unit =
  (if (!history_pointer <> 0) 
  then
    history := get_current()::(!history);
    history_pointer := 0;
    history_length := !history_length + 1
  );
  history := t::(!history);
  history_length := !history_length + 1;;










(* ********************************************************************************************** *)
(*                                  Tool of transformation of a term                              *)
(* ********************************************************************************************** *)


(* ------------------------------- update_idents (tree:term) :term ------------------------------ *)
(* Function which, given a term, sets all its identifiers *)
let update_idents (tree:term) :term =
  let rec update_intern (id:ident) (tree:term):term = match tree with
  | State elmt -> State {symbol= elmt.symbol; fromstate = ""; zone = elmt.zone; ident = id; linear = elmt.linear}
  | Node (elmt,tree_list) ->
      Node (
      {symbol= elmt.symbol; fromstate = elmt.fromstate; zone = elmt.zone; ident = id; linear = elmt.linear},
      let rec apply (i:int) (tree_list:term list):term list = match tree_list with
      | [] -> []
      | h::t -> (update_intern (id@[i]) h)::(apply (i+1) t)
      in (apply 1 tree_list)
     )
  in update_intern [] tree;;


(* update_mode linear/tree for a term *)

let rec update_mode (b: bool) (t: term): term=
  match t with
      State _ -> t
    | Node(elmt, tree_list) ->
	let elmtbis = {symbol = elmt.symbol; fromstate = elmt.fromstate; 
		       zone = elmt.zone; ident = elmt.ident; linear = b}
	in 
	  Node(elmtbis, List.map (update_mode b) tree_list);;


(* -------------------- replace_subtree (id:ident) (tree:term) (st:term) :term ------------------ *)
(* Function which, given an identifier 'id' of type "int list", a sub-tree 'st' and a tree,
   returns this tree whose sub-tree identified by 'id' replaced by 'st' *)
let replace_subtree (id:ident) (tree:term) (st:term) :term =
  let rec replace_intern accuVide id st tree = match tree, accuVide@id with
  | State elmt, i -> if (i = elmt.ident)
                    then st
                    else raise (Exn_error "replace_subtree: No matching ident")
  | Node (elmt,tree_list),[] -> st
  | Node (elmt,tree_list), i -> if (i = elmt.ident)
                    then st
                    else match id with
                    | [] -> raise (Exn_error "replace_subtree: No matching ident*") 
                    | h::t -> Node (elmt,apply1_list h (replace_intern (accuVide@[h]) t st) tree_list)
  in update_idents (replace_intern [] id st tree);;










(* ********************************************************************************************** *)
(*                                      Cleaning lists functions                                  *)
(* ********************************************************************************************** *)

let rec comp_list (f:'a -> 'a -> bool) (l1:'a list) (l2:'a list) :bool = match (l1,l2) with
| [], [] -> true
| h1::t1, h2::t2 -> (f h1 h2) && comp_list f t1 t2
| _ -> false;; 

let rec term_equal (t1:term) (t2:term) :bool = match (t1, t2) with
| State e1, State e2 -> e1.symbol = e2.symbol
| Node (e1, tl1), Node (e2, tl2) -> (e1.symbol = e2.symbol)&&(comp_list term_equal tl1 tl2)
| _ -> false;;

let add_term_list (tt:term) (tl:term list) :term list =
  let rec intern (accu:'a list) (tt:'a) (tl:'a list) =
    match tl with
    | [] -> accu@[tt]
    | h::t ->
	if (term_equal h tt)
	then accu@(h::t)
	else intern (accu@[h]) tt t
  in intern [] tt tl;;



(* --------------------------- add_list (tt:'a) (tl:'a list) :'a list --------------------------- *)
(* Function which adds an element of type "'a" in a "'a list" object if this element does not
   already exits in this list. If not, it is not added in the list *)
let add_list (tt:'a) (tl:'a list) :'a list =
  let rec intern (accu:'a list) (tt:'a) (tl:'a list) =
    match tl with
    | [] -> accu@[tt]
    | h::t ->
	if h=tt
	then accu@tl
	else intern (accu@[h]) tt t
  in intern [] tt tl;;


(* ------------------------ union_list (l1:'a list) (l2:'a list) :'a list ----------------------- *)
(* Function which realizes the exclusive union of two lists and returns it as new list *)
let rec union_list (l1:'a list) (l2:'a list) :'a list = match l1 with
| [] -> l2
| h::t -> union_list t (add_list h l2);;


(* --------------------------- union_xlist (ll:'a list list) :'a list --------------------------- *)
(* Function which realize the exclusive union of more than two lists and returns it as new list *)
let rec union_xlist (ll:'a list list) :'a list = match ll with
| [] -> []
| l1::xl -> union_list l1 (union_xlist xl);;


(* ------------------------------ clean_list (l:'a list) :'a list ------------------------------- *)
(* Function which << cleans >> a list by removing all its doubles by realizing a exclusive union
   between this list and an empty list *)
let clean_list (l:'a list) :'a list = union_list l [];;










(* ********************************************************************************************** *)
(*                                 Function get_symbs () :string list                             *)
(*                            Used by extern modules for intern operations                        *)
(* ********************************************************************************************** *)


(* ---------------------------------- get_states () :string list -------------------------------- *)
(* Function which returns the list of symbols of states of the current automaton *)
let get_states () :string list = !auto.q;;


(* -------------------- mapconcat (f:'a -> 'b list) (l:'a list) :'b list ------------------------ *)
(* Function which applies a function 'f' on each element of type "'a" of a list and concatenates
   the "'b" lists get after each transformation of a "'a" in order to return a list of "'b"
   (instead of getting a list (of 'b lists) which will have to be flattened just after that) *)
let rec mapconcat (f:'a -> 'b list) (l:'a list) :'b list = match l with
| [] -> []
| h::t -> (f h)@(mapconcat f t);;


(* ------------------------ get_symbs_sterm (tt:simple_term) :string list ----------------------- *)
(* Function which returns the list of all the symbols get from a "simple_term" *)
let rec get_symbs_sterm (tt:simple_term) :string list = match tt with
| State _ -> []
| Node (elmt, term_list) -> elmt::(mapconcat get_symbs_sterm term_list);;


(* ----------------------------- get_symbs_transition () :string list --------------------------- *)
(* Function which returns all the symbols of the transitions list from the current automaton *)
let get_symbs_transition () :string list =
  let rec intern (tl:transition list):string list =
    match tl with
    | [] -> []
    | h::t -> let (a,b) = h in
      union_xlist [(get_symbs_sterm a); (get_symbs_sterm b); (intern t)]
  in intern (!auto.t);;


(* ----------------------------------- get_symbs () :string list -------------------------------- *)
(* Function which returns a list composed of symbols of the states and the symbols of the
   transitions of the current automaton *)
let get_symbs () :string list = ((get_states ())@(get_symbs_transition ()));;


(* ------------------------------------ print_symbs () :unit ------------------------------------ *)
(* Function which displays all the symbols of the current automaton on the screen *)
let print_symbs () :unit =
  print_string "[";
  let rec intern (l:string list):unit = match l with
  | [] -> print_string "]\n"
  | h::t -> print_string h; (if t <> [] then print_string "; "); intern t
  in intern (get_symbs ());;














(* ********************************************************************************************** *)
(*                                 calcul d'un automate pour la géné alea                         *)
(* ********************************************************************************************** *)

type autorand = {qr: (string*int) list; fr: string list; tr: (transition * int) list};;
let autorand = ref ({qr=[];fr=[];tr=([]:(transition*int) list)}:autorand);;


let getweight (q:string):int =
  let rec intern (tl:(transition * int) list) = match tl with
  | [] -> 0
  | (t,0)::tt -> intern tt
  | (t,i)::tt ->
      if (snd t = State q)
      then 
	(
	 let next = intern tt in
	 if (i<=next)||(next=0)
	 then i
	 else next
	)
      else intern tt
  in
  intern !autorand.tr;;

let rec list_plus (l:(int*bool) list) :(int*bool) = match l with
| [] -> (0,true)
| (n1,b1)::t -> let (n2,b2) = list_plus t in
  ((n1+n2),(b1&&b2));;

let calculweight (t:transition) :int =
  let rec intern (st:simple_term):(int*bool) = match st with
  | State q -> let w = getweight q in (w,(w>0))
  | Node (_, term_list) -> let li = List.map intern term_list in
    list_plus li
  in
  let result = intern (fst t) in
  if ((snd result) = false)
  then 0
  else (fst result) + 1;;

let init_autorand () :unit =
  let q = List.map (fun q -> (q,0)) !auto.q in
  let f = !auto.f in
  let t = List.map (fun t -> (t,0)) !auto.t in
  autorand := {qr=q; fr=f; tr=t};;

let rec calculiw (tl:(transition*int) list) (i:int) :(transition*int) list = match tl with
| [] -> []
| (tr,0)::t ->
    let w = calculweight tr in
    let next = calculiw t i in
    if (w = i)
    then (tr,w)::next
    else (tr,0)::next
| (tr,w)::t -> (tr,w)::(calculiw t i);;

let calculisdone () :bool =
  let rec intern (tl:(transition*int) list) :bool = match tl with
  | [] -> true
  | (_t,0)::t -> false
  | (_t,w)::t -> intern t
  in
  intern (!autorand.tr);;

let getqr () :unit =
  let rec intern (ql:(string*int) list) :(string*int) list = match ql with
  | [] -> []
  | (q,_w)::t -> (q, (getweight q) )::(intern t)
  in
  let q = intern !autorand.qr in
  let f = !autorand.fr in
  let t = !autorand.tr in
  autorand := {qr=q; fr=f; tr=t};;

let getautorand () :unit =
  init_autorand ();
  let rec intern (i:int) :unit =
    if ( calculisdone () || (i=100))
    then ()
    else
      (
       let q = !autorand.qr in
       let f = !autorand.fr in
       let t = calculiw (!autorand.tr) i in
       autorand := {qr=q; fr=f; tr=t};
       intern (i+1)
      )
  in
  intern 1;
  getqr ();;

let print_autorand (automat:autorand) :unit =
  let rec intern f l = match l with
  | [] -> ()
  | h::t -> f h; intern f t
  in
  (
   print_string ("States: ");
   intern (function se -> print_string ((fst se)^" w:"); print_int (snd se)) automat.qr;
   println ();
   print_string ("final states: ");
   intern (function se -> print_string (se^" ")) automat.fr;
   println ();
   print_string ("transitions: ");
   println ();
   intern
     (
      function t ->
	print_stree (fst (fst t));
	print_string (" -> ");
	print_stree (snd (fst t));
	print_string " w:";
	print_int (snd t);
	println ()
     )
     automat.tr
  );;

let get_select_rand (symb:string) (nb_step:int) :term list =
  let rec get_intern (s:string) l = match l with
  | [] -> []
  | h::t ->
      if ((snd h)<=nb_step)
      then
	(
	 match (snd (fst h)) with
	 | State elmt -> if (elmt = s)
         then
	     let mod_e =
	       (
		match (set_to_term (fst (fst h))) with
		| State e -> State {symbol = e.symbol; fromstate = elmt; zone = e.zone; ident = e.ident; linear = e.linear}
		| Node (e,termlist) -> Node ({symbol= e.symbol; fromstate= elmt; zone = e.zone; ident = e.ident; linear = e.linear}, termlist)
	       )
	     in mod_e::(get_intern s t)
	 else (get_intern s t)
	 | Node (_,_) -> raise (Exn_error "get_select_rand: No selection for a not state symbol")
	)
      else (get_intern s t)
  in get_intern symb (!autorand).tr;;

let rec list_p (l:int list) :int = match l with
| [] -> 0
| n1::t -> let n2 = list_p t in
  (n1+n2);;

let rec calcultw (t:term) = match t with
| State elt -> getweight elt.symbol
| Node (_elt,term_list) ->
    let li = List.map calcultw term_list in
    list_p li;;






















(* ************************************************************************************************
 *                                                                                                *
 *                                       Random terms generation                                  *
 *                                                                                                *
 **************************************************************************************************
 *                                                                                                *
 *    Such functions allow the random generation of terms from an automaton and parameters for    *
 *    computations. A data with the 'step' type represents a step of computation. It is a couple  *
 *    of lists whose elements are terms associated to a list of identifiers.                      *
 *    The first list of such a couple contains some non-final terms (with its states), and the    *
 *    second one some final states (without states). The list, which is associated to each term,  *
 *    contains the identifiers of the states of each of those terms.                              *
 *                                                                                                *
 ************************************************************************************************ *)
type step = (term * ident list) * int;;


(* ------------------------ get_new_idents (tt:term) (id:ident) :ident list --------------------- *)
(* This function sets the list of identifiers associated to a term, it searches in the 'tt' term,
   from the 'id' identifier, the complete list of states by returning the list of their identifiers.
   NOTE: if id=[], the research is done in the entire term (from the root) *)
let rec get_new_idents (tt:term) (id:ident) :ident list = match tt,id with
| (State elmt,_) -> [elmt.ident]
| (Node (_,term_list),h::t) -> get_new_idents (List.nth term_list (h-1)) t
| (Node (_,term_list),[]) -> List.concat (List.map (fun x -> get_new_idents x []) term_list);;


(* ------------------------------------ get_first_step (tt:term) :step -------------------------- *)
(* This function computes from a given term a data whose type is 'step', it is the beginning of a
   random generation *)
let get_first_step (tt:term) :step = ((tt,(get_new_idents tt [])),0);;

let get_nth (i:int) (l:'a list):('a*'a list) =
  let rec intern (i:int) (accu:'a list) (l:'a list) :('a*'a list) = match l with
  | [] -> raise (Exn_error "get_nth: index out of bound")
  | h::t -> if (i=1) then (h, (List.append accu t)) else intern (i-1) (accu@[h]) t
  in intern i [] l;;

let get_next_step (s:step) (nb_steps:int) :(step*bool) =
  let ((tt, idlist), nb_steps_left) = (fst s, (nb_steps - (snd s))) in
    if ((List.length idlist)=0) then (((fst s),nb_steps),false) else
      let (id, ids_left) = get_nth (Random.int(List.length idlist) + 1) idlist in
      let state = (get_elmt id tt).symbol in
      let wa = (nb_steps_left - (calcultw tt) + (getweight state)) in
      let selec_rand = get_select_rand state wa in
      let only_one = (List.length selec_rand = 1) in
	if ((List.length selec_rand)=0) 
	then (raise (Exn_error ("Set of random terms is empty!\nSome states recognize an empty language\n or random depth/time is too short")))
	else
	  let new_subtree = List.nth selec_rand (Random.int(List.length selec_rand)) in
	  let new_tt = replace_subtree id tt new_subtree in
	  let new_idlist = List.append ids_left (get_new_idents new_tt id) in
	    (((new_tt, new_idlist), ((snd s) + 1)), only_one);;


(* ----------------- rand_gen (tt:term) (nb_steps:int) (maxt:float) (nb_terms:int) :(term list) ---------- *)
(* This function samples the results given by more than one successif xgen, 'max' represents the
   number of terms kept at random at each step AND the number of terms to get, at least, before the
   function rand_gen ends *)


let rand_gen (tt:term) (nb_steps:int) (maxt:float) (nb_terms:int) :(term list) =
  let fs = get_first_step tt in
  let ttime= maxt +. Sys.time() in
  let rec intern1 (nb_terms:int):term list =
    let rec intern2 (s:step) :(term*bool) =
      let (next, only_one) = get_next_step s nb_steps in
      let stop = only_one && ((snd (fst next)) = []) && ((snd next) = 1) in
      let nb_steps_left = nb_steps - (snd next) in
      if (nb_steps_left = 0) || stop
      then ((fst (fst next)),stop)
      else intern2 next
    in
    let (new_tt,stop) = intern2 fs in
    if stop || (nb_terms = 1) || (ttime <= Sys.time())
    then [new_tt]
    else add_term_list new_tt (intern1 (nb_terms - 1))
  in intern1 nb_terms;;






(* ********************************************************************************************** *)
(*                                   Function which runs the orders                               *)
(* ********************************************************************************************** *)
let send_order (o:order) :return_code = match o with
| OpenDirect a ->
    direct_build a;
    getautorand ();
    let sa = State {
      symbol = (
	   match !auto.f with 
	   | h::t -> h
	   | [] -> raise (Exn_error "send_order: Open: no final states")
	  );
      fromstate = "";
      zone = (0,0,0,0);
      ident = []; 
      linear = true} 
    in (reset_histo (); Return_Open sa)

| Open s ->
    (
     try 
       (
	parse_file s;
	getautorand ();
	let a = State {
	  symbol = 
	  (
	   match !auto.f with 
	   | h::t -> h
	   | [] -> raise (Exn_error "send_order: Open: no final states")
	  );
	  fromstate = "";
	  zone = (0,0,0,0);
	  ident = []; 
	  linear = true} 
	in (reset_histo (); Return_Open a)
       ) 
     with
     | Sys_error se -> Error (Error_Open_cant_find_the_file, "parse_file: "^se)
     | Local_read_error("No automaton in file") -> Error (Error_Open_wrong_type_of_file, "parse_file: "^s^": no automaton found")
     | Local_read_error("Other type of file") -> Error (Error_Open_wrong_type_of_file, "parse_file: "^s^": neither XML or TXT automaton file")
     | Stream.Error(_) -> Error (Error_Open_wrong_type_of_file, "parse_file: "^s^": bad TXT automaton format")
    )
| Selection (id,t) ->
    Return_Selection (get_selection (get_elmt id t).symbol)
| Fold (id,t) ->
    (* We do not treat yet and perhaps never the case where 'fs' is empty (we do not receive such an order) *)
    let fs = (get_elmt id t).fromstate in
    let new_term = replace_subtree id t (State {symbol = fs; fromstate = ""; zone = (0,0,0,0); ident = []; linear = true}) in
    (
     add_histo (new_term,id);
     Return_Fold new_term
    )
| Unfold (id,t1,t2,b) ->
    let t2bis = update_mode b t2 in
    let new_term = replace_subtree id t1 t2bis in
    (
     add_histo (new_term,id);
     Return_Unfold new_term
    )
| Undo n ->
    (
     try (undo n; Return_Undo (fst (get_current ()))) with 
     | Exn_error s -> Error (Error_Undo, s)
    )
| Redo n ->
    (
     try (redo n; Return_Redo (fst (get_current ()))) with 
     | Exn_error s -> Error (Error_Redo, s)
    )
| GetHistory ->
    Return_GetHistory !history
| GetRandom (id,tt,nb_step,maxt,nb_terms) ->
    let ran_state = State {symbol = (get_elmt id tt).symbol; fromstate = ""; zone =(0,0,0,0); ident = []; linear = true} in
    Return_GetRandom (rand_gen ran_state nb_step maxt nb_terms)
| _ -> raise (Exn_error "send_order: Order non implemented till today, sorry ! Perhaps a next time, thanks for coming ...");;



