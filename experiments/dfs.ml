open Taml;;
open Input;;


(* Depth first search 
   - using parent pointers (no stack) *)

let dfs=[
	(*  0 *) X_ass_y ("x","root",1);
	(*  1 *) If_xnull ("x",12,2); 
	(*  2 *) X_ass_yleft("y","x",3);
	(*  3 *) If_xnull ("y",6,4); 
	(*  4 *) If_xdata("y","marked",6,5);
	(*  5 *) X_ass_y ("x","y",1);
	(*  6 *) X_ass_yright("y","x",7);
	(*  7 *) If_xnull ("y",10,8); 
	(*  8 *) If_xdata("y","marked",10,9);
	(*  9 *) X_ass_y ("x","y",1);
	(* 10 *) Setdata("x","marked",11);
	(* 11 *) X_ass_yup("x","x",1);
	(* 12 *) Exit
	];;


	
	

(* Compile program = create transducers *)
let comp_dfs= compile_program dfs ["root";"x";"y"] ["marked";"unmarked"];;

(* Create timbuk alphabeth *)
let alpha=create_alphabeth  ["root";"x";"y"] ["marked";"unmarked"];;

(* some init automata *)
(*
let init_dfs=automaton alpha "
	States qbot q1 qroot qnull qundef qacc q0
	Final States qacc
	Transitions 
	   bot0 -> q0
	   bot2(qbot,qbot) -> qbot
	   bot2(q0,q0) -> qbot
	   bot2(q0,qbot) -> qbot
	   bot2(qbot,q0) -> qbot
	   bot2(qbot,qbot) -> q1
	   unmarked(q1,q1) -> q1
           rootunmarked(q1,q1) -> qroot
	   NULL(qroot,qbot) -> qnull
	   xyUNDEF(qnull,qbot) -> qundef
	   normal(qundef,qbot) -> qacc ";;
*)
	   
(* original one *)
let init_dfs=automaton alpha "
	States qbot q1 qroot qnull qundef qacc
	Final States qacc
	Transitions 
	   bot0 -> qbot
	   bot2(qbot,qbot) -> qbot
	   bot2(qbot,qbot) -> q1
	   unmarked(q1,q1) -> q1
           rootunmarked(q1,q1) -> qroot
	   NULL(qroot,qbot) -> qnull
	   xyUNDEF(qnull,qbot) -> qundef
	   normal(qundef,qbot) -> qacc ";;
	   


let init_dfs_simple=automaton alpha "
	States qbot q1 qroot qnull qundef qacc
	Final States qacc
	Transitions 
	   bot0 -> qbot
	   bot2(qbot,qbot) -> qbot
	   unmarked(qbot,qbot) -> q1
           rootunmarked(q1,q1) -> qroot
	   NULL(qroot,qbot) -> qnull
	   xyUNDEF(qnull,qbot) -> qundef
	   normal(qundef,qbot) -> qacc ";;
	

let bad=automaton alpha "
	States q1 q2
	Final States q2
	Transitions
	  bot0 -> q1
	  bot2(q1,q1) -> q1
	  unmarked(q1,q1) -> q1
	  xunmarked(q1,q1) -> q1
	  yunmarked(q1,q1) -> q1
	  rootunmarked(q1,q1) -> q1
	  xyunmarked(q1,q1) -> q1
	  rootxunmarked(q1,q1) -> q1
	  rootyunmarked(q1,q1) -> q1
	  rootxyunmarked(q1,q1) -> q1
	  marked(q1,q1) -> q1
	  xmarked(q1,q1) -> q1
	  ymarked(q1,q1) -> q1
	  rootmarked(q1,q1) -> q1
	  xymarked(q1,q1) -> q1
	  rootxmarked(q1,q1) -> q1
	  rootymarked(q1,q1) -> q1
	  rootxymarked(q1,q1) -> q1
	  NULL(q1,q1) -> q1
	  xNULL(q1,q1) -> q1
	  yNULL(q1,q1) -> q1
	  rootNULL(q1,q1) -> q1
	  xyNULL(q1,q1) -> q1
	  rootxNULL(q1,q1) -> q1
	  rootyNULL(q1,q1) -> q1
	  rootxyNULL(q1,q1) -> q1
	  UNDEF(q1,q1) -> q1
	  xUNDEF(q1,q1) -> q1
	  yUNDEF(q1,q1) -> q1
	  rootUNDEF(q1,q1) -> q1
	  xyUNDEF(q1,q1) -> q1
	  rootxUNDEF(q1,q1) -> q1
	  rootyUNDEF(q1,q1) -> q1
	  rootxyUNDEF(q1,q1) -> q1
	  normal(q1,q1) -> q1
	  bad(q1,q1) -> q2 ";;

(* INPUT configuration of main procedure is a list of automata
   - first is init one
   - others are empty 
   
   Create this list by function "create_init_conf"*)





