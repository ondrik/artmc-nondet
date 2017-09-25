open Taml;;
open Input;;


(********* Red-Black Tree Rebalancing after an Insert - using parent pointers (no stack) ********)

let rbt_reb_ins = [
	(*  0 *) Setdata("x","red",1);
	(*  1 *) If_xeqy("x","root",37,2); 
	(*  2 *) X_ass_yup("xp","x",3);
	(*  3 *) If_xdata("xp","red",4,37);
	(*  4 *) X_ass_yup("xpp","xp",5);
	(*  5 *) X_ass_yleft("y","xpp",6);
	(*  6 *) If_xeqy("xp","y",7,22); 
	(*  7 *) X_ass_yright("y","xpp",8);      (******* Left branch *******)
	(*  8 *) If_xdata("y","red",9,13);
	(*  9 *) Setdata("xp","black",10);
	(* 10 *) Setdata("y","black",11);
	(* 11 *) Setdata("xpp","red",12);
	(* 12 *) X_ass_y ("x","xpp",1);
	(* 13 *) X_ass_yright("y","xp",14);
	(* 14 *) If_xeqy("x","y",15,19); 
	(* 15 *) X_ass_y ("x","xp",16);
	(* 16 *) Leftrotate("x",17);
	(* 17 *) X_ass_yup("xp","x",18);
	(* 18 *) X_ass_yup("xpp","xp",19);
	(* 19 *) Setdata("xp","black",20);
	(* 20 *) Setdata("xpp","red",21);
	(* 21 *) Rightrotate("xpp",1);      
	(* 22 *) X_ass_yleft("y","xpp",23);      (******* Right branch *******)
	(* 23 *) If_xdata("y","red",24,28);
	(* 24 *) Setdata("xp","black",25);
	(* 25 *) Setdata("y","black",26);
	(* 26 *) Setdata("xpp","red",27);
	(* 27 *) X_ass_y ("x","xpp",1);
	(* 28 *) X_ass_yleft("y","xp",29);
	(* 29 *) If_xeqy("x","y",30,34); 
	(* 30 *) X_ass_y ("x","xp",31);
	(* 31 *) Rightrotate("x",32);
	(* 32 *) X_ass_yup("xp","x",33);
	(* 33 *) X_ass_yup("xpp","xp",34);
	(* 34 *) Setdata("xp","black",35);
	(* 35 *) Setdata("xpp","red",36);
	(* 36 *) Leftrotate("xpp",1);      
	(* 37 *) Setdata("root","black",38);(*nastavit vse krome root na null*)
	(* 38 *) Exit
	];;

(********* Compile the program = create transducers *********)
let comp_rbt_reb_ins = compile_program rbt_reb_ins ["root";"x";"xp";"xpp";"y"] ["red";"black"];;

(********* Create timbuk alphabeth *********)
let alpha = create_alphabeth  ["root";"x";"xp";"xpp";"y"] ["red";"black"];;

(************************** some init automata ************************)

(********* Regular red-black trees ***********)
let init_rbt_reb_ins = automaton alpha "
	States qbot q1 qb qr qx qbx qrx qrootx qbrootx qnull qundef qacc
	Final States qacc
	Transitions 
	   bot0 -> qbot
	   bot2(qbot,qbot) -> qbot
	   bot2(qbot,qbot) -> q1

           black(q1,q1) -> qb

           xred(q1,q1) -> qx
           xblack(q1,q1) -> qx
           rootxred(q1,q1) -> qrootx
           rootxblack(q1,q1) -> qrootx

           red(qb,qb) -> qr
           red(qb,qbx) -> qrx
           red(qb,qx) -> qrx
           red(qbx,qb) -> qrx
           red(qx,qb) -> qrx
           
           black(qb,qb) -> qb
           black(qr,qb) -> qb
           black(qb,qr) -> qb
           black(qr,qr) -> qb
           black(qbx,qb) -> qbx
           black(qx,qb) -> qbx
           black(qb,qbx) -> qbx
           black(qb,qx) -> qbx
           black(qrx,qb) -> qbx
           black(qx,qb) -> qbx
           black(qr,qbx) -> qbx
           black(qr,qx) -> qbx
           black(qbx,qr) -> qbx
           black(qx,qr) -> qbx
           black(qb,qrx) -> qbx
           black(qb,qx) -> qbx
           black(qrx,qr) -> qbx
           black(qx,qr) -> qbx
           black(qr,qrx) -> qbx
           black(qr,qx) -> qbx

           rootblack(qbx,qb) -> qbrootx
           rootblack(qx,qb) -> qbrootx
           rootblack(qb,qbx) -> qbrootx
           rootblack(qb,qx) -> qbrootx
           rootblack(qrx,qb) -> qbrootx
           rootblack(qx,qb) -> qbrootx
           rootblack(qr,qbx) -> qbrootx
           rootblack(qr,qx) -> qbrootx
           rootblack(qbx,qr) -> qbrootx
           rootblack(qx,qr) -> qbrootx
           rootblack(qb,qrx) -> qbrootx
           rootblack(qb,qx) -> qbrootx
           rootblack(qrx,qr) -> qbrootx
           rootblack(qx,qr) -> qbrootx
           rootblack(qr,qrx) -> qbrootx
           rootblack(qr,qx) -> qbrootx

	   NULL(qrootx,qbot) -> qnull
	   NULL(qbrootx,qbot) -> qnull
	   xpxppyUNDEF(qnull,qbot) -> qundef
	   normal(qundef,qbot) -> qacc ";;
(*
(* RB-trees degenerated to the left branch only... *)
let init_rbt_reb_ins = automaton alpha "
	States qbot q1 qb qr qx qbx qrx qrootx qbrootx qnull qundef qacc
	Final States qacc
	Transitions 
	   bot0 -> qbot
	   bot2(qbot,qbot) -> qbot
	   bot2(qbot,qbot) -> q1

           black(q1,q1) -> qb

           xred(q1,q1) -> qx
           xblack(q1,q1) -> qx
           rootxred(q1,q1) -> qrootx
           rootxblack(q1,q1) -> qrootx

           red(qb,q1) -> qr
           red(qbx,q1) -> qrx
           red(qx,q1) -> qrx
           
           black(qb,q1) -> qb
           black(qr,q1) -> qb
           black(qbx,q1) -> qbx
           black(qx,q1) -> qbx
           black(qrx,q1) -> qbx

           rootblack(qbx,q1) -> qbrootx
           rootblack(qx,q1) -> qbrootx
           rootblack(qb,q1) -> qbrootx
           rootblack(qrx,q1) -> qbrootx
           rootblack(qr,q1) -> qbrootx

	   NULL(qrootx,qbot) -> qnull
	   NULL(qbrootx,qbot) -> qnull
	   xpxppyUNDEF(qnull,qbot) -> qundef
	   normal(qundef,qbot) -> qacc ";;
	
	*)
	   
(************ The set of bad states ****************)

(******* A trivial set of bad states ********)
let bad=automaton alpha "
	States 
	Final States 
	Transitions ";;

(* The input of the main procedure is a list of automata
   - the first is the init,
   - the others are empty. 
   
   This list can be created by function "create_init_conf" *)

let rec create_set_of_empty_automata number alpha=
    let empty = automaton alpha "
		States
		Final States
		Transitions " in 
	if number=0 then []
	else  empty:: (create_set_of_empty_automata (number-1) alpha);;

let create_init_conf init_aut0 number alpha=
	init_aut0::create_set_of_empty_automata (number-1) alpha;;

let init_set=create_init_conf init_rbt_reb_ins 39 alpha;;

