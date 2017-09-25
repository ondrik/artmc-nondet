open Taml;;
open Input;;


(********* Red-Black Tree Rebalancing after an Insert - using parent pointers (no stack) ********)

let rbt_reb_ins = [
	(*  0 *) Setdata("x","red",1);
	(*  1 *) If_xeqy("x","root",41,2); 
	(*  2 *) X_ass_yup("xp","x",3);
	(*  3 *) If_xdata("xp","red",4,41);
	(*  4 *) X_ass_yup("xpp","xp",5);
	(*  5 *) X_ass_yleft("y","xpp",6);
	(*  6 *) If_xeqy("xp","y",7,24); 
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

	(* 21 *) If_xeqy("xpp","root",22,23); 
	(* 22 *) X_ass_y ("root","xp",23);

	(* 23 *) Rightrotate("xpp",1);      
	(* 24 *) X_ass_yleft("y","xpp",26);      (******* Right branch *******)
	(* 25 *) If_xdata("y","red",26,30);
	(* 26 *) Setdata("xp","black",27);
	(* 27 *) Setdata("y","black",28);
	(* 28 *) Setdata("xpp","red",29);
	(* 29 *) X_ass_y ("x","xpp",1);
	(* 30 *) X_ass_yleft("y","xp",31);
	(* 31 *) If_xeqy("x","y",32,36); 
	(* 32 *) X_ass_y ("x","xp",33);
	(* 33 *) Rightrotate("x",34);
	(* 34 *) X_ass_yup("xp","x",35);
	(* 35 *) X_ass_yup("xpp","xp",36);
	(* 36 *) Setdata("xp","black",37);
	(* 37 *) Setdata("xpp","red",38);

	(* 38 *) If_xeqy("xpp","root",39,40); 
	(* 39 *) X_ass_y ("root","xp",40);

	(* 40 *) Leftrotate("xpp",1);      
	(* 41 *) Setdata("root","black",42);(*nastavit vse krome root na null*)
   (* 42 *) X_ass_null("x",43);
   (* 43 *) X_ass_null("y",44);
   (* 44 *) X_ass_null("xp",45);
   (* 45 *) X_ass_null("xpp",46);
	(* 46 *) Exit
	];;

(********* Compile the program = create transducers *********)
let comp_rbt_reb_ins = compile_program rbt_reb_ins ["root";"x";"xp";"xpp";"y"] ["red";"black"];;

(********* Create timbuk alphabeth *********)
let alpha = create_alphabeth  ["root";"x";"xp";"xpp";"y"] ["red";"black"];;

(************************** some init automata ************************)

(********* Regular red-black trees ***********)
let init_rbt_reb_ins = automaton alpha "
	States qbot q1 qb qr qx qbx qrx qrootx qbrootx qnull qundef qacc qsink
	Final States qacc
	Transitions 
	   bot0 -> qbot
	   bot2(qbot,qbot) -> qbot
	   bot2(qbot,qbot) -> q1

           black(q1,q1) -> qsink

           xred(qsink,qsink) -> qx
           xblack(qsink,qsink) -> qx
           rootxred(qsink,qsink) -> qrootx
           rootxblack(qsink,qsink) -> qrootx

           red(qb,qb) -> qr
           red(qsink,qb) -> qr
           red(qb,qsink) -> qr
           red(qsink,qsink) -> qr
           red(qb,qbx) -> qrx
           red(qsink,qbx) -> qrx
           red(qb,qx) -> qrx
           red(qsink,qx) -> qrx
           red(qbx,qb) -> qrx
           red(qbx,qsink) -> qrx
           red(qx,qb) -> qrx
           red(qx,qsink) -> qrx
           
           black(qb,qb) -> qb
           black(qsink,qb) -> qb
           black(qb,qsink) -> qb
           black(qsink,qsink) -> qb
           black(qr,qb) -> qb
           black(qr,qsink) -> qb
           black(qb,qr) -> qb
           black(qsink,qr) -> qb
           black(qr,qr) -> qb
           black(qbx,qb) -> qbx
           black(qbx,qsink) -> qbx
           black(qx,qb) -> qbx
           black(qx,qsink) -> qbx
           black(qb,qbx) -> qbx
           black(qsink,qbx) -> qbx
           black(qb,qx) -> qbx
           black(qsink,qx) -> qbx
           black(qrx,qb) -> qbx
           black(qrx,qsink) -> qbx
           black(qx,qb) -> qbx
           black(qx,qsink) -> qbx
           black(qr,qbx) -> qbx
           black(qr,qx) -> qbx
           black(qbx,qr) -> qbx
           black(qx,qr) -> qbx
           black(qb,qrx) -> qbx
           black(qsink,qrx) -> qbx
           black(qsink,qx) -> qbx
           black(qrx,qr) -> qbx
           black(qx,qr) -> qbx
           black(qr,qrx) -> qbx
           black(qr,qx) -> qbx

           rootblack(qbx,qb) -> qbrootx
           rootblack(qbx,qsink) -> qbrootx
           rootblack(qx,qb) -> qbrootx
           rootblack(qx,qsink) -> qbrootx
           rootblack(qb,qbx) -> qbrootx
           rootblack(qsink,qbx) -> qbrootx
           rootblack(qb,qx) -> qbrootx
           rootblack(qsink,qx) -> qbrootx
           rootblack(qrx,qb) -> qbrootx
           rootblack(qrx,qsink) -> qbrootx
           rootblack(qx,qb) -> qbrootx
           rootblack(qx,qsink) -> qbrootx
           rootblack(qr,qbx) -> qbrootx
           rootblack(qr,qx) -> qbrootx
           rootblack(qbx,qr) -> qbrootx
           rootblack(qx,qr) -> qbrootx
           rootblack(qb,qrx) -> qbrootx
           rootblack(qsink,qrx) -> qbrootx
           rootblack(qb,qx) -> qbrootx
           rootblack(qsink,qx) -> qbrootx
           rootblack(qrx,qr) -> qbrootx
           rootblack(qx,qr) -> qbrootx
           rootblack(qr,qrx) -> qbrootx
           rootblack(qr,qx) -> qbrootx

	   NULL(qrootx,qbot) -> qnull
	   NULL(qbrootx,qbot) -> qnull
	   xpxppyUNDEF(qnull,qbot) -> qundef
	   normal(qundef,qbot) -> qacc ";;

(********* Regular red-black trees ***********)
let all_rb_trees = automaton alpha "
	States qbot q1 qb qr  qroot qbroot qnull qundef qacc qsink
	Final States qacc
	Transitions 
	   bot0 -> qbot
	   bot2(qbot,qbot) -> qbot
	   bot2(qbot,qbot) -> q1

           black(q1,q1) -> qsink

           red(qb,qb) -> qr
           red(qsink,qb) -> qr
           red(qb,qsink) -> qr
           red(qsink,qsink) -> qr
           
           black(qb,qb) -> qb
           black(qsink,qb) -> qb
           black(qb,qsink) -> qb
           black(qsink,qsink) -> qb
           black(qr,qb) -> qb
           black(qr,qsink) -> qb
           black(qb,qr) -> qb
           black(qsink,qr) -> qb
           black(qr,qr) -> qb

           rootblack(qb,qb) -> qbroot
           rootblack(qsink,qb) -> qbroot
           rootblack(qb,qsink) -> qbroot
           rootblack(qsink,qsink) -> qbroot
           rootblack(qr,qb) -> qbroot
           rootblack(qb,qr) -> qbroot
           rootblack(qr,qr) -> qbroot
           rootblack(qsink,qr) -> qbroot
           rootblack(qr,qsink) -> qbroot

	   xxpxppyNULL(qbroot,qbot) -> qnull
	   UNDEF(qnull,qbot) -> qundef
	   normal(qundef,qbot) -> qacc ";;

let get_all_nonrb_trees _ =
   print_string "reading bad configurations ... ";flush stdout;
   (*let all_nonrbs =*)
   (*        Minimize_abstr_fin_length.minimize(Automaton.determinise(Automaton.simplify(Automaton.inverse( *)
   (*                Automaton.simplify all_rb_trees))));;*)
   (*Automaton.print all_nonrbs;;*)
   (*Main_loop.save_aut "all_nonrbs" "all_nonrbs" all_nonrbs;;*)
   let all_nonrb_trees = List.hd (Mess.aut_list_from_file "all_nonrbs.spec") in
   print_endline "done";flush stdout;
   all_nonrb_trees


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

