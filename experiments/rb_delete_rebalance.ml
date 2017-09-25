open Taml;;
open Input;;

(********* Red-Black Tree Rebalancing after a deletion - using parent pointers (no stack) ********)

(****** We use a pre-defined set of initial RB trees and a set of all (good) RB trees: not a constructor/tester ********)

(****** The RB conditions are abstracted: no testing of balancedness, each leaf must be black (but we do not ensure
        that a node can have a single (non-sentinel) son only if it is a (non-sentinel) red leaf. Consequently,
        it seems (not 100% checked) that a black sentinel can become a non-sentinel node after a rotation with no
        sentinel below it... **********)

let rbt_reb_del = [
	(*  0 *) If_xeqy("x","root",73,1); 
	(*  1 *) If_xdata("x","red",73,2);
   (********************************)
   (******* start rebalancing ******)
	(*  2 *) X_ass_yup("xp","x",3);
	(*  3 *) X_ass_yleft("w","xp",4);
	(*  4 *) If_xeqy("x","w",5,39); 
   (******************************)
   (******* the left branch ******)
	(*  5 *) X_ass_yright("w","xp",6);
	(*  6 *) If_xdata("w","red",7,13);
        (******* case 1 ******)
	(*  7 *) Setdata("w","black",8);
	(*  8 *) Setdata("xp","red",9);
	(*  9 *) If_xeqy("root","xp",10,11);    (* take care of the possible rotation of the root *)
	(* 10 *) X_ass_yright("root","xp",11);
        (* 11 *) Leftrotate("xp",12);
	(* 12 *) X_ass_yright("w","xp",13);
        (******* testing for case 2 ******)
	(* 13 *) X_ass_yleft("y","w",14);
	(* 14 *) If_xdata("y","black",15,19);
	(* 15 *) X_ass_yright("y","w",16);
	(* 16 *) If_xdata("y","black",17,29);
        (******* case 2 ******)
	(* 17 *) Setdata("w","red",18);
	(* 18 *) X_ass_yup("x","x",0);
        (******* testing for case 3 ******)
	(* 19 *) X_ass_yright("y","w",20);
	(* 20 *) If_xdata("y","black",21,29);
        (******* case 3 ******)
	(* 21 *) X_ass_yleft("y","w",22);
	(* 22 *) Setdata("y","black",23);
	(* 23 *) Setdata("w","red",24);
	(* 24 *) If_xeqy("root","w",25,26);    (* take care of the possible rotation of the root *)
	(* 25 *) X_ass_yleft("root","w",26);
	(* 26 *) Rightrotate("w",27);
	(* 27 *) X_ass_yup("xp","x",28);
	(* 28 *) X_ass_yright("w","xp",29);
        (******* case 4 ******)
	(* 29 *) If_xdata("xp","black",30,31);
	(* 30 *) Setdata("w","black",32);
	(* 31 *) Setdata("w","red",32);
	(* 32 *) Setdata("xp","black",33);
	(* 33 *) X_ass_yright("y","w",34);
	(* 34 *) Setdata("y","black",35);
	(* 35 *) If_xeqy("root","xp",36,37);    (* take care of the possible rotation of the root *)
	(* 36 *) X_ass_yright("root","xp",37);
	(* 37 *) Leftrotate("xp",38);
	(* 38 *) X_ass_y("x","root",0);
   (******************************)
   (******* the right branch ******)
	(* 39 *) X_ass_yleft("w","xp",40);
	(* 40 *) If_xdata("w","red",41,47);
        (******* case 1 ******)
	(* 41 *) Setdata("w","black",42);
	(* 42 *) Setdata("xp","red",43);
	(* 43 *) If_xeqy("root","xp",44,45);    (* take care of the possible rotation of the root *)
	(* 44 *) X_ass_yleft("root","xp",45);
        (* 45 *) Rightrotate("xp",46);
	(* 46 *) X_ass_yleft("w","xp",47);
        (******* testing for case 2 ******)
	(* 47 *) X_ass_yright("y","w",48);
	(* 48 *) If_xdata("y","black",49,53);
	(* 49 *) X_ass_yleft("y","w",50);
	(* 50 *) If_xdata("y","black",51,63);
        (******* case 2 ******)
	(* 51 *) Setdata("w","red",52);
	(* 52 *) X_ass_yup("x","x",0);
        (******* testing for case 3 ******)
	(* 53 *) X_ass_yleft("y","w",54);
	(* 54 *) If_xdata("y","black",55,63);
        (******* case 3 ******)
	(* 55 *) X_ass_yright("y","w",56);
	(* 56 *) Setdata("y","black",57);
	(* 57 *) Setdata("w","red",58);
	(* 58 *) If_xeqy("root","w",59,60);    (* take care of the possible rotation of the root *)
	(* 59 *) X_ass_yright("root","w",60);
	(* 60 *) Leftrotate("w",61);
	(* 61 *) X_ass_yup("xp","x",62);
	(* 62 *) X_ass_yleft("w","xp",63);
        (******* case 4 ******)
	(* 63 *) If_xdata("xp","black",64,65);
	(* 64 *) Setdata("w","black",66);
	(* 65 *) Setdata("w","red",66);
	(* 66 *) Setdata("xp","black",67);
	(* 67 *) X_ass_yleft("y","w",68);
	(* 68 *) Setdata("y","black",69);
	(* 69 *) If_xeqy("root","xp",70,71);    (* take care of the possible rotation of the root *)
	(* 70 *) X_ass_yleft("root","xp",71);
	(* 71 *) Rightrotate("xp",72);
	(* 72 *) X_ass_y("x","root",0);
   (**********************************)
   (******* rebalancing is over ******)
	(* 73 *) Setdata("x","black",74);
   (**********************************)
   (******* clean all ******)
        (* 74 *) X_ass_null("x",75);
        (* 75 *) X_ass_null("y",76);
        (* 76 *) X_ass_null("xp",77);
        (* 77 *) X_ass_null("w",78);
	(* 78 *) Exit
	];;

(********* Compile the program = create transducers *********)
let comp_rbt_reb_del = compile_program rbt_reb_del ["root";"x";"xp";"y";"w"] ["red";"black"];;

(********* Create timbuk alphabeth *********)
let alpha = create_alphabeth  ["root";"x";"xp";"y";"w"] ["red";"black"];;

(********* Initial red-black trees (the regular overapproximation described above) ***********)

let init_rbt_reb_del = automaton alpha "
	States qbot q1 qb qr qrNS qrS qx qbx qrx qrootx qbrootx qnull qundef qacc qsink
	Final States qacc
	Transitions 
	   bot0 -> qbot
	   bot2(qbot,qbot) -> qbot
	   bot2(qbot,qbot) -> q1

           black(q1,q1) -> qsink

           xblack(q1,q1) -> qx
           xblack(qsink,qsink) -> qx
           xblack(qb,qb) -> qx
           xblack(qr,qsink) -> qx
           xblack(qsink,qr) -> qx
           xblack(qr,qr) -> qx
           xblack(qr,qb) -> qx
           xblack(qb,qr) -> qx

           black(qx,qb) -> qbx
           black(qb,qx) -> qbx
           black(qx,qrNS) -> qbx
           black(qrNS,qx) -> qbx

           red(qx,qb) -> qrx
           red(qb,qx) -> qrx

           rootblack(qx,qb) -> qrootx
           rootblack(qb,qx) -> qrootx
           rootblack(qx,qrNS) -> qrootx
           rootblack(qrNS,qx) -> qrootx
           rootred(qx,qb) -> qrootx
           rootred(qb,qx) -> qrootx

           red(qb,qb) -> qr
           red(qb,qb) -> qrNS
           red(qsink,qsink) -> qr
           red(qsink,qsink) -> qrS

           red(qb,qbx) -> qrx
           red(qbx,qb) -> qrx
           
           black(qb,qb) -> qb
           black(qsink,qsink) -> qb
           black(qrNS,qb) -> qb
           black(qb,qrNS) -> qb
           black(qrS,qsink) -> qb
           black(qsink,qrS) -> qb
           black(qrS,qrS) -> qb
           black(qrNS,qrNS) -> qb

           black(qbx,qb) -> qbx
           black(qrx,qb) -> qbx
           black(qb,qbx) -> qbx
           black(qb,qrx) -> qbx
           black(qrNS,qbx) -> qbx
           black(qrNS,qrx) -> qbx
           black(qbx,qrNS) -> qbx
           black(qrx,qrNS) -> qbx

           rootblack(qbx,qb) -> qbrootx
           rootblack(qrx,qb) -> qbrootx
           rootblack(qb,qbx) -> qbrootx
           rootblack(qb,qrx) -> qbrootx
           rootblack(qrNS,qbx) -> qbrootx
           rootblack(qrNS,qrx) -> qbrootx
           rootblack(qbx,qrNS) -> qbrootx
           rootblack(qrx,qrNS) -> qbrootx

	   xpywNULL(qrootx,qbot) -> qnull
	   xpywNULL(qbrootx,qbot) -> qnull
	   UNDEF(qnull,qbot) -> qundef
	   normal(qundef,qbot) -> qacc ";;

(********* Good red-black trees (the regular overapproximation described above) ***********)
(********* All pointers apart from the root point to NULL *********)

let all_rb_trees_del = automaton alpha "
	States qbot q1 qb qr  qroot qbroot qnull qundef qacc qsink
	Final States qacc
	Transitions 
	   bot0 -> qbot
	   bot2(qbot,qbot) -> qbot
	   bot2(qbot,qbot) -> q1

           black(q1,q1) -> qsink

           red(qb,qb) -> qr
           red(qb,qsink) -> qr
           red(qsink,qb) -> qr
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
           rootblack(qb,qsink) -> qbroot
           rootblack(qsink,qb) -> qbroot
           rootblack(qsink,qsink) -> qbroot
           rootblack(qr,qb) -> qbroot
           rootblack(qr,qsink) -> qbroot
           rootblack(qb,qr) -> qbroot
           rootblack(qsink,qr) -> qbroot
           rootblack(qr,qr) -> qbroot

	   xxpywNULL(qbroot,qbot) -> qnull
	   UNDEF(qnull,qbot) -> qundef
	   normal(qundef,qbot) -> qacc ";;

let inverse a=  Main_loop_utility.inverse_deterministic (Interim.simplify_taml (determinise a));;

print_endline "inverse ...";flush_all ();;
let all_nonrbs_del = (Interim.simplify_taml (inverse all_rb_trees_del));;
(*print_endline "fn ...";flush_all ();;*)
(*let all_nonrbs_del_check =  (Taml.inverse (Taml.simplify(all_rb_trees_del)));;*)
(*print_endline "bz ...";flush_all ();;*)
(*if not (Heuristics.are_equiv all_nonrbs_del all_nonrbs_del_check) then failwith"problema";;*)
print_endline "done";flush_all ();;

let get_all_nonrb_trees_del _ = all_nonrbs_del;;

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

