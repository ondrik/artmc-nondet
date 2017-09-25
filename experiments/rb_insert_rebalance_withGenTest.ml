open Taml;;
open Input;;

(********* Red-Black Tree Rebalancing after an Insert - using parent pointers (no stack) ********)
(********* black leaves modelling null are left out *************)

let rbt_reb_ins = [
   (************ Constructing random r/b trees: in this phase, we use xp as a brother, not parent, pointer *******)
   (************ If a node has just one son, then this son is a red leaf *******)
   (************)
	(******** choose whether to add a new node or not ******)
        (*   0 *) If_nondet(1,39); 
        (******** start going down from the root in a random way ******)
	(*   1 *) X_ass_y("x","root",2);
        (******** choose whether to add a node into the left or right subtree *******)
	(*   2 *) X_ass_y("xp","x",3);
        (*   3 *) If_nondet(4,27);
	(******** adding a new node into the left subtree ******)
	(*   4 *) X_ass_yleft("x","xp",5);
	(*   5 *) X_ass_yleft("y","x",6);
	(*   6 *) If_xnull("y",7,26); 
        (******** x->left==null, hence x is a sentinel, and we will probably add a new node to the left of xp ******)
	(*   7 *) If_xdata("xp","red",8,19);
        (******** we are below a red node, test whether it is not without a brother,
                  i.e. test whether xpp, the brother, is a sentinel ******)
	(*   8 *) X_ass_yleft("y","xpp",9);
	(*   9 *) If_xnull("y",0,10); 
        (******** add 2 black nodes below the red node xp with a brother: both of its sons are sentinels, 
                  these sentinels become regular nodes, 4 new sentinels are added ******)
	(*  10 *) X_ass_yright("y","xp",11);
        (*  11 *) New_xleft("x","black",12);
	(*  12 *) New_xright("x","black",13);
        (*  13 *) New_xleft("y","black",14);
	(*  14 *) New_xright("y","black",15);
        (******** clean the temp variables and start again *******)
	(*  15 *) X_ass_null("x",16); 
	(*  16 *) X_ass_null("y",17); 
	(*  17 *) X_ass_null("xp",18); 
	(*  18 *) X_ass_null("xpp",0); 
        (******** for a black node xp with a sentinel to the left, test what is to the right *******)
	(*  19 *) X_ass_yright("xpp","xp",20);
	(*  20 *) X_ass_yleft("y","xpp",21);
	(*  21 *) If_xnull("y",22,23); 
        (******* both sons of xp are sentinels, choose whether to add a single red node or two black ones *******)
	(*  22 *) If_nondet(23,10);
        (******* adding a single red node, the other may be added in another descent,
                 i.e. we recolor x to red and add 2 sentinels below it ******)
	(*  23 *) Setdata("x","red",24);
        (*  24 *) New_xleft("x","black",25);
	(*  25 *) New_xright("x","black",15);
        (******** continue going down: the new brother is to the right *******)
        (*  26 *) X_ass_yright("xpp","xp",2);
	(******** adding a new node into the right subtree ******)
	(*  27 *) X_ass_yright("x","xp",28);
	(*  28 *) X_ass_yleft("y","x",29);
	(*  29 *) If_xnull("y",30,38);
        (******** x->left==null, hence x is a sentinel, and we will probably add a new node to the right of xp ******)
	(*  30 *) If_xdata("xp","red",31,34);
        (******** we are below a red node, test whether it is not without a brother,
                  i.e. test whether xpp, the brother, is a sentinel ******)
	(*  31 *) X_ass_yleft("y","xpp",32);
	(*  32 *) If_xnull("y",0,33); 
        (******** add 2 black nodes below the red node xp with a brother: both of its sons are sentinels, 
                  these sentinels become regular nodes, 4 new sentinels are added ******)
	(*  33 *) X_ass_yleft("y","xp",11);
        (******** for a black node xp with a sentinel to the right, test what is to the left *******)
	(*  34 *) X_ass_yleft("xpp","xp",35);
	(*  35 *) X_ass_yleft("y","xpp",36);
	(*  36 *) If_xnull("y",37,23); 
        (******* both sons of xp are sentinels, choose whether to add a single red node or two black ones *******)
	(*  37 *) If_nondet(23,33);
        (******** continue going down: the new brother is to the left *******)
        (*  38 *) X_ass_yleft("xpp","xp",2);
   (************ add a leaf to be considered newly added and mark it with x *******)
   (************)
	(*  39 *) X_ass_y("x","root",40);
        (******** choose whether to go into the left or right subtree *******)
        (*  40 *) If_nondet(41,47);
	(******* going left ******)
	(*  41 *) X_ass_yleft("y","x",42);
	(*  42 *) If_xnull("y",44,43); 
        (*  43 *) X_ass_y ("x","y",40);
        (******* recolor the sentinel to a new red node from where to start rebalancing and add two sentinels *)
	(*  44 *) Setdata("x","red",45);
        (*  45 *) New_xleft("x","black",46);
        (*  46 *) New_xright("x","black",48);
	(******* going right ******)
	(*  47 *) X_ass_yright("y","x",42);
   (************ Behave as though x is a newly added node, already marked red -- start re-balancing *******)
   (************)

	(* 48 *) Setdata("x","red",49); 	(*dummy line*)
	(* 49 *) If_xeqy("x","root",89,50); 
	(* 50 *) X_ass_yup("xp","x",51);
	(* 51 *) If_xdata("xp","red",52,89);
	(* 52 *) X_ass_yup("xpp","xp",53);
	(* 53 *) X_ass_yleft("y","xpp",54);
	(* 54 *) If_xeqy("xp","y",55,72); 
	(* 55 *) X_ass_yright("y","xpp",56);      (******* Left branch *******)
	(* 56 *) If_xdata("y","red",57,61);
	(* 57 *) Setdata("xp","black",58);
	(* 58 *) Setdata("y","black",59);
	(* 59 *) Setdata("xpp","red",60);
	(* 60 *) X_ass_y ("x","xpp",49);
	(* 61 *) X_ass_yright("y","xp",62);
	(* 62 *) If_xeqy("x","y",63,67); 
	(* 63 *) X_ass_y ("x","xp",64);
	(* 64 *) Leftrotate("x",65);
	(* 65 *) X_ass_yup("xp","x",66);
	(* 66 *) X_ass_yup("xpp","xp",67);
	(* 67 *) Setdata("xp","black",68);
	(* 68 *) Setdata("xpp","red",69);

	(* 69 *) If_xeqy("xpp","root",70,71); 
	(* 70 *) X_ass_y ("root","xp",71);

	(* 71 *) Rightrotate("xpp",49);      
	(* 72 *) X_ass_yleft("y","xpp",74);      (******* Right branch *******)
	(* 73 *) If_xdata("y","red",74,78);
	(* 74 *) Setdata("xp","black",75);
	(* 75 *) Setdata("y","black",76);
	(* 76 *) Setdata("xpp","red",77);
	(* 77 *) X_ass_y ("x","xpp",49);
	(* 78 *) X_ass_yleft("y","xp",79);
	(* 79 *) If_xeqy("x","y",80,84); 
	(* 80 *) X_ass_y ("x","xp",81);
	(* 81 *) Rightrotate("x",82);
	(* 82 *) X_ass_yup("xp","x",83);
	(* 83 *) X_ass_yup("xpp","xp",84);
	(* 84 *) Setdata("xp","black",85);
	(* 85 *) Setdata("xpp","red",86);

	(* 86 *) If_xeqy("xpp","root",87,88); 
	(* 87 *) X_ass_y ("root","xp", 88);

	(* 88 *) Leftrotate("xpp",49);      
	(* 89 *) Setdata("root","black",90);(*nastavit vse krome root na null*)

   (************* Set all temporary variables to null *******)
   (*************)
        (*  90 *) X_ass_null("x",91);
        (*  91 *) X_ass_null("y",92);
        (*  92 *) X_ass_null("xp",93);
        (*  93 *) X_ass_null("xpp",94);
   (************ Test that there are no two consecutive red nodes in a random walk down the tree *******)
   (************ Test also that if a node has just a single son, then the son is a red leaf *******)
   (************)
	(*  94 *) X_ass_y ("x","root",95);
        (******** choose whether to go into the left or right subtree *******)
        (*  95 *) If_nondet(96,110);
	(******** going left ******)
	(*  96 *) X_ass_yleft("y","x",97);
	(*  97 *) If_xnull("y",98,105); 
        (******** test that the right son is either a red leaf or null *****)
	(*  98 *) X_ass_yright("y","x",99);
        (*  99 *) If_xnull("y",113,100);
        (* 100 *) If_xdata("y","red",101,107);
	(* 101 *) X_ass_yleft("x","y",102);
        (* 102 *) If_xnull("x",103,107); 
	(* 103 *) X_ass_yright("x","y",104);
        (* 104 *) If_xnull("x",113,107); 
        (******* test that no two successive elements are red *****)
        (* 105 *) If_xdata("x","red",106,109);
        (* 106 *) If_xdata("y","red",107,109);
        (******** !!!!!!!!!!!! cause an error !!!!!!!!!! *******)
	(* 107 *) X_ass_null("x",108);
	(* 108 *) X_ass_yleft("y","x",108);
        (******** continue the descent *******)
        (* 109 *) X_ass_y ("x","y",95);
	(******** going right ******)
	(* 110 *) X_ass_yright("y","x",111);
	(* 111 *) If_xnull("y",112,105); 
        (******* test that the left son is either a red leaf or null *****)
	(* 112 *) X_ass_yleft("y","x",99);
   (************ We are done *******)
   (************)
	(* 113 *) Exit
	];;

(********* Compile the program = create transducers *********)
let comp_rbt_reb_ins = compile_program rbt_reb_ins ["root";"x";"xp";"xpp";"y"] ["red";"black"];;

(********* Create a timbuk alphabeth *********)
let alpha = create_alphabeth  ["root";"x";"xp";"xpp";"y"] ["red";"black"];;

(************************** some init automata ************************)

(********* Just a single red-black tree: a basis for generating RB trees ***********)
let init_rbt_reb_ins_oneNodeOnly = automaton alpha "
	States qbot q1 q2 qroot qnull qundef qacc
	Final States qacc
	Transitions 
	   bot0 -> qbot
	   bot2(qbot,qbot) -> qbot
	   bot2(qbot,qbot) -> q1

           black(q1,q1) -> q2

           rootblack(q2,q2) -> qroot

	   xxpxppyNULL(qroot,qbot) -> qnull
	   UNDEF(qnull,qbot) -> qundef
	   normal(qundef,qbot) -> qacc ";;

(********* Regular red-black trees: the requirement that if a node has a single son,
           it's a red leaf not enforced!!! ***********)
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

(********* Regular red-black trees:the requirement that if a node has a single son, 
           it's a red leaf not enforced!!! ***********)
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

(* let init_set=create_init_conf init_rbt_reb_ins_oneNodeOnly 110 alpha;; *)


