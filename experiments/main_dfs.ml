(*
set makeprg=cd\ ~/ta/pointers/ptrs;make
*)
open Taml;;
open Main_loop;;
open Predicate_generation;;
open Dfs;;
open Colapsing_v3;;


let spur = automaton alpha
"States q8:0 q7:0 q6:0 q5:0 q4:0 q3:0 q2:0 q1:0 q0:0 

Final States q8 

Transitions 
bot0 -> q0
bot2(q0,q0) -> q0
bot2(q0,q0) -> q7
yunmarked(q7,q7) -> q1
unmarked(q7,q7) -> q1
yunmarked(q7,q7) -> q7
unmarked(q7,q7) -> q7
yunmarked(q1,q7) -> q2
unmarked(q1,q7) -> q2
yunmarked(q2,q7) -> q3
unmarked(q2,q7) -> q3
xyunmarked(q7,q3) -> q4
xunmarked(q7,q3) -> q4
rootxyunmarked(q7,q3) -> q4
rootxunmarked(q7,q3) -> q4
yunmarked(q4,q7) -> q4
unmarked(q4,q7) -> q4
rootyunmarked(q4,q7) -> q4
rootunmarked(q4,q7) -> q4
yNULL(q4,q7) -> q5
NULL(q4,q7) -> q5
yUNDEF(q5,q7) -> q6
UNDEF(q5,q7) -> q6
normal(q6,q7) -> q8
";;

let structure = automaton alpha 
"
States q4:0 q3:0 q2:0 q1:0 q0:0 

Final States q4

Transitions 
bot0 -> q0
bot2(q0,q0) -> q0
marked(q0,q0) -> q1
xmarked(q0,q0) -> q1
ymarked(q0,q0) -> q1
xymarked(q0,q0) -> q1
rootmarked(q0,q0) -> q1
rootxmarked(q0,q0) -> q1
rootymarked(q0,q0) -> q1
rootxymarked(q0,q0) -> q1
unmarked(q0,q0) -> q1
xunmarked(q0,q0) -> q1
yunmarked(q0,q0) -> q1
xyunmarked(q0,q0) -> q1
rootunmarked(q0,q0) -> q1
rootxunmarked(q0,q0) -> q1
rootyunmarked(q0,q0) -> q1
rootxyunmarked(q0,q0) -> q1
marked(q0,q1) -> q1
xmarked(q0,q1) -> q1
ymarked(q0,q1) -> q1
xymarked(q0,q1) -> q1
rootmarked(q0,q1) -> q1
rootxmarked(q0,q1) -> q1
rootymarked(q0,q1) -> q1
rootxymarked(q0,q1) -> q1
unmarked(q0,q1) -> q1
xunmarked(q0,q1) -> q1
yunmarked(q0,q1) -> q1
xyunmarked(q0,q1) -> q1
rootunmarked(q0,q1) -> q1
rootxunmarked(q0,q1) -> q1
rootyunmarked(q0,q1) -> q1
rootxyunmarked(q0,q1) -> q1
marked(q1,q0) -> q1
xmarked(q1,q0) -> q1
ymarked(q1,q0) -> q1
xymarked(q1,q0) -> q1
rootmarked(q1,q0) -> q1
rootxmarked(q1,q0) -> q1
rootymarked(q1,q0) -> q1
rootxymarked(q1,q0) -> q1
unmarked(q1,q0) -> q1
xunmarked(q1,q0) -> q1
yunmarked(q1,q0) -> q1
xyunmarked(q1,q0) -> q1
rootunmarked(q1,q0) -> q1
rootxunmarked(q1,q0) -> q1
rootyunmarked(q1,q0) -> q1
rootxyunmarked(q1,q0) -> q1
marked(q1,q1) -> q1
xmarked(q1,q1) -> q1
ymarked(q1,q1) -> q1
xymarked(q1,q1) -> q1
rootmarked(q1,q1) -> q1
rootxmarked(q1,q1) -> q1
rootymarked(q1,q1) -> q1
rootxymarked(q1,q1) -> q1
unmarked(q1,q1) -> q1
xunmarked(q1,q1) -> q1
yunmarked(q1,q1) -> q1
xyunmarked(q1,q1) -> q1
rootunmarked(q1,q1) -> q1
rootxunmarked(q1,q1) -> q1
rootyunmarked(q1,q1) -> q1
rootxyunmarked(q1,q1) -> q1
NULL(q1,q0) -> q2
NULL(q0,q0) -> q2
xNULL(q1,q0) -> q2
xNULL(q0,q0) -> q2
yNULL(q1,q0) -> q2
yNULL(q0,q0) -> q2
xyNULL(q1,q0) -> q2
xyNULL(q0,q0) -> q2
rootNULL(q1,q0) -> q2
rootNULL(q0,q0) -> q2
rootxNULL(q1,q0) -> q2
rootxNULL(q0,q0) -> q2
rootyNULL(q1,q0) -> q2
rootyNULL(q0,q0) -> q2
rootxyNULL(q1,q0) -> q2
rootxyNULL(q0,q0) -> q2
UNDEF(q2,q0) -> q3
xUNDEF(q2,q0) -> q3
yUNDEF(q2,q0) -> q3
xyUNDEF(q2,q0) -> q3
rootUNDEF(q2,q0) -> q3
rootxUNDEF(q2,q0) -> q3
rootyUNDEF(q2,q0) -> q3
rootxyUNDEF(q2,q0) -> q3
normal(q3,q0) -> q4
";;

let pred_x=create_predicate_automaton "x" ["root";"x";"y"]["marked";"unmarked"];;
let pred_y=create_predicate_automaton "y" ["root";"x";"y"]["marked";"unmarked"];;
let pred_root=create_predicate_automaton "root" ["root";"x";"y"]["marked";"unmarked"];;

(*print_string "1\n";;*)

let init_preds =[("px",pred_x);("py",pred_y)];;
(*	let alpha = Taml.Automaton.get_alphabet (List.nth init_set 0) in*)
(*	write_alphabet_to_files alpha;*)
(*	match which_predicates_to_add with*)
(*	Structure -> [("px",pred_x);("py",pred_y);("struct",structure)]*)
(*	| No -> [("px",pred_x);("py",pred_y)]*)
(*	Structure -> [("px",pred_x);("py",pred_y);("struct",structure);("proot",pred_root)]*)
(*	| No -> [("px",pred_x);("py",pred_y);("proot",pred_root)]*)
(*;;*)

let main () =
	run_main_loop_predabs 
   ~abstr_restriction:Unrestricted
   "DFT" 
   (Array.of_list comp_dfs)
   0 
   init_dfs   
   init_preds (Some (bad,None))
;;



main()

