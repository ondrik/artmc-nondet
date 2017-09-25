open Rb_delete_rebalance;;
open Taml;;
open Main_loop;;
open Predicate_generation;;
open Colapsing_v3;;

let pred_x=create_predicate_automaton "x" ["root";"x";"xp";"y";"w"] ["red";"black"];; 
let pred_xp=create_predicate_automaton "xp" ["root";"x";"xp";"y";"w"] ["red";"black"];; 
let pred_y=create_predicate_automaton "y" ["root";"x";"xp";"y";"w"] ["red";"black"];; 
let pred_w=create_predicate_automaton "w" ["root";"x";"xp";"y";"w"] ["red";"black"];; 
let pred_root=create_predicate_automaton "root" ["root";"x";"xp";"y";"w"] ["red";"black"];; 

let pred_red=create_data_predicate_automaton "red" ["root";"x";"xp";"y";"w"] ["red";"black"];; 
(* let pred_black=create_data_predicate_automaton "black" ["root";"x";"xp";"y";"w"] ["red";"black"];; *)

(* let bad_pred =  Minimize_abstr_fin_length.minimize (Automaton.simplify (Automaton.determinise all_nonrbs_del));; *)
(* let ini_pred =  Minimize_abstr_fin_length.minimize (Automaton.simplify (Automaton.determinise init_rbt_reb_del));; *)

let init_preds =  
(*  [("px",pred_x);("pxp",pred_xp);("py",pred_y);("pw",pred_w);("root",pred_root)]
 *  ;;   *)
  [("px",pred_x);("pxp",pred_xp);("py",pred_y);("pw",pred_w);("root",pred_root);("pred",pred_red)] ;;
(*  [("px",pred_x);("pxp",pred_xp);("py",pred_y);("pw",pred_w);("root",pred_root);("pred",pred_red);("pblk",pred_black)] ;; *)
(*  [("px",pred_x);("pxp",pred_xp);("py",pred_y);("pw",pred_w);("root",pred_root);("pred",pred_red);
     ("pblk",pred_black);("pbad",all_nonrbs_del)] ;; *)
(*  [("px",pred_x);("pxp",pred_xp);("py",pred_y);("pw",pred_w);("root",pred_root);("pred",pred_red);
     ("pblk",pred_black);("pbad",bad_pred)] ;; *)
(*  [("px",pred_x);("pxp",pred_xp);("py",pred_y);("pw",pred_w);("root",pred_root);("pred",pred_red);
     ("pblk",pred_black);("pini",ini_pred )] ;; *)

let main () =
	run_main_loop_predabs 
(*   ~abstr_restriction:Unrestricted*)
   ~abstr_restriction:(Positive[0])
   "RBT" 
   (Array.of_list comp_rbt_reb_del)
   0 
   init_rbt_reb_del
   init_preds 
   (Some (get_all_nonrb_trees_del (),Some all_rb_trees_del)) 
(*   (Some (get_all_nonrb_trees_del (),None)) *)
(*   None*)
;;

main()

