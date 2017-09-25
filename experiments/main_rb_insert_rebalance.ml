open Rb_insert_rebalance;;
open Taml;;
open Main_loop;;
open Predicate_generation;;
open Colapsing_v3;;

let pred_x=create_predicate_automaton "x" ["root";"x";"xp";"xpp";"y"] ["red";"black"];; 
let pred_xp=create_predicate_automaton "xp" ["root";"x";"xp";"xpp";"y"] ["red";"black"];; 
let pred_xpp=create_predicate_automaton "xpp" ["root";"x";"xp";"xpp";"y"] ["red";"black"];; 
let pred_y=create_predicate_automaton "y" ["root";"x";"xp";"xpp";"y"] ["red";"black"];; 
let pred_root=create_predicate_automaton "root" ["root";"x";"xp";"xpp";"y"] ["red";"black"];; 

let pred_red=create_data_predicate_automaton "red" ["root";"x";"xp";"xpp";"y"] ["red";"black"];; 
(* let pred_blk=create_data_predicate_automaton "black" ["root";"x";"xp";"xpp";"y"] ["red";"black"];; *)

let init_preds =  
(*    [("px",pred_x);("pxp",pred_xp);("pxpp",pred_xpp);("py",pred_y)] ;;*)
(*    [("px",pred_x);("pxp",pred_xp);("pxpp",pred_xpp);("py",pred_y);("root",pred_root)]
 *    ;; *)
    [("px",pred_x);("pxp",pred_xp);("pxpp",pred_xpp);("py",pred_y);("root",pred_root);("pred",pred_red)] ;;

let main () =
	run_main_loop_predabs 
(*   ~abstr_restriction:Unrestricted*)
   ~abstr_restriction:(Positive[1])
   "RBT" 
   (Array.of_list comp_rbt_reb_ins)
   0 
   init_rbt_reb_ins   
(*   init_preds (Some (get_all_nonrb_trees (),Some all_rb_trees))*)
(*   init_preds (Some (get_all_nonrb_trees (),None))*)
    init_preds None
;;

main()

