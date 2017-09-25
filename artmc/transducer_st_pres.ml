open Taml;;
open Mess;;
let print_time str func arg = print_string str; print_running_time func arg
(* ==================================================================================================== *)
(* **************************************************************************************************** *)
(* ***** Transducing an automaton in a structure-preserving way                                         *)
(* **************************************************************************************************** *)
(* ==================================================================================================== *)

(* ==================================================================================================== *)
(* ***** Precompiling a structure-preserving transducer                                                 *)
(* ==================================================================================================== *)

let compile_tr_state state_str = Common.Const (Symbol.of_string state_str);;

let rec compile_tr_states st_names =
  match st_names with
      [] -> State_set.empty
    | st_name::st_names_rest ->
        let state_set_rest = compile_tr_states st_names_rest in
          State_set.add (compile_tr_state st_name) state_set_rest;;

let rec compile_tr_ops st_names =
  match st_names with
      [] -> Alphabet.new_alphabet
    | st_name::st_names_rest ->
        let st_ops_rest = compile_tr_ops st_names_rest in
          Alphabet.add_symbol (Symbol.of_string st_name) 0 st_ops_rest;;

let compile_tr_rule tr_rule =
  match tr_rule with (src_op_str, arg_str, targ_op_str, targ_st_str) ->
    let src_op = Symbol.of_string src_op_str in
    let arg = List.map compile_tr_state arg_str in
    let targ_op = Symbol.of_string targ_op_str in
    let targ_st = compile_tr_state targ_st_str in
      (src_op, arg, targ_op, targ_st);;

let compile_transducer trans =
  match trans with (tr_states,tr_fin_states,tr_rules) ->
    ( (compile_tr_ops tr_states),
      (compile_tr_states tr_states),
      (compile_tr_states tr_fin_states),
      (List.map compile_tr_rule tr_rules) );;

(* ==================================================================================================== *)
(* ***** Inverting structure-preserving transducers                                                     *)
(* ==================================================================================================== *)

let rec invert_rules rules =
  match rules with
      [] -> []
    | (insym,instates,outsym,outstate)::rules_rest ->
        (outsym,instates,insym,outstate)::(invert_rules rules_rest);;

let inverse_transducer2 trans =
  match trans with (tr_ops,tr_states,tr_fin_states,tr_rules) ->
    tr_ops,tr_states,tr_fin_states,(invert_rules tr_rules);;

let inverse_transducer trans =
  match trans with (tr_states,tr_fin_states,tr_rules) ->
     let res = compile_transducer (tr_states,tr_fin_states,(invert_rules
     tr_rules)) in
     let check = inverse_transducer2 (compile_transducer trans) in
     if res=check then res else failwith"inverse_transducer"


(* ==================================================================================================== *)
(* ***** Functions for composing an automaton transition with a struct.-preserv. transducer transition  *)
(* ==================================================================================================== *)

type 'a res_type = Sym of Taml.Symbol.t 
                 | SymList of Taml.Symbol.t list
                 | Term of (Taml.Symbol.t, 'a) Common.term_const
                 | TermList of ((Taml.Symbol.t, 'a) Common.term_const) list
                 | Rule of Taml.Rewrite.rule
                 | RuleList of Taml.Rewrite.rule list
                 | Err;;

let merge_states state1 state2 = 
  Common.Special (Common.Fsym (State_set.default_prod_symbol,[state1;state2]));;

let merge_substate_state substate1 state2 = 
  match substate1 with (Common.Special state1) ->
    merge_states state1 state2
  | _->failwith("merge_substate_state")

let merge_substate_state_list substate_list state_list =
  if ((List.length substate_list) = (List.length state_list)) then
    TermList (List.map2 merge_substate_state substate_list state_list ) 
  else
    Err;;

let do_compose_one_aut_one_tr_rule aut_lhs aut_targ tr_op tr_arg tr_new_op tr_targ =
  match aut_lhs with
      Common.Fsym (aut_op, aut_arg) -> 
        (if (aut_op = tr_op) then
           let new_arg_res = merge_substate_state_list aut_arg tr_arg in   
             (match new_arg_res with
                 (TermList new_arg) ->
                   (match aut_targ with Common.Special aut_targ_stripped ->
                     (Rule (Rewrite.new_rule (Common.Fsym (tr_new_op, new_arg))
                                             (merge_states aut_targ_stripped tr_targ)))
               	    | _ -> failwith("do_compose_one_aut_one_tr_rule1")
		   )
               | _ -> Err(*tohle ale nepatri k tomu, k cemu je to zarovnane !*)
             )
         else Err
        )  
    | Common.Const aut_op ->
      (if ((aut_op = tr_op) && (tr_arg = [])) then
         match aut_targ with Common.Special aut_targ_stripped ->
           (Rule (Rewrite.new_rule (Common.Const tr_new_op) (merge_states aut_targ_stripped tr_targ)))
	   |_->failwith"do_compose_one_aut_one_tr_rule2"
       else Err
      )
    | _ -> Err;;

let compose_one_aut_one_tr_rule aut_rule tr_rule =
  let aut_lhs = Rewrite.lhs aut_rule in
  let aut_targ = Rewrite.rhs aut_rule in
  match tr_rule with (tr_op, tr_arg, tr_new_op, tr_targ) ->
    do_compose_one_aut_one_tr_rule aut_lhs aut_targ tr_op tr_arg tr_new_op tr_targ;;

(* ==================================================================================================== *)
(* ***** Composing a set of automata transitions with a set of transduction rules                       *)
(* ==================================================================================================== *)

let rec compose_one_aut_rule_all_tr_rules aut_rule tr_rules =
  match tr_rules with
      [] -> Rewrite.empty
    | tr_rule :: tr_rules_rest -> 
        (let res = compose_one_aut_one_tr_rule aut_rule tr_rule in
         let new_rules = compose_one_aut_rule_all_tr_rules aut_rule tr_rules_rest in
         match res with
             Rule new_rule -> (Rewrite.add new_rule new_rules)
           | _ -> new_rules
        );;

let rec compose_aut_tr_rules aut_rules tr_rules =
  if (Rewrite.is_empty aut_rules) then Rewrite.empty
  else 
    let fst_aut_rule = (Rewrite.first aut_rules) in
    let aut_rules_rest = (Rewrite.remainder aut_rules) in
      Rewrite.union (compose_one_aut_rule_all_tr_rules fst_aut_rule tr_rules)
                    (compose_aut_tr_rules aut_rules_rest tr_rules);;

(* ==================================================================================================== *)
(* ***** Computing the new set of states and final states -- simply the product                         *)
(* ==================================================================================================== *)

let compose_aut_tr_states aut_states tr_states = State_set.symbolic_product aut_states tr_states;;

(* ==================================================================================================== *)
(* ***** Computing a one-step transduction                                                              *)
(* ==================================================================================================== *)

let do_apply_tr_aut tr aut =
  let aut_states = Automaton.get_states aut in
  let aut_fin_states = Automaton.get_final_states aut in
  let aut_rules = Automaton.get_transitions aut in
  match tr with (tr_st_ops, tr_states, tr_fin_states, tr_rules) ->
    (
(*     let new_states = compose_aut_tr_states aut_states tr_states in*)
(*     let new_fin_states = compose_aut_tr_states aut_fin_states tr_fin_states in*)
(*     let new_rules = compose_aut_tr_rules aut_rules tr_rules in*)
       (Automaton.make_automaton
         (Automaton.get_alphabet aut)
         (Alphabet.add_symbol 
            State_set.default_prod_symbol 
            2
            (Alphabet.union (Automaton.get_state_ops aut) tr_st_ops))
         (compose_aut_tr_states aut_states tr_states)
         (compose_aut_tr_states aut_fin_states tr_fin_states)
         (Automaton.get_prior aut)                            (* We suppose prior to be always empty *)
         (compose_aut_tr_rules aut_rules tr_rules) 
        ) 
      );;

let apply_tr_aut tr aut = Interim.simplify_taml (do_apply_tr_aut tr aut);;
(*let apply_tr_aut tr aut = Automaton.simplify (do_apply_tr_aut tr aut);;*)

