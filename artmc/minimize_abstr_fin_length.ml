open Taml;;
(* ==================================================================================================== *)
(* **************************************************************************************************** *)
(* ***** Some universal functions                                                                       *)
(* **************************************************************************************************** *)
(* ==================================================================================================== *)

exception UnexpectedUnmatch of string;;

(* ==================================================================================================== *)

let listOfStr_to_str sep list = String.concat sep list;;

let print_listOfStr_to_str list = Printf.printf "> %s\n" (listOfStr_to_str " " list);;

let listOfListOfStr_to_str sep1 sep2 list = 
  let listOfStr_to_str2 list2 = listOfStr_to_str sep2 list2 in
    listOfStr_to_str sep1 (List.map listOfStr_to_str2 list);;

let print_listOfListOfStr_to_str list = Printf.printf ">> %s\n" (listOfListOfStr_to_str " | " " " list);;

(* ==================================================================================================== *)

let rec remove_duplicities list =
  match list with
    [] -> []
  | elm::list_rest ->
     let rest = (remove_duplicities list_rest) in
       if (List.mem elm rest) then rest
       else elm::rest;;

let rec list_minus_list list1 list2 =
  match list1 with 
      [] -> []
    | elm::list1_rest -> 
        if (List.mem elm list2) then (list_minus_list list1_rest list2)
        else elm::(list_minus_list list1_rest list2);;

(* ==================================================================================================== *)

(* *** Maintaing a list-encoded set. The list is kept ordered! *)

let rec add_to_ordlist list elem =
  match list with
      [] ->  [ elem ]
    | elem2::list_rest -> 
        if elem=elem2 then elem::list_rest
        else if elem2>elem then elem::(elem2::list_rest)
        else elem2::(add_to_ordlist list_rest elem);;

let rec is_in_ordlist list elem =
  match list with
      [] ->  false
    | elem2::list_rest -> 
        if elem=elem2 then true
        else if elem2>elem then false
        else is_in_ordlist list_rest elem;;

(* ==================================================================================================== *)

let is_leaf_rule rule = 
  match (Rewrite.lhs rule) with
      Common.Const(_) -> true
    | _ -> false;;

(* -------------------------------------------------------
    Next two functions are taken from predicate labeling 
    implementation and are used in minimazition
   ------------------------------------------------------- *)

(* Maintaining a table of labels -- i.e. a list of (state,list of states) *)
(* *** We supose labelling of Common.Special by Common.Special... Again, we keep the lists ordered! *)

let rec add_label lab_table st label =
  match lab_table with
      [] -> [ (st, [ label ]) ]
    | (st2,lab_list)::lab_table_rest -> 
        if st=st2 then (st,(add_to_ordlist lab_list label))::lab_table_rest
        else if st2>st then (st, [ label ])::((st2,lab_list)::lab_table_rest)
        else (st2,lab_list)::(add_label lab_table_rest st label);;

let rec leaf_and_inner_rules rules =
  match rules with
      [] -> ([],[])
    | rule::rules_rest ->
      let (leaf_rules_rest,inner_rules_rest) = (leaf_and_inner_rules rules_rest) in
        if (is_leaf_rule rule) then (rule::leaf_rules_rest,inner_rules_rest)
        else (leaf_rules_rest,rule::inner_rules_rest);;


(* ==================================================================================================== *)
(* **************************************************************************************************** *)
(* ***** Minimization of simplified deterministic bottom-up tree automata                               *)
(* **************************************************************************************************** *)
(* ==================================================================================================== *)

let rec rule_for_minimization rule =
  match (Rewrite.lhs rule) with
      Common.Fsym (symbol,from_states_list) -> 
        ((Symbol.to_string symbol),
         List.map Term.to_string from_states_list,
         Term.to_string (Rewrite.rhs rule))
    | Common.Const (symbol) ->
        ((Symbol.to_string symbol),
         [],
         Term.to_string (Rewrite.rhs rule))
    | _ -> failwith("rule_for_minimization");;	 

let rec add_rules_for_minimization symbol st_list1 st_list2 target table =
  match st_list2 with
      [] -> table
    | st::st_list2_rest -> 
        add_label (add_rules_for_minimization symbol (st_list1 @ [st]) st_list2_rest target table) 
                  st
                  (symbol,(st_list1 @ ("__"::st_list2_rest)),target);;

let rec rules_for_minimization rules =
  match rules with
      [] -> []
    | rule::rules_rest -> 
        let table = (rules_for_minimization rules_rest) in
        let (symbol,st_list,target) = (rule_for_minimization rule) in
          (add_rules_for_minimization symbol [] st_list target table);;

(* ==================================================================================================== *)

let rec usedst_in_minim st rules =
  match rules with
      [] -> false
    | (st2,_)::rules_rest ->
        if (st=st2) then true 
        else (usedst_in_minim st rules_rest);;

let rec add_rules_for_unusedst_in_minim st_list rules =
  match st_list with
      [] -> rules
    | st::st_list_rest -> 
        if (usedst_in_minim st rules) then
          (add_rules_for_unusedst_in_minim st_list_rest rules)
        else (st,[])::(add_rules_for_unusedst_in_minim st_list_rest rules);;

(* ==================================================================================================== *)

let rec st_in_class st class_list =
  match class_list with
    [] -> raise (UnexpectedUnmatch "st_in_class")
  | cl::class_list_rest ->
      if (List.mem st cl) then cl
      else (st_in_class st class_list_rest);;

(* ==================================================================================================== *)

let rec do_prepare_new_part_for_minim rules class_list =
  match rules with
      [] -> []
    | (symbol,st_list,target)::rules_rest ->
        (symbol,st_list,(st_in_class target class_list))::(do_prepare_new_part_for_minim rules_rest class_list);;
 
let rec prepare_new_part_for_minim st_rules class_list =
  match st_rules with
      [] -> []
    | (state,rules)::st_rules_rest ->
        let res_rest = (prepare_new_part_for_minim st_rules_rest class_list) in 
        let res = (state,(st_in_class state class_list),
                         (List.sort Pervasives.compare (do_prepare_new_part_for_minim rules class_list))) in
          res::res_rest;;

(* ==================================================================================================== *)

let rec coll_new_part_for_minim cl_descr cl_list to_do_list skip_list =
    match to_do_list with
      [] -> 
        (match skip_list with
           [] -> [ cl_list ] 
         | (st,old_cl,old_rules)::skip_list_rest ->
             let part_rest = (coll_new_part_for_minim (old_cl,old_rules) [st] skip_list_rest []) in
               cl_list::part_rest
        )
    | (st,old_cl,old_rules)::to_do_list_rest ->
        if ((old_cl,old_rules) = cl_descr) then
          (coll_new_part_for_minim cl_descr (st::cl_list) to_do_list_rest skip_list)
        else
          (coll_new_part_for_minim cl_descr cl_list to_do_list_rest ((st,old_cl,old_rules)::skip_list));;

let new_part_for_minim st_rules old_class_list =
  let sort_list l = List.sort Pervasives.compare l in
  let prep_part1 = prepare_new_part_for_minim st_rules old_class_list in
  let prep_part2 = match prep_part1 with
    (st,cl,rules)::part_rest ->
      (coll_new_part_for_minim (cl,rules) [st] part_rest []) 
      |_->failwith"new_part_for_minim"
  in
    (sort_list (List.map sort_list prep_part2));;
		   
(* ==================================================================================================== *)

let rec part_for_minim st_rules old_class_list =
  let new_class_list = (new_part_for_minim st_rules old_class_list) in
    if (old_class_list = new_class_list) then new_class_list
    else (part_for_minim st_rules new_class_list);;

(* following function is modified function part_for_minim, and it is used to abstracting of automata
   based on finite length languages *)

let rec abstr_len_n_part_for_minim st_rules old_class_list deep=
  (* If we reach deep 0, we stop the algorithm. *)
  if (deep=0) then old_class_list
  else
  	let new_class_list = (new_part_for_minim st_rules old_class_list) in
	    if (old_class_list = new_class_list) then new_class_list
	    else (abstr_len_n_part_for_minim st_rules new_class_list (deep-1));;
   

(* ==================================================================================================== *)

let rec minim_gen_states class_list =
  match class_list with 
      [] -> (State_set.empty, Alphabet.new_alphabet)
    | cls::class_list_rest ->
        let (st_rest, st_ops_rest) = (minim_gen_states class_list_rest) in
          ((State_set.add (Common.Const (Symbol.of_string (String.concat "" cls))) st_rest), 
           (Alphabet.add_symbol (Symbol.of_string (String.concat "" cls)) 0 st_ops_rest));;

let rec minim_gen_fin_states class_list fin_stset =
  match class_list with 
    [] -> State_set.empty
  | (st::cls_rest)::class_list_rest ->
      let new_fin_rest = (minim_gen_fin_states class_list_rest fin_stset) in
        if (List.mem st fin_stset) then 
          (State_set.add (Common.Const (Symbol.of_string (String.concat "" (st::cls_rest)))) new_fin_rest)
        else new_fin_rest
  |_->failwith"minim_gen_fin_states"
;;

(* ==================================================================================================== *)

let minim_rename_const_to_class class_list const =
  Common.Const (Symbol.of_string (String.concat "" (st_in_class (Term.to_string const) class_list)));;

let minim_rename_spec_to_class class_list spec = 
  match spec with
    Common.Special const ->
      Common.Special (minim_rename_const_to_class class_list const)
  |_->failwith"minim_rename_spec_to_class"
 ;;

let rec minim_rename_spec_list_to_class class_list spec_list = 
  match spec_list with 
      [] -> []
    | spec::spec_list_rest -> 
        (minim_rename_spec_to_class class_list spec)::(minim_rename_spec_list_to_class class_list spec_list_rest);;

let minim_rename_aut_rule_to_class class_list rule =
  let lhs,targ = Rewrite.lhs rule, Rewrite.rhs rule in
  match lhs with
      Common.Fsym (op, arg) -> 
        (Rewrite.new_rule (Common.Fsym (op, (minim_rename_spec_list_to_class class_list arg))) 
                                       (minim_rename_spec_to_class class_list targ))
    | Common.Const op ->
        (Rewrite.new_rule (Common.Const op) (minim_rename_spec_to_class class_list targ))
    |_->failwith"minim_rename_aut_rule_to_class"
;;

let rec do_minim_rename_aut_rules_to_class class_list rules =
  if Rewrite.is_empty rules then []
  else let rule,rules_rest = Rewrite.first rules, Rewrite.remainder rules in
    (minim_rename_aut_rule_to_class class_list rule)::(do_minim_rename_aut_rules_to_class class_list rules_rest);;

let minim_rename_aut_rules_to_class class_list rules =
  Rewrite.list_to_trs (remove_duplicities (do_minim_rename_aut_rules_to_class class_list rules));;

(* ==================================================================================================== *)

let minimize aut =
  (* check for empty automaton *)
  if (Automaton.is_language_empty aut) then aut
  else (* do minimization *)
  let st_list = (List.map Term.to_string (State_set.to_list (Automaton.get_states aut))) in
  let fin_st_list = (List.map Term.to_string (State_set.to_list (Automaton.get_final_states aut))) in
  let non_fin_st_list = (list_minus_list st_list fin_st_list) in
  let (_,non_leaf_rules) = (leaf_and_inner_rules (Rewrite.to_list (Automaton.get_transitions aut))) in
  let rules_for_minim = (add_rules_for_unusedst_in_minim st_list (rules_for_minimization non_leaf_rules)) in
  let cls_list = (part_for_minim rules_for_minim [ non_fin_st_list; fin_st_list ]) in
  let (new_st_set, new_st_ops) = (minim_gen_states cls_list) in
    (Automaton.make_automaton
      (Automaton.get_alphabet aut)
      new_st_ops
      new_st_set
      (minim_gen_fin_states cls_list fin_st_list)
      Rewrite.empty
      (minim_rename_aut_rules_to_class cls_list (Automaton.get_transitions aut)) 
     );;

(* abstraction based on finite deep tree languages is a minimalization, which is stoped after n steps,
   so some states are collabsed into one state *)

   
let abstract_fin_deep aut deep=
  (* check for empty automaton *)
  if (Automaton.is_language_empty aut) then aut
  else (* do abstraction *)
  let st_list = (List.map Term.to_string (State_set.to_list (Automaton.get_states aut))) in
  let fin_st_list = (List.map Term.to_string (State_set.to_list (Automaton.get_final_states aut))) in
  let non_fin_st_list = (list_minus_list st_list fin_st_list) in
  let (_,non_leaf_rules) = (leaf_and_inner_rules (Rewrite.to_list (Automaton.get_transitions aut))) in
  let rules_for_minim = (add_rules_for_unusedst_in_minim st_list (rules_for_minimization non_leaf_rules)) in
  let cls_list = (abstr_len_n_part_for_minim rules_for_minim [ non_fin_st_list; fin_st_list ] deep) in
  let (new_st_set, new_st_ops) = (minim_gen_states cls_list) in
    (Automaton.make_automaton
      (Automaton.get_alphabet aut)
      new_st_ops
      new_st_set
      (minim_gen_fin_states cls_list fin_st_list)
      Rewrite.empty
      (minim_rename_aut_rules_to_class cls_list (Automaton.get_transitions aut)) 
     );;


     
