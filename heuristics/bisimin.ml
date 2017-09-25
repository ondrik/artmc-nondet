
open Taml;;

(*block - finer relation class, group - rougher relation class*)
let vl opt str = 
  match opt with
    None -> failwith ("vl:"^str)
  | Some a -> a
;;
let pvl p_opt str = vl (!p_opt) str ;;

type  state = {
	s_name: string;
	s_block: block ref option ref;
	s_rules: rule ref list ref; 
	s_c: int ref option array;
	s_mark: bool ref;
	s_cmarks: bool array;
	s_final: bool
	}

and block = {
	b_group: group ref option ref; 
	b_states: state ref list ref; 
	b_child: block ref option ref;
	b_n: int ref 
	}

and group = {
	g_blocks: block ref list ref; 
	g_n: int ref 
	}

and cell = {
	c_state: state ref; 
	c_c: int ref option ref; 
	c_c1: int ref option ref;
	c_c2: int ref option ref;
	i:int
	}

and rule = {
	r_symbol: string;
	r_symbolic_rule: (symbolic_rule ref) ref; 
	r_cells:  cell ref list;
	r_mark: bool ref 
	}

and leaf = {
	l_rules: rule ref list ref;
	l_positions:  cell ref list list ref 
	}

and tree = 
	Empty |
	Leaf of leaf ref |
	Node of tree * tree

and symbolic_rule = {
	sr_tree: tree ref;
	sr_leaves: leaf ref list ref;
	sr_mark: bool ref
	}
;;

(*First I have to transform rules of automaton into structure from asrticle. No direct acces to states from rules in Taml, so i am using Map*)

(*Map of new states - key is name (Taml) of state*)
module String_map = Map.Make(String);;

(*Maru¹ 731725508*)

let new_p_group () = ref {g_blocks = ref []; g_n = ref 0};;
let new_p_block  () = ref {b_group = ref None; b_states = ref []; b_n = ref 0; b_child = ref None};;
let new_p_state max_sigma_card final taml_state = 
	let name =Term.to_string taml_state in 
	ref {   s_name = name; 
		s_block = ref None; 
		s_rules = ref []; 
		s_mark = ref false;
		s_cmarks = Array.make max_sigma_card false;
		s_c = Array.make max_sigma_card (None);
		s_final = final
		}
;;
let new_leaf() = {l_rules = ref []; l_positions = ref []};;

(*adds state to block. Increments and decrements counts of states of from and target blocks*)
(*doesn't check if state isn't alreadi present in target block*)
let add_to_block p_block p_state =
	incr(!p_block.b_n);
	(match !(!p_state.s_block) with None -> () | Some p_bl -> decr(!p_bl.b_n));
	!p_block.b_states := p_state::!(!p_block.b_states);
	!p_state.s_block := Some p_block
;;

(*analogous as previous function*)
let add_to_group p_group p_block =
	incr(!p_group.g_n);
	(match !(!p_block.b_group) with None -> () | Some p_gr -> decr(!p_gr.g_n));
	!p_group.g_blocks := p_block::!(!p_group.g_blocks);
	!p_block.b_group := Some p_group;
;;

let (<=) = add_to_block;;
let (<<=) = add_to_group;;

let b_empty p_block = !(!p_block.b_n)<1;;
let g_empty p_group = !(!p_group.g_n)<1;;
let g_compound p_group = !(!p_group.g_n)>1;;

let get_max_arity alphabet = 
	List.fold_left	(fun t_max syma -> if t_max > (snd syma) then t_max else (snd syma)) 
			0 
			(Alphabet.to_list alphabet)
;;

let make_init_Group_State_p_map aut =
	let taml_final_states = State_set.to_list (Automaton.get_final_states aut) in
	let taml_nonfinal_states =  State_set.to_list (State_set.minus (Automaton.get_states aut) (Automaton.get_final_states aut)) in

	let p_init_group = new_p_group() in
	let p_final_block = new_p_block() in
	let p_nonfinal_block = new_p_block() in

	let max_arity = (get_max_arity (Automaton.get_alphabet aut)) + 1 in
	let final_state_p_list = List.map (new_p_state max_arity true) taml_final_states in
	let nonfinal_state_p_list = List.map (new_p_state max_arity false) taml_nonfinal_states in

	let add_state map taml_state p_state = String_map.add (Term.to_string taml_state) p_state map in
	let final_state_p_map = List.fold_left2 add_state String_map.empty taml_final_states final_state_p_list in
	let all_state_p_map = List.fold_left2 add_state final_state_p_map taml_nonfinal_states nonfinal_state_p_list in

	List.iter (add_to_block p_final_block) final_state_p_list; 
	List.iter (add_to_block p_nonfinal_block) nonfinal_state_p_list; 
	if not (b_empty p_final_block) then p_init_group<<=p_final_block; 
	if not (b_empty p_nonfinal_block) then p_init_group<<=p_nonfinal_block; 
	
	p_init_group,all_state_p_map
;;

let make_init_symbolic_rule_tree_leaf_p_List_Map aut =
	let symbol_name_list = Alphabet.to_string_list(Automaton.get_alphabet aut) in

	let leaf_p_list = List.map (function _ -> ref (new_leaf())) symbol_name_list in
	let add_p_leaf map symbol_name p_leaf = String_map.add symbol_name p_leaf map in
	let leaf_p_map = List.fold_left2 add_p_leaf String_map.empty symbol_name_list leaf_p_list in

	leaf_p_list, leaf_p_map
;;


(*rule from Taml rule. I transpose lhs and rhs - rhs first. I want to be able to find rhs fast *)
let make_rule taml_rule state_p_map p_sym_rule = 
	let lhs = Rewrite.lhs taml_rule in
	let rhs = Rewrite.rhs taml_rule in
	let state_list = ((Term.list_leaves rhs)@(Term.list_arguments lhs)) in
(*	let state_list = ((Term.list_arguments lhs)@(Term.list_leaves rhs)) in*)
	let make_p_cell index taml_state = ref {
		c_state = String_map.find (Term.to_string taml_state) state_p_map;
		c_c	= ref None;
		c_c1	= ref None;
		c_c2	= ref None;
		i = index;
		} in
(*	let cells = let i=ref (-1) in List.map (i:=!i+1;print_int !i;make_p_cell !i) state_list in PROC TO NEFUNGUJE???*)
	let rec get_cells st_list i = match st_list with [] -> [] | st::tail -> (make_p_cell i st)::get_cells tail (i+1) in
	let cells = get_cells state_list 0 in
	let symbol = Symbol.to_string(Term.top_symbol lhs) in 
	{r_cells = cells; r_symbol = symbol; r_mark = ref false; r_symbolic_rule = ref p_sym_rule} ,symbol
;;

(*adds rule to state (pointed from cell)*)
let add_rule_to_state p_rule p_cell = 
	let p_state = !p_cell.c_state in
	if (!(!p_state.s_rules) = [] ||  List.hd !(!p_state.s_rules) != p_rule) then
		!p_state.s_rules := p_rule::!(!p_state.s_rules); 
;;
	
(*connects rule to the list of rules, connects neighbour cells of head and added rule*)
(*Now I connect olso rhs of rule*)
let connect_to_leaf p_leaf p_rule =
	(match !(!p_leaf.l_rules) with 
		[] -> !p_leaf.l_positions:= List.map (function p_cell -> [p_cell]) ((*List.tl*) (!p_rule.r_cells))
		| hd::_ -> !p_leaf.l_positions:=List.map2 (fun p_cell position -> p_cell::position)
							((*List.tl*) !p_rule.r_cells) !(!p_leaf.l_positions)
	);
	!p_leaf.l_rules:=p_rule::!(!p_leaf.l_rules)
;;

(*transforms Taml rule into rule, connects it to appropriate states, connect it to appropriate leafs of initial symbolic
rule*)
let process_taml_rule state_p_map leaf_p_map p_sym_rule taml_rule  = 
	match make_rule taml_rule state_p_map p_sym_rule with rule,symbol ->
	let p_rule = ref rule in
	List.iter (add_rule_to_state p_rule) !p_rule.r_cells;
	let p_leaf = String_map.find symbol leaf_p_map in
	connect_to_leaf p_leaf p_rule;
	p_rule
;;

(*let's misbehave*)
let transofrm_that_fucking_Taml_automaton_to_something_more_fucking aut =
	match make_init_symbolic_rule_tree_leaf_p_List_Map aut with leaf_p_list,leaf_p_map ->
	let p_init_sym_rule = ref {sr_tree =ref  Empty; sr_leaves = ref leaf_p_list; sr_mark = ref false} in

	let taml_rule_list = Rewrite.to_list (Automaton.get_transitions aut) in

	match make_init_Group_State_p_map aut with p_init_group,state_p_map -> 
	let rules = List.map (process_taml_rule state_p_map leaf_p_map p_init_sym_rule) taml_rule_list in

	p_init_group, p_init_sym_rule, rules
;;

let print_positions s_r = 
	let l = s_r.sr_leaves in
	let pr plf = 
		let pl = !plf.l_positions in
		let p_p p = 
			let str = String.concat " " (List.map (fun p_c -> !(!p_c.c_state).s_name) p) in
			print_string (str^"\n")
		in
		List.iter p_p !pl;
		print_string "---\n"
	in
	List.iter pr !l
;;

(*for all rules of leaf, for all actions in list do: for all cells of rule run action on it*)
let for_all_cells_of_leaf action_list p_leaf =
	let process_rule p_rule = 
		let apply_action cell_action = List.iter cell_action !p_rule.r_cells in 
		List.iter apply_action action_list 
	in
	List.iter process_rule !(!p_leaf.l_rules)
;;

(****************************************************************************************************)
(*					Dealing with counters					    *)
(****************************************************************************************************)

type which_c = C | C1 | C2 | NoC;; 
let counter which p_cell = 
	match which with
	C  -> !p_cell.c_c |
	C1 -> !p_cell.c_c1 |
	C2 -> !p_cell.c_c2 |
	_-> failwith "counter"
;;

(*increments c, c1, or c2 of cell, markes state of cell*)
let inc_counter  which_counter p_cell =
	let p_state = !p_cell.c_state in
	let s_c =  !p_state.s_c in
	let i = (!p_cell.i) in
		(match s_c.(i) with
			None -> s_c.(i) <- Some (ref 1)
			|Some p_c -> p_c := (!p_c+1)
		);
		
	(counter which_counter p_cell):=s_c.(i)
;;

(*unmarkes state of cell*)
let unmark_state p_cell =
	!(!p_cell.c_state).s_mark:=false
;;

let disconnect_s_c_i p_cell = !(!p_cell.c_state).s_c.(!p_cell.i) <- None;;

(*calculates values of counters in symblolic rule tree*)
let calculate_counters which disconnect_after_leaf p_sym_rule = 
	let visit_leaf p_leaf =
		 for_all_cells_of_leaf  [inc_counter which] p_leaf;
		 if disconnect_after_leaf then for_all_cells_of_leaf [disconnect_s_c_i] p_leaf
	in
	List.iter visit_leaf !(!p_sym_rule.sr_leaves);
	if not disconnect_after_leaf then 
		List.iter (for_all_cells_of_leaf [disconnect_s_c_i]) !(!p_sym_rule.sr_leaves)
;;

let print_counters which p_sym_rule = 
	let print_cell which p_nl p_cell = 
		p_nl:=true;
		Printf.printf "|%s %d|" !(!p_cell.c_state).s_name 
			(match !(counter which p_cell) with Some p_c -> !p_c | _ -> -1) 
	in
	let print_nl p_nl p_cell = 
		if !p_nl then print_newline(); p_nl:=false in
	let p_nl = ref true in
	let visit_leaf p_leaf = 
		for_all_cells_of_leaf [print_cell which p_nl; print_nl p_nl] p_leaf;
		print_endline "---------" 
	in
	List.iter visit_leaf !(!p_sym_rule.sr_leaves)
;;

let print_all_counters which sym_rules = 
	List.iter (function p_sr -> print_counters which p_sr;print_endline "\n***********************") sym_rules
;;
	
(*for all lists of sym. rule tree: makes new symbolic rule and connects all cells to it*)
let connect_one_sr_rules_to_new_sym_rules p_sym_rule =
	let visit_leaf p_leaf =
		let p_new_sym_rule = ref {sr_tree = ref Empty; sr_leaves = ref []; sr_mark = ref false} in
		let connect p_rule = !p_rule.r_symbolic_rule := p_new_sym_rule in
		List.iter connect !(!p_leaf.l_rules);
		p_new_sym_rule
	in
	List.map visit_leaf !(!p_sym_rule.sr_leaves) 
;;


let connect_rules_to_new_sym_rules p_sym_rules =
	let new_sym_rules = (List.concat (List.map connect_one_sr_rules_to_new_sym_rules !p_sym_rules)) in
	List.iter (function p_sr -> !p_sr.sr_tree:=Empty;!p_sr.sr_leaves:=[]) !p_sym_rules;
	p_sym_rules:=!p_sym_rules@new_sym_rules
;;


(****************************************************************************************)
(*			Refinemets of relation wrt leaves of rules			*)
(****************************************************************************************)

(*moves state from current block to new block, but doesn't remove it from old block state list*)
(*adds old block to list of split blocks*)
let rip_off_state p_split_blocks p_cell = 
(*	let p_split_blocks = ref split_blocks in*)
	if not !(!(!p_cell.c_state).s_mark) then (
		let p_block = pvl (!(!p_cell.c_state).s_block) "rip_off_state1" in
		let p_child = match !(!p_block.b_child) with 
			None -> let new_pb = new_p_block() in
				p_split_blocks := (pvl(!(!p_cell.c_state).s_block) "rip_off_state2")::!p_split_blocks;
				!p_block.b_child := Some new_pb; 
				new_pb
			| Some pb -> pb in
		p_child <= !p_cell.c_state;
		!(!p_cell.c_state).s_mark:=true
	)
(*	!p_split_blocks*)
;;

(*connects new blocks, which hav been created by splitting, into groups*)
let integrate_split_blocks split_block_list = 
	let integrate_split_block p_block = 
		match !(!p_block.b_child) with None -> () | Some p_child ->
		(pvl !p_block.b_group "integrate_split_blocks") <<= p_child;
		!p_block.b_child := None
	in
	List.iter integrate_split_block split_block_list
;;

(*splits all blocks pointed to from list of cells (--position list) *)
let split_blocks cell_p_list =
	let p_split_blocks = ref [] in
	List.iter (rip_off_state p_split_blocks) cell_p_list;
	integrate_split_blocks !p_split_blocks; 
	List.iter unmark_state cell_p_list 
;;

(*refine relation wrt one symbolic rule tree and its rules*)
let refine_wrt_one_sr_possitions p_sym_rule =
	let process_leaf p_leaf = List.iter split_blocks !(!p_leaf.l_positions) in 
	List.iter process_leaf !(!p_sym_rule.sr_leaves)
;;

(*deletes empty blocks from group*)
let delete_empty_blocks p_group =
	let stay_if_not_empty p_block = 
		if b_empty p_block then (decr(!p_group.g_n);false)
		else true
	in
	!p_group.g_blocks:=List.filter stay_if_not_empty !(!p_group.g_blocks)
;;

(*removes empty groups, partition the rest into compound and solid groups*)
(*could be more effective -- propably I could presume that no blocks in compound are solid*)
let sort_groups p_groups =
	match !p_groups with (compound,solid) ->
	let not_empty g = not (g_empty g) in
	p_groups:=(List.partition g_compound (List.filter not_empty compound@solid))
;;

(*from all blocks (of group) and their state lists deletes states, which doesn't belong to block*)
let revise_blocks p_group =
	let revise_block p_block =
		!p_block.b_states:=List.filter (function p_state -> (pvl(!p_state.s_block) "revise_blocks")== p_block) !(!p_block.b_states)
	in
	List.iter revise_block !(!p_group.g_blocks) 
;;

(*deletes empty blocks, deletes empty groups (maybee not necessary), reparttitions groups into compound and solid,*)
(*deletes states which doesn't belong to block from block's list of states*)
let make_order_in_classes p_groups  =
	(match !p_groups with c,s ->
	List.iter delete_empty_blocks (c@s));
	sort_groups p_groups;
	(match !p_groups with c,s ->
	List.iter revise_blocks (c@s); 
	p_groups:=(c,s))
;;

(*refine realtion according to positions in symbolic rule trees.. lists.. rules*)
let refine_wrt_possitions sym_rule_p_list p_groups =
	List.iter refine_wrt_one_sr_possitions sym_rule_p_list;
	make_order_in_classes p_groups
;;

let create_c1s_c2s p_sym_rule =
	calculate_counters C1 true p_sym_rule;
	calculate_counters C2 false p_sym_rule
;;

let refine_wrt_one_sr_counters p_sym_rule = 
	let split_if_not_equal p_split_blocks p_cell = 
		if !(pvl(!p_cell.c_c) "refine_wrt_one_sr_counters") = !(pvl(!p_cell.c_c2) "refine_wrt_one_sr_counters") then 
(*		if false then*)
			(*mistake in parosh? c1 x c2 ???*)
(*			print_string "BUM ";*)
			rip_off_state p_split_blocks p_cell 
	in
	let visit_leaf p_leaf = 
		let p_split_blocks = ref [] in
(*		for_all_cells_of_leaf [(split_if_not_equal p_split_blocks);unmark_state] p_leaf;*)
		for_all_cells_of_leaf [(split_if_not_equal p_split_blocks)] p_leaf;
		for_all_cells_of_leaf [unmark_state] p_leaf;
		integrate_split_blocks !p_split_blocks
	in
	List.iter visit_leaf !(!p_sym_rule.sr_leaves)
;;

let refine_wrt_counters sym_rule_list p_groups = 
	List.iter refine_wrt_one_sr_counters sym_rule_list;
	make_order_in_classes p_groups
;;

let update_counters p_sym_rule = 
	let update_cell_counters p_cell = 
		let cell = !p_cell in
		let mark = !(cell.c_state).s_cmarks.(cell.i) in
		if not mark then begin
			!(cell.c_state).s_cmarks.(cell.i) <- true;
			let c = pvl cell.c_c "update_counters1" in
			c:=!c-(!(pvl cell.c_c2 "update_counters2"));
		end;
		cell.c_c:=!(cell.c_c1);(*mistake in parosh? c1 x c2 ???*)
		cell.c_c1:=None;cell.c_c2:=None;
	in

	let visit_leaf p_leaf = for_all_cells_of_leaf [update_cell_counters] p_leaf in	
	List.iter visit_leaf !(!p_sym_rule.sr_leaves); 
	let unmark p_cell = !(!p_cell.c_state).s_cmarks.(!p_cell.i) <- false in
	let unmark_leaf p_leaf = for_all_cells_of_leaf [unmark] p_leaf in
	List.iter unmark_leaf !(!p_sym_rule.sr_leaves)
;;
		
	
(*
#use "/home/holik/ta/univers_compile/bisimin.ml";;
*)
(****************************************************************************************)
(****************************************************************************************)

let print_block p_block = 
	let print_state p_state = 
		print_string (!p_state.s_name^"|") 
	in
	List.iter (function p_state -> print_state p_state) !(!p_block.b_states); 
	print_newline()
;;
let print_group p_group = 
		List.iter (function p_block -> print_block p_block) !(!p_group.g_blocks); 
		print_endline "-------"
;;
let print_relations (compound,solid) =
	print_endline "compound:\n-------"; List.iter print_group compound;
	print_endline "\nsolid:\n-------";List.iter print_group solid
;;

let make_initial_configuration aut =
	match (transofrm_that_fucking_Taml_automaton_to_something_more_fucking aut) 
	with p_init_group,p_basic_sym_rule,rules ->
	calculate_counters C true p_basic_sym_rule;
	let init_p_groups = ref ([p_init_group],[]) in
	refine_wrt_possitions [p_basic_sym_rule] init_p_groups;
	let p_init_sym_rules = ref (connect_one_sr_rules_to_new_sym_rules p_basic_sym_rule) in
	init_p_groups,p_init_sym_rules,rules
;;
	
let choose_G_B p_groups =
	match !p_groups with (compound,solid) -> match compound with p_G::c_tail ->  
	let p_B = match !(!p_G.g_blocks) with 
		first::second::tail -> ( 
		if (!(!first.b_n)) < (!(!second.b_n)) then (!p_G.g_blocks:=second::tail;first) 
	  	else (!p_G.g_blocks:=first::tail;second)) 
		| _ -> failwith "choose_G_B" 
	in
	let p_Bg = new_p_group() in
	p_Bg<<=p_B;
	p_groups:= (if (g_compound p_G) then (p_G::c_tail,p_Bg::solid) else (c_tail,p_G::p_Bg::solid));
	p_Bg,p_G
	| _ -> failwith "choose_G_B"
;;

(*Bg left, nBg right*)
let graft_rule_on_tree p_Bg p_nBg p_rule = 
	
	if !(!p_rule.r_mark) = false then

	let p_tree = !(!(!p_rule.r_symbolic_rule)).sr_tree in
	let p_leaves = !(!(!p_rule.r_symbolic_rule)).sr_leaves in

	let to_leaf tree = 
		let p_leaf = (match tree with 
			Empty -> (
				let p_nl = ref (new_leaf()) in
				p_leaves:=p_nl::!p_leaves;
				p_nl
			) 
			| Leaf p_l -> p_l
			| _-> failwith "graft_rule_on_tree"
		) in 
		connect_to_leaf p_leaf p_rule;
		!p_rule.r_mark:=true;
		Leaf p_leaf
	in

	let in_group p_group p_cell = 
		p_group == pvl(!(pvl(!(!p_cell.c_state).s_block) "in_group1").b_group) "in_group2"
	in
	
	let rec graft tree cells =
		match cells with 
			| [] -> to_leaf tree
			| p_cell::c_tail -> branch_out_or_follow_branch tree p_cell c_tail

	and branch_out_or_follow_branch tree p_cell c_tail = 
		match tree,(in_group p_Bg p_cell),(in_group p_nBg p_cell) with 
		  Node (left,right),true,false -> Node ((graft left c_tail),right)
		| Node (left,right),false,true -> Node (left,(graft right c_tail)) 
		| Empty,false,true ->  Node (Empty,(graft Empty c_tail)) 
		| Empty,true,false ->  Node ((graft Empty c_tail),Empty) 
		| _ -> graft tree c_tail
	in
	
	p_tree:=graft !p_tree !p_rule.r_cells;
;;

let graft_state_rules p_Bg p_nBg p_state = 
	List.iter (graft_rule_on_tree p_Bg p_nBg) !(!p_state.s_rules)
;;

let grow_trees (p_Bg,p_nBg) =
	match !(!p_Bg.g_blocks) with [p_B] ->
	List.iter (graft_state_rules p_Bg p_nBg) !(!p_B.b_states);
	let unmark_state_rules p_state =  List.iter (function p_rule -> !p_rule.r_mark:=false) !(!p_state.s_rules) in
	List.iter unmark_state_rules !(!p_B.b_states)
	| _ -> failwith "grow_trees"
;;
(**************************************)

let rec print_tree tree = 
	match tree with 
	Empty -> print_string "Empty"
	| Leaf _ -> print_string "Leaf"
	| Node (l,r) -> (print_string "Node(";print_tree l;print_string ";";print_tree r;print_string ")";)
;;
let print_sr_trees sr_list =
	let visit_sr p_sr = print_tree !(!p_sr.sr_tree);print_endline "----------" in
	List.iter visit_sr sr_list
;;

let print_cell which p_cell = 
	print_string !(!p_cell.c_state).s_name;
	(match which with C | C1 | C2 -> Printf.printf "[%d]" (match !(counter which p_cell) with Some p_c -> !p_c | _ -> -1);
	| _ -> ());
	print_char ' ' 
;;
let print_rule which p_rule = 
	let r = !p_rule in
	print_string r.r_symbol;print_char '(';
	List.iter (print_cell which) (List.tl r.r_cells);print_string ") -> ";
	print_cell which (List.hd r.r_cells);print_newline();
;;
let print_rules which rules =  List.iter (print_rule which) rules
;;
let print_sr_leaves which p_sym_rule = 
	let visit_leaf p_leaf = List.iter (print_rule which) !(!p_leaf.l_rules);print_endline "---------" in
	List.iter visit_leaf !(!p_sym_rule.sr_leaves);
;;
let print_all_rules which sym_rules =
	List.iter (function p_sr -> (print_sr_leaves which) p_sr;print_endline "*************************") sym_rules	
;;

(*			The Algorithm			*)


(*I am a pig. I create automaton string and then I let Taml to eat this string and spit out the automaton*)
let patch_taml_automaton alphabet rules solid sym_rules =
	let b_repre p_block = 
		match !(!p_block.b_states) with p_state::_ -> p_state | _ -> failwith "b_repre" in
	let g_repre p_group = 
		match !(!p_group.g_blocks) with [p_block] -> b_repre p_block | _-> failwith "g_repre" in
	let s_repre p_state = b_repre (pvl(!p_state.s_block) "patch_automaton") in

	let states = List.map g_repre solid in
	let final_states = List.filter (function p_s -> !p_s.s_final) states in
	let states_str = String.concat " " (List.map (function p_s -> !p_s.s_name) states) in 
	let final_states_str = String.concat " " (List.map (function p_s -> !p_s.s_name) final_states) in

	let choose_rule choosen p_r = 
		if not !(!(!(!p_r.r_symbolic_rule)).sr_mark) then begin
			!(!(!p_r.r_symbolic_rule)).sr_mark := true;
			p_r::choosen
		end else choosen
	in
	let repre_rules = List.fold_left choose_rule [] rules in

	let rule_str p_rule =
		let st_strs = List.map (function p_c -> !(s_repre (!p_c.c_state)).s_name) !p_rule.r_cells in
		let lhs = List.tl st_strs in let rhs = List.hd st_strs in
		match lhs with 
		[] -> Printf.sprintf "%s->%s" (!p_rule.r_symbol) rhs
		| _::_ -> Printf.sprintf "%s(%s)->%s" (!p_rule.r_symbol) (String.concat "," lhs) rhs
	in

	let automaton_str = "States "^states_str^"\nFinal States "^final_states_str^
			"\nTransitions\n"^(String.concat "\n" (List.map rule_str repre_rules)) in
	
	automaton alphabet automaton_str
;;
	(*iteration*)
let iteration p_groups ?(bla=false) p_sym_rules = 
(*	print_endline "\nITERATION:";*)
	let sym_rules = !p_sym_rules in

	let step12() 	= choose_G_B p_groups in 			 (*coresponds to steps 1 and 2 in Parosh*)
	let step3 b_nb	= grow_trees b_nb in 				 (*coresponds to step 3 in Parosh*)
	let step4() 	= List.iter create_c1s_c2s sym_rules in 	 (*coresponds to step 4 in Parosh*)
	let step5() 	= refine_wrt_possitions sym_rules p_groups in  	 (*coresponds to step 5 in Parosh*)
	let step6() 	= refine_wrt_counters sym_rules p_groups in	 (*coresponds to step 6 in Parosh*)
	let step7() 	= List.iter update_counters sym_rules in	 (*coresponds to step 7 in Parosh*)
	let step8() 	= connect_rules_to_new_sym_rules p_sym_rules in	 (*coresponds to step 8 in Parosh*)
			  	 
	let b_nb = step12() in
	step3 b_nb;
	step4();
	step5();
	step6();

	if bla then (
		print_endline "\nSYM_RULES:";
		print_endline "C:";
		print_all_rules C   !p_sym_rules;
		print_endline "C1:";
		print_all_rules C1  !p_sym_rules;
		print_endline "C2:";
		print_all_rules C2  !p_sym_rules;
	);


	step7();
	step8();
;;

(*relations are stable when blocks and determine same relations -- when there is no compound group*)
let relations_stable (compound,solid) = match compound with [] -> true | _ -> false 
;;
(*when all blocks contain exactly one state, there is no chance for minimizing automaton*)
let no_chance (compound,solid) = 
	let is_singleton p_block = !(!p_block.b_n)<2 in
	let contains_only_singletons p_group = List.for_all is_singleton !(!p_group.g_blocks) in
	(List.for_all contains_only_singletons compound) &&  (List.for_all contains_only_singletons solid)
;;
type algortithm_state = God_knows | Relations_stable_hujaja | No_chance
;;
let determine_algorithm_state groups =
	if no_chance groups then No_chance
	else if relations_stable groups then Relations_stable_hujaja
	else God_knows
;;
let count_of_states aut = List.length (State_set.to_list (Automaton.get_states aut))
;;
let bisimin ?(bla=false) aut = 
	match (make_initial_configuration aut) with p_groups,p_sym_rules,rules ->
	let rec do_something() =  

		if(bla) then (
			print_endline "\nRELATIONS:";
			print_relations !p_groups;
			print_endline "\nRULES:";
			print_endline "C:";
			print_rules C rules;
		);

		match (determine_algorithm_state !p_groups) with
		No_chance -> (*print_string "NO_CHANCE\n";*) aut
		| God_knows -> (*print_string "GOD_KNOWS\n";*) iteration ~bla:bla p_groups p_sym_rules;do_something()
		| Relations_stable_hujaja -> print_string "RELATIONS_STABLE_HUJAJA"; 
		patch_taml_automaton (Automaton.get_alphabet aut) rules (snd !p_groups) !p_sym_rules
	in
	do_something()
;;

(*
#use "/home/holik/ta/univers_compile/bisimin.ml";;
*)
