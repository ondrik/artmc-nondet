open Interim

module New = struct
	let get_equivalence_blocks preorder = 
		let members = Array.mapi (fun i _ -> i) preorder in
		let rec get_blocks rest_of_members blocks =
			match rest_of_members with
			[] -> blocks
			| x:: _ ->
				let newblock,rest_of_rest = List.partition (fun y ->
					preorder.(x).(y)&&preorder.(y).(x)) rest_of_members
				in
				get_blocks rest_of_rest (newblock::blocks)
		in
		get_blocks (Array.to_list members) []
	
	let print_relation_on_blocks preorder blocks states =
		let block_to_string block = Printf.sprintf "{%s}" (String.concat " " (List.map (fun q -> states.(q).s_name) block)) in
		let above block1 block2 = preorder.(List.hd block1).(List.hd block2) in
		List.iter (function block -> 
			let above_list = List.filter (above block) blocks in
			Printf.printf "%s < %s\n" (block_to_string block) (String.concat " " (List.map block_to_string above_list))
		) blocks 


	let print_blocks blocks states =
		let block_to_string block = Printf.sprintf "{%s}" (String.concat " " (List.map (fun q -> states.(q).s_name) block)) in
		Printf.printf "%s" (String.concat " " (List.map block_to_string blocks))

	let get_representants blocks states =
		let representants = ref [] in
		let represented_by = Array.make (Array.length states) (-1) in
		let process_block i block =
			let {s_name=name;s_final=final} = states.( 
				try List.find (fun q -> states.(q).s_final) block
				with Not_found -> List.hd block )
			in
			representants:={s_name=name;s_final=final;s_index=i}::!representants;
			List.iter (function q -> represented_by.(q) <- i) block
		in
		let _ = List.fold_left (fun i block -> process_block i block; i+1) 0 blocks in
		Array.of_list (List.rev !representants),represented_by
	
	let merge_rules rules repre_states represented_by =
		let get_repre_lhs lhs = 
			Array.map (function q -> represented_by.(q)) lhs
		in
      let get_repre_rhs q = represented_by.(q) in
      let with_duplicities = List.map (function {r_rhs=rhs;r_lhs=lhs;r_symbol=symbol} ->
         {r_lhs=get_repre_lhs lhs; r_rhs=get_repre_rhs rhs; r_symbol=symbol}
		) rules in
		let splited = sort_and_split compare with_duplicities in
		List.map (fun rl -> List.hd rl) splited

	let merge aut preorder =
		let blocks = get_equivalence_blocks preorder in
(*		print_relation_on_blocks preorder blocks aut.a_states;*)
(*		print_blocks blocks aut.a_states;*)
		let repre_states,represented_by = get_representants blocks aut.a_states in
		let repre_rules = merge_rules aut.a_rules repre_states represented_by in
		{a_rules=repre_rules;a_states=repre_states;a_alphabet=aut.a_alphabet}
end

(*
let get_equivalence_blocks preorder =
	let block = Array.mapi (fun i a -> i) preorder in
	let l = Array.length preorder in
	for i = 0 to l-1 do
		if block.(i) = i then (
			for j = i to l-1 do
				if preorder.(i).(j) && preorder.(j).(i) then
					block.(j) <- i
			done
		)
	done;
(*Printf.printf "[[%s]]" (String.concat ";" (List.map string_of_int
 * (Array.to_list block)));*)
	block

let get_repre_states blocks states =
	let repre = ref [] in
	for i = 0 to (Array.length blocks)-1 do
		if blocks.(i) = i then 
			repre:=states.(i)::!repre
	done;
	Array.of_list !repre


let get_repre_rules sblocks states rules =
	let get_rhslhs_repre rhslhs =
		Array.map (fun q ->
			ref (states.(sblocks.(!q.s_index)))
		) rhslhs
	in
	let get_repre_rule r =
		let nr =
			{
				r_symbol = r.r_symbol;
				r_rhslhs = get_rhslhs_repre r.r_rhslhs;
			}
		in
(*		let sr = (rule_to_string r) in*)
(*		let snr = (rule_to_string nr) in*)
(*		Printf.printf "%s ... %s %s\n" sr snr  (if sr=snr then "OK" else "UAAA");*)
		nr
	in
	let repre_rules = List.map get_repre_rule rules in
	let splited = sort_and_split compare repre_rules in
	List.map (fun rl -> List.hd rl) splited



let merge_states aut blocks = 
	{
		a_alphabet = aut.a_alphabet;
		a_states = get_repre_states blocks aut.a_states;
		a_rules = get_repre_rules blocks aut.a_states aut.a_rules
	}
*)
