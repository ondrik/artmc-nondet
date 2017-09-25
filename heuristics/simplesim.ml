open Interim
type whichRel = Sim | Bis

module Upward = struct
	let simulated_by drel urel j
	{r_symbol = symbol1; r_lhs = lhs1; r_rhs = rhs1} 
	{r_symbol = symbol2; r_lhs = lhs2; r_rhs = rhs2} =
		if symbol1 <> symbol2 then false
		else
			let ok = ref true in
			for i=0 to Array.length lhs1 - 1 do
				if j<>i && (not drel.(lhs1.(i)).(lhs2.(i))) then ok:=false
			done;
			!ok && urel.(rhs1).(rhs2)

	let check_pair_wrt_rule rules drel urel (q,r) rule1 =
		let n = Array.length rule1.r_lhs in
		let ok = ref true in
		for j=0 to n-1 do
			if rule1.r_lhs.(j) = q then
				ok := !ok && List.exists (fun rule2 -> (simulated_by drel urel j rule1 rule2)  && rule2.r_lhs.(j) = r) rules
		done;
		!ok

	let check_pair rules drel urel (q,r) =
		List.for_all (check_pair_wrt_rule rules drel urel (q,r)) rules

	let iteration rules drel urel which_rel =
		let change = ref false in
		let n = Array.length urel in
		for q=0 to n-1 do
			for r=0 to n-1 do
				if urel.(q).(r) then 
					if not (check_pair rules drel urel (q,r)) then (
						urel.(q).(r)<-false;
						if which_rel = Bis then urel.(r).(q)<-false;
						change := true
					)
			done
		done;
		!change

	let simulation drel aut =
		let n = Array.length aut.a_states in
		let urel = Array.make_matrix n n true in
		for q=0 to n-1 do
			for r=0 to n-1 do
				if aut.a_states.(q).s_final && not aut.a_states.(r).s_final then (urel.(q).(r)<-false; urel.(r).(q)<-false)
			done
		done;
		while (iteration aut.a_rules drel urel Sim) do () done;
		urel

	let bisimulation drel aut =
		let n = Array.length aut.a_states in
		let urel = Array.make_matrix n n true in
		for q=0 to n-1 do
			for r=0 to n-1 do
				if aut.a_states.(q).s_final && not aut.a_states.(r).s_final then (urel.(q).(r)<-false;urel.(r).(q)<-false)

			done
		done;
		while (iteration aut.a_rules drel urel Bis) do () done;
		urel
end;;

module Downward = struct
	let simulated_by rel  
		{r_symbol = symbol1; r_lhs = lhs1} 
		{r_symbol = symbol2; r_lhs = lhs2} =
		if symbol1 <> symbol2 then false
		else
			let ok = ref true in
			for i=0 to Array.length lhs1 - 1 do
				if not rel.(lhs1.(i)).(lhs2.(i)) then ok:=false
			done;
			!ok
		
	let check_pair_wrt_rule rules rel (q,r) rule1 =
		if rule1.r_rhs != q then true else
		List.exists (fun rule2 -> rule2.r_rhs = r && (simulated_by rel rule1 rule2)) rules

	let check_pair rules rel (q,r) =
		List.for_all (check_pair_wrt_rule rules rel (q,r)) rules

	let iteration rules rel which_rel =
		let change = ref false in
		let n = Array.length rel in
		for q=0 to n-1 do
			for r=0 to n-1 do
				if rel.(q).(r) then 
					if not (check_pair rules rel (q,r)) then (
						rel.(q).(r)<-false;
						if which_rel = Bis then rel.(r).(q)<-false;
						change := true
					)
			done
		done;
		!change

	let simulation aut =
		let n = Array.length aut.a_states in
		let rel = Array.make_matrix  n n true in
		while (iteration aut.a_rules rel Sim) do () done;
		rel

	let bisimulation aut =
		let n = Array.length aut.a_states in
		let rel = Array.make_matrix  n n true in
		while (iteration aut.a_rules rel Bis) do () done;
		rel
end;;

