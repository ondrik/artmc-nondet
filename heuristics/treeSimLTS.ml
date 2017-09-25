open HHK

module Translation = 
struct
	let downward aut = 
		let fvectors_list = Interim.get_vectors aut in
		let vector_list = List.concat fvectors_list in
		let aut_states = Array.length aut.Interim.a_states in
		let aut_vectors = List.length vector_list in
		let states = aut_states + aut_vectors in
		let symbols = Interim.rank aut + 1 in
		LTS.create aut_states symbols states;
		
		let vIndex = ref aut_states in 
		List.iter (fun v ->
			(*rhs -> vector transitions*)
			List.iter (fun q ->
				LTS.add_transition q (symbols-1) !vIndex;
			) v.Interim.v_rhs
			;
			(*vector v -> v(i) transitions*)
			Array.iteri (fun i q ->
				LTS.add_transition !vIndex i q
			) v.Interim.v_lhs
			;
			incr(vIndex)
		) vector_list
		;

		Relation.create ();
		Relation.add_square 0 aut_states true;
		let _ = List.fold_left (fun s fvectors -> 
			let d=List.length fvectors in 
			Relation.add_square s d true;
			s+d
		) aut_states fvectors_list in
		()

	let environment_of_rule {Interim.r_symbol = f;Interim.r_rhs = rhs;Interim.r_lhs = lhs} hole =
		let lhs = snd (Array.fold_left 
			(fun (i,lhs_tmp) q -> 
				if hole<>i then (i+1,q::lhs_tmp)
				else (i+1,lhs_tmp)
		) (0,[]) lhs)
		in
		f,lhs,rhs (*symbol,left-hand side, right-hand side*)


	(*environments contains symbol but not the position of hole -- this is transfered to edges*)
	module OrderedEnvironment = 
	struct
		type t = (int*int list*int)
		let compare (f1,lhs1,rhs1) (f2,lhs2,rhs2) = 
			let cmpf = compare f1 f2 in
			if cmpf<>0 then cmpf 
			else compare (lhs1,rhs1) (lhs2,rhs2)
	end

	module EnvironmentMap = Map.Make(OrderedEnvironment)

	let upward downsim aut = 
		let aut_rank = Interim.rank aut in
		let aut_states_count = Array.length aut.Interim.a_states in
		(*inrhs.(q) --- list of environmets of which q is rhs*)
		let inrhsof = Array.make aut_states_count [] in
		(*inholes.(q).(i) ---list of environments e such that q is in the ith hole of e*)
		let inholeof = Array.make_matrix aut_states_count aut_rank [] in

		(*create set of environments and save info about transitions into inholoef and inrhsof*)
		let total_of_environments, all_environments = List.fold_left (fun (env_count,environments) rule  ->
			let rank = Array.length rule.Interim.r_lhs in
			let rec envs_for_holes h (env_c,envs) = (*process one rule (all hole positions)*)
				if h = rank then
					(env_c,envs)
				else (
					let (f,lhs,rhs) = environment_of_rule rule h in
					let current,new_env_count,new_envs =
						try 
							((EnvironmentMap.find (f,lhs,rhs) envs), env_c, envs)
						with Not_found -> ( (*if env. is new then add it into the set and incr. count of env.*)
							let new_env = env_c+aut_states_count in
							inrhsof.(rhs) <- new_env::inrhsof.(rhs);
							new_env,(env_c+1),(EnvironmentMap.add (f,lhs,rhs) (new_env) envs)
						)
					in
					let q = rule.Interim.r_lhs.(h) in
					inholeof.(q).(h) <- current::inholeof.(q).(h);
					envs_for_holes (h+1) (new_env_count,new_envs)
				)
			in
			(envs_for_holes 0 (env_count,environments))
		) (0,EnvironmentMap.empty) (List.sort (Interim.rule_comparator Interim.By_symbol) aut.Interim.a_rules) 
		(*I need to have environments grouped by symbol*)
		in

		(*create LTS*)
		LTS.create aut_states_count (aut_rank+1) (total_of_environments+aut_states_count);
		Array.iteri (fun q envs ->
			List.iter (function e -> 
				LTS.add_transition e aut_rank q
			) envs
		) inrhsof
		;
		Array.iteri (fun q hole_array ->
			Array.iteri (fun h envs ->
				List.iter (function e ->  
					LTS.add_transition q h e
				) envs
			) hole_array
		) inholeof
		;

		(*initialize Relation*)
		Relation.create ();
		Relation.add_square 0 aut_states_count false;

		(*final states superiority*)
		for q = 0 to aut_states_count-1 do
			for r = 0 to aut_states_count-1 do
				if aut.Interim.a_states.(r).Interim.s_final 
				|| not aut.Interim.a_states.(q).Interim.s_final then
					Relation.add_rel q r 
			done
		done
		;

		(*initial relation on lhs*)
		let in_init_simulation (f1,lhs1,rhs1) (f2,lhs2,rhs2) =
			f1=f2 && List.fold_left2 (fun tmp q r -> tmp && downsim.(q).(r)) true lhs1 lhs2
		in

		(*compute initial simulation only for environments with the same symbol (else let there false)*)
		let set_init_simulations env_list =
			let least_index = List.fold_left (fun min (_,i) -> if (min > i) || (min < 0) then i else min) (-1) env_list in
			let l = (List.length env_list) in
			if (List.exists (function (_,i) -> i > least_index + (l-1)) env_list) then failwith"sakra";
			Relation.add_square least_index (List.length env_list) false;
			List.iter (fun (e1,i1) ->
				List.iter (fun (e2,i2) ->
					if in_init_simulation e1 e2 then Relation.add_rel i1 i2
				)env_list
			)env_list
		in

		(*Wanderer, don't try to understand this.*)
		set_init_simulations(snd( (*process also the last group of envs.!*)
		EnvironmentMap.fold (fun e index (current_f,envs) ->
			match e with (f,_,_) ->
			if current_f<>f then (
				set_init_simulations envs;
				(f,[(e,index)])
			)
			else (f,(e,index)::envs)
		) all_environments (-1,[])
		));
end

module Simulation = 
struct
	let general translation aut =
		translation aut;
		initialization ();
		computation ();
		Relation.get_first_matrix () 	
	let downward = general Translation.downward
	let upward downsim aut = general (Translation.upward downsim) aut
end
      

