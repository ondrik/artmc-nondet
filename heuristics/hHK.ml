let print_array a =
	Printf.printf "[|%s|]" (String.concat ";" (Array.to_list (Array.map string_of_int a)))

let print_list l = Printf.printf"[%s]" (String.concat "," (List.map string_of_int l))

module LTS =
   struct
      let lts = ref [||]
      let pre q a = !lts.(a).(q)
		let border = ref 0 (*for a bipartite LTS, this is the first index of the second partition*)
      let create first_index_of_second_part symbols states = 
			border := first_index_of_second_part;
         lts := Array.make_matrix symbols states []
		let symbols () = Array.length !lts
		let states () = Array.length !lts.(0)
		let add_transition q a r = 
	      !lts.(a).(r) <- (q::(!lts.(a).(r)))

		let shift q = if q < !border then q else q - !border

		let leadsto a set =
			let leadstoarray =  match set with 
				[] -> [||]
				| r::_ -> 					
					if r < !border then (*why < ... ?*)
						Array.make ((states())-(!border)) 0
					else
						Array.make !border 0
			in

			List.iter (function r ->
				List.iter (function q -> leadstoarray.(shift q) <- leadstoarray.(shift q) + 1
				) (pre r a)
			) set
			;
			leadstoarray

		let print () =
			Array.iteri (fun a pre_a ->
				Array.iteri (fun q pre_a_q ->
					List.iter (function r ->
						Printf.printf "%d --%d--> %d\n" r a q
					) pre_a_q
				) pre_a
			) !lts
   end

module Counter =
   struct
      let counters = ref [||]
      let create () = counters := Array.make_matrix  (LTS.states ()) (LTS.symbols ()) [||]
      let is_zero q a r = !counters.(r).(a).(LTS.shift q) = 0
      let add q a r value = !counters.(r).(a).(LTS.shift q) <- !counters.(r).(a).(LTS.shift q) + value
      let dec q a r = add q a r (-1)
		let set a r counterarray = !counters.(r).(a) <- counterarray (*bacha!*)
   end

(*   a counter of comparisons, for degiing reasons, to be removed remove *)
let comparisons =  ref 0

module Relation =
	struct
		let plan = ref [||]
		let print_plan _ = print_string "Plan: ";Array.iter (function (m,i) -> Printf.printf "(%d,%d)" (Array.length m) i) !plan
		let create _ = plan := Array.make (LTS.states ()) ([||],-1)
		let add_square from n value = 
			let new_matrix = Array.make_matrix n n value in
			for i = from to (n+from-1) do
				!plan.(i) <- (new_matrix,i-from)
			done
		let get_location q r = (*TODO: simplify later*)
			let (mq,iq) = !plan.(q) in
			let (mr,ir) = !plan.(r) in
			mq,mr,iq,ir
		let rm_rel q r = 
			let m,mr,iq,ir = get_location q r in
			if m!=mr then failwith"rm_rel" else
			m.(iq).(ir) <- false
		let add_rel q r = 			
			let m,mr,iq,ir = get_location q r in
			if m!=mr then failwith"add_rel" else
			m.(iq).(ir) <- true
		let in_rel q r = 
            incr comparisons; (*just incrementing the number of
            comparisons, for debuging reasons, to be removed*)
			let m,mr,iq,ir = get_location q r in
			if m!=mr then false else 
			m.(iq).(ir)
		let above q = 
			let (m,iq) = !plan.(q) in
			let diff = q - iq in
			fst (
				Array.fold_left (
					fun (above_list,i) value -> 
						if value then (i+diff::above_list,i+1) else (above_list,i+1)
				)  ([],0) m.(iq)
			)
		let get_first_matrix _ = 
			match !plan with 
			[||] -> [||]
			| _ -> fst !plan.(0)
	end
		
module Remove =
	struct
		let removes = ref [||]
		let create () =
         removes := Array.make_matrix (LTS.symbols ())  (LTS.states ()) []
		let set q a set = !removes.(a).(q) <- set 
		let get q a = !removes.(a).(q)
		let add q a r = !removes.(a).(q) <- (r::(!removes.(a).(q)))
		let empty q a = !removes.(a).(q) <- []
		let is_empty q a =  !removes.(a).(q) = []
	end


let initialization () =
	(*I suppose that Relation is initialized*)
	let rulesn = Array.fold_left (fun tmp a_part -> Array.fold_left (fun tmp2 rules -> List.length rules + tmp2) tmp a_part) 0 !LTS.lts in
	Remove.create (); Counter.create ();

	let init_counters_and_removes a (f1,l1) (f2,l2) = 
		for r =  f1 to l1  do
			let lead_under_a_above_r = LTS.leadsto a (Relation.above r) in
			Counter.set a r lead_under_a_above_r;
			for q = f2  to l2 do 
				if Counter.is_zero q a r then Remove.add r a q;
			done
		done
	in

	for a = 0 to LTS.symbols()-1 do
		init_counters_and_removes a (0,!LTS.border-1) (!LTS.border,LTS.states()-1);
		init_counters_and_removes a (!LTS.border,LTS.states()-1)(0,!LTS.border-1)
	done


let loop_passes =  ref 0
let inner_loop_passes =  ref 0

let computation () =
	let nonempty_removes = ref [] in
	for a = 0 to LTS.symbols()-1 do
		for q = 0 to LTS.states()-1 do
			if not (Remove.is_empty q a) then
				nonempty_removes:=(q,a)::!nonempty_removes
		done
	done;

	while !nonempty_removes<>[] do
		match !nonempty_removes with (q,a)::tail -> 
                incr(loop_passes);
			nonempty_removes := tail;
			let remove = Remove.get q a in
			Remove.empty q a;
			List.iter (function r ->
				List.iter (function s ->
                        if (s < !LTS.border) then
                incr(inner_loop_passes);
					if Relation.in_rel r s then (
						Relation.rm_rel r s;
						for b=0 to LTS.symbols()-1 do
							List.iter (function t ->
								Counter.dec t b r;
								if Counter.is_zero t b r then (
									if Remove.is_empty r b then
										nonempty_removes:=(r,b)::!nonempty_removes;
									Remove.add r b t
								)
							) (LTS.pre s b)
						done
					)
				) remove
			) (LTS.pre q a)
		| _-> ()
    done
        ;;
    (*print_newline();*)
    (*print_int (!comparisons);*)
    (*print_newline();*)
    (*print_int (!loop_passes);*)
    (*print_newline();*)
    (*print_int (!inner_loop_passes);*)
    (*print_newline()*)
	

