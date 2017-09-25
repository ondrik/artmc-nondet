open Taml
open FixpointAntichain

(*module StateSet = SS*)
module StateSet = struct 
	include Set.Make(OrderedState)
	let smaller = subset
	let bigger a b = subset b a
end;;

(*universality checking algorithm*)

(*inclusion checking algorithm - I have to create antichain element = (state,StateSet)*)
module StateStateSetF (StSe:STATE_SET) = struct
	module StateSet = StSe
	type t = StateSet.elt * StateSet.t
	type elt = StateSet.elt
	let compare eset1 eset2 = match (eset1,eset2) with ((e1,set1),(e2,set2)) -> 
		if e1 = e2 then StateSet.compare set1 set2 else compare e1 e2
	let smaller eset1 eset2 = match (eset1,eset2) with ((e1,set1),(e2,set2)) -> 
		if e1 = e2 then StateSet.smaller set1 set2 else false 
	let bigger a b = smaller b a
end;;


(**************************************************************************************)
(* antichains with simulations*)
(**************************************************************************************)

module Sim = struct
	let simulation = ref [||] (*this value has to be initialized before the first use of the module, an ugly global variable!!*)
	let (<<) q r = !simulation.(q).(r)

	module StateSet = struct
		include List
		type elt = int
		type t = elt list
		let compare = compare
		let add q s = q::s
		let smaller s1 s2 = for_all (fun q -> exists (fun r -> q << r) s2) s1 
		let bigger s1 s2 = smaller s2 s1 
		let add q s = if not (exists (fun r -> q << r) s) then add q s else s
		let empty = []
(*		let fold = fold_right*)
		let fold f l i = 
			let g a b = f b a in
			fold_left g i l
	end;;

	module StateStateSetF (StSet:STATE_SET) =
		struct
		include List
		module StateSet = StSet
		type t = StateSet.elt * StateSet.t
		type elt = StateSet.elt
		let compare = compare
		let smaller (q,s1) (r,s2) = 
			(StateSet.exists (fun s -> r << s) s2) ||	
			((r << q) && (StateSet.smaller s1 s2)) 
		let bigger x y = smaller y x
	end;;
end;;

