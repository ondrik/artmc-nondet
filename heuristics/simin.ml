open TreeSimLTS

let print_time str func arg = print_string str;flush_all(); Mess.print_running_time func arg



let downward taml_aut =
	let aut = Interim.of_taml taml_aut in
	let downsim = Simulation.downward aut in
(*        let check = Simplesim.Downward.simulation aut in*)
(*        if downsim <> check then failwith"downward simulation wrong";*)
	Interim.to_taml (Merge.New.merge aut downsim)



let composed taml_aut =
	let aut = Interim.of_taml taml_aut in
	let downsim = Simulation.downward aut in
	let upsim = Simulation.upward downsim aut in
(*        let check = Simplesim.Upward.simulation aut downsim in*)
(*        if upsim <> check then failwith"upward simulation wrong";*)
	let usefull = Relation.usefull downsim upsim in
        let res  = Interim.to_taml (Merge.New.merge aut usefull) in
(*        if not (Heuristics.are_equiv res taml_aut) then failwith"hmmm...";*)
(*        print_endline "ok";flush_all();*)
        res

(*	this is supposed to be incorrect*)
let upward taml_aut = 
	let aut = Interim.of_taml taml_aut in
	let downsim = Simulation.downward aut in
	let upsim = Simulation.upward downsim aut in
(*	print_int (Relation.cardinality upsim);*)
	Interim.to_taml (Merge.New.merge aut upsim)


let downward_bisim taml_aut =
	let aut = Interim.of_taml taml_aut in
	let bis = Simplesim.Downward.bisimulation aut in
	Interim.to_taml (Merge.New.merge aut bis)

let upward_bisim_id taml_aut =
	let aut = Interim.of_taml taml_aut in
	let bis = Simplesim.Upward.bisimulation (Relation.identity (Array.length aut.Interim.a_states)) aut in
	Interim.to_taml (Merge.New.merge aut bis)


let composed_bisim taml_aut =
	let aut = Interim.of_taml taml_aut in
	let downbis = Simplesim.Downward.bisimulation aut in
	let upbis = Simplesim.Upward.bisimulation downbis aut in
	let usefull = Relation.usefull downbis upbis in
        let res  = Interim.to_taml (Merge.New.merge aut usefull) in
        res

type reltype = Sim | Bis | Id
let composition downtype uptype taml_aut = 
	let downward =  match downtype with
		Id -> fun a -> Relation.identity (Array.length a.Interim.a_states)
		| Bis -> Simplesim.Downward.bisimulation
		| Sim -> Simulation.downward
	in
	let upward = match uptype with
		Id -> fun _ a -> Relation.identity (Array.length a.Interim.a_states)
		| Bis -> Simplesim.Upward.bisimulation
		| Sim -> Simulation.upward
	in
	let a = Interim.of_taml taml_aut in
	let drel = downward a in
	let urel = upward drel a in
    (*print_newline();*)
    (*Mess.print_bool_matrix drel;*)
    (*print_newline();*)
    (*print_newline();*)
    (*Mess.print_bool_matrix urel;*)
    (*print_newline();*)
    (*print_newline();*)
	let usefull = Relation.usefull drel urel in
    (*Mess.print_bool_matrix usefull;*)
    (*print_newline();*)
	Interim.to_taml (Merge.New.merge a usefull)

let reltype_to_string = function 
		Id -> "ID" 
		| Bis -> "BIS" 
		| Sim -> "SIM" 







