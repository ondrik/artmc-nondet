(* Timbuk - Tree Automata completion and Reachability testing 
   Copyright (C) 2000-2004 Thomas Genet and Valérie Viet Triem Tong

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU Library General Public License version 2, as
   published by the Free Software Foundation.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

   See the GNU Library General Public License version 2 for more details
   (enclosed in the file LGPL).


   Version 2.0. Last modification 21/01/04
*)

(* Timbuk - Tree Automata completion and Reachability testing 
   Copyright (C) 2000-2004 Thomas Genet and Valérie Viet Triem Tong

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU Library General Public License version 2, as
   published by the Free Software Foundation.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

   See the GNU Library General Public License version 2 for more details
   (enclosed in the file LGPL).


   Version 2.0. Last modification 21/01/04
*)

(* This is a sample main program to use with the Timbuk library. It simply reads 
   a spec file name given as a parameter of the program and starts a completion 
   with 
   
   - the first TRS of the spec,
   - the first tree automaton of the spec, 
   - the first approximation (if it exists) of the spec (or the approximation whose name
     is given with the option flag --approx
   - no approximation at all if the --noapprox flag is present.

   - static computation of approximation is activated with the --static flag

   - dynamic computation of approximation is activated with the --dynamic flag [default]

   And in DYNAMIC MODE ONLY: 

   - the default completion strategy or a strategy given using the --strat flag followed by
     strategy component names given by priority and chosen among the keywords:
           [exact]           (exact normalisation with prioritary rules)   
           [prior]           (normalisation with prioritary rules)
           [norm_rules]      (normalisation with approximation rules)
           [auto]            (automatic normalisation with new states)
           [auto_conf]       (similar to [auto] but asks for user confirmation first)
           [auto_prior]      (automatic normalisation with new states and new transitions
                              are stored as prioritary transitions)
           [auto_prior_conf] (similar to [auto_prior] but asks for user confirmation first)
           [manual]          (manual normalisation)
           [manual_conf]     (similar to [manual] but asks for user confirmation first)


   and it permits to compute intersections with the completed automaton and all the other
   automata of the specification file (with the (i) command of the completion mechanism.

   Examples:        main --approx Simple --strat norm_rules auto example_comp2.txt
                    main example_comp2.txt
                    main --noapprox --strat auto example_comp2.txt
                    main example_comp.txt
   


   Be careful: static and dynamic automata may not be syntactically equivalent, even if they recognise
   the same language! (If they are different, the dynamic one is the minimalest one)

*)

open Symbol
open Alphabet
open Variable
open Variable_set
open Term
open State_set
open State_content
open Rewrite
open Automaton
open Gamma
open Specification
open Completion

(* module instanciation *)

module MyF= Alphabet(Symbol)
module MyX= Variable_set(Variable)
module Myterm=Term(Symbol)(MyF)(Variable)(MyX)
module Mytrs= RewriteSystem(MyF)(MyX)(Myterm)
module MyQ= State_set(Symbol)(MyF)(Myterm)(State_content)
module Myautomaton= TreeAutomata(Symbol)(MyF)(Variable)(Myterm)(State_content)(Mytrs)(MyQ)
module MyGamma= Gamma(Symbol)(MyF)(Variable)(MyX)(Myterm)(Mytrs)(MyQ)(Myautomaton)
module Myspec= Specification(MyF)(MyX)(Myterm)(Mytrs)(Myautomaton)(MyGamma)
module MyComp = Completion(Variable)(Symbol)(MyF)(MyX)(Myterm)(Mytrs)(MyQ)(Myautomaton)
		  (Myspec)(MyGamma)


(* configuration of the garbage collector for lowest memory usage *)

let new_gc_control= {Gc.minor_heap_size=32768; Gc.major_heap_increment=63488;
 Gc.space_overhead=42; Gc.verbose=0; Gc.max_overhead=10;
 Gc.stack_limit=262144;Gc.allocation_policy=0};;
Gc.set new_gc_control;;


let usage= ("Usage: "^Sys.argv.(0)^" [options] [specification file name]
Options: --dynamic        for usual completion algorithm (default)
         --static         to activate the static compilation of matching and 
                          normalisation (needs a complete set of prior and 
                          norm rules) 
         --fstatic        to activate the static compilation of matching and 
                          normalisation. If the set of prior and norm rules is
                          not complete, a transition not covered by the rules is
                          normalised using a single new state #qstatic#
         --approx A       where A is an approximation name of the specification
                          (default: the first one is used)
         --noapprox       to ignore the approximations in the specification
         -f file          to read timbuk commands from a file
         -o file          output timbuk execution trace in a file

         IN DYNAMIC MODE ONLY:

         --strat followed by keywords:
           exact           (exact normalisation, see documentation for TRS 
                            classes)
           prior           (normalisation with prioritary rules)
           norm_rules      (normalisation with approximation rules)
           auto            (automatic normalisation with new states)
           auto_conf       (similar to 'auto' but asks for confirmation first)
           auto_prior      (automatic normalisation with new states where
                            new transitions are stored as prioritary rules)

           auto_prior_conf (similar to 'auto_prior' but asks for confirmation 
                            first)
           manual_norm     (manual addition of normalisation rules)
           manual_norm_conf(similar to 'manual_norm' but asks for confirmation 
                            first)
           manual          (manual normalisation)
           manual_conf     (similar to 'manual' but asks for confirmation first)
");;
let arg_number= Array.length Sys.argv;;
let approx= ref "";;
let error= ref false;;
let static= ref "dynamic";;
let i= ref 1;;
let in_strat= ref false;;
let strat= ref  ["prior"; "norm_rules"; "manual_norm_conf"; "auto_conf"];;
let possible_strat_names= ["exact";"prior"; "norm_rules"; "manual"; "manual_conf"; "auto"; "auto_conf";
			   "auto_prior"; "auto_prior_conf"; "manual_norm"; "manual_norm_conf"];;

let commandsin= ref "";;
let outfile= ref "";;

if arg_number<=1 then print_string usage
else 
  begin
    while not !error && !i<arg_number-1 do
      match Sys.argv.(!i) with
	| "-f" -> 
	    if !i+1=arg_number-1 
	    then 
	      begin
		print_string ("Missing command file name!\n");
		print_string usage;
		error := true
	      end
	    else
	      begin
		commandsin:= Sys.argv.(!i+1);
		i:= !i+2
	      end
	| "-o" -> 
	    if !i+1=arg_number-1 
	    then 
	      begin
		print_string ("Missing out file name!\n");
		print_string usage;
		error := true
	      end
	    else
	      begin
		outfile:= Sys.argv.(!i+1);
		i:= !i+2
	      end
	| "--approx" ->
	    if !in_strat then in_strat:=false else ();
	    approx := Sys.argv.(!i+1);
	    i:=!i+2
	| "--noapprox" -> 
	    if !in_strat then in_strat:=false else ();
	    approx := "##NOAPPROX##";
	    i:=!i+1
	| "--strat" -> 
	    in_strat:= true;
	    strat:=[];
	  i:= !i+1
	    
	| "--static" -> 
	    static:= "static";
	    i:= !i +1 
	| "--fstatic" -> 
	    static:= "forced static";
	    i:= !i +1 
	| "--dynamic" -> 
	    static:= "dynamic";
	    i:= !i+1
	| s -> 
	    if List.mem s possible_strat_names
	    then
	      if !in_strat 
	      then 
		begin
		  strat:= List.append !strat [s];
		  i:=!i +1
		end
	      else
		begin
		  print_string ("Strategy component "^s^" is not preceeded by --strat!"^"\n");
		  print_string usage;
		error:= true
	      end
	    else 
	      begin
		print_string ("Error on : "^s^"\n");
		print_string usage;
		error:= true
	      end
    done;
    if not !error then
      try(
	let _= if not (!outfile="") then 
	  let ochan= open_out !outfile in 
	    (MyGamma.out_chan:= ochan;
	     MyComp.out_chan:= ochan) in
	let _= if not (!commandsin="") then 
	  let ichan=  open_in !commandsin in
	    (MyGamma.in_chan:= ichan;
	     MyComp.in_chan:= ichan) in
	  (* parsing of the specification file *)
	let s= Myspec.file_parse (Sys.argv.(arg_number-1)) in
	
      (* extraction of named trs, automata and approximations: i.e. lists of pairs
	 (name, object) *)
	
      let ltrs= Myspec.get_list_trs s in
      let laut= Myspec.get_list_automata s in
      let lapprox= Myspec.get_list_approximation s in
	if ltrs=[] then Printf.fprintf !MyGamma.out_chan "%s" "Missing term rewriting system in the specification"
	else 
	  if laut=[] then Printf.fprintf !MyGamma.out_chan "%s" "Missing tree automaton in the specification"
	  else 
	    let (_, trs)=List.hd ltrs in
	    let (init_name, aut)=List.hd laut in
	    let app=
	      if not (!approx = "" or  !approx="##NOAPPROX##") then 
		(* if an approximation has been given on the command line, we use it *)
		Myspec.get_approximation !approx s
	      else 
		if (lapprox=[] or !approx="##NOAPPROX##")
		  (* if there is no approximation in the file or the --noapprox flag
		     has been used then we use the empty approximation *)
		then MyGamma.empty
		  (* we use the first approximation of the file *)
		else ((function x,y -> y)(List.hd lapprox))
	    in
	    let aut_completed=  MyComp.complet trs aut (MyGamma.set_strategy !strat app) (List.tl laut) !static (Myspec.get_variables s) init_name in
	      Myautomaton.print aut_completed
      )
      with 
	  Stream.Failure -> Printf.fprintf !MyGamma.out_chan "%s" ("\n\nError: Bad specification file!\n")
	| Stream.Error s -> Printf.fprintf !MyGamma.out_chan "%s" ("\n\nError: Bad specification file!\n"^s)
	| MyF.Multiply_defined_symbol(f) -> Printf.fprintf !MyGamma.out_chan "%s" ("\n\nError: Symbol "^f^" is defined several times\n")
	| Myterm.Undefined_symbol(f) -> Printf.fprintf !MyGamma.out_chan "%s" ("\n\nError: Symbol "^f^" is undefined\n")
	| Myterm.Badly_formed_term(f) -> Printf.fprintf !MyGamma.out_chan "%s" ("\n\nError: Bad term syntax! "^f^"\n")
	| Myspec.Name_used_twice (s) -> Printf.fprintf !MyGamma.out_chan "%s" ("\n\nError: Identifier(s) "^s^" used several times\n")
	| Mytrs.Badly_formed_rule(f) -> Printf.fprintf !MyGamma.out_chan "%s" ("\n\nError: Bad rule syntax! "^f^"\n")
	| Myspec.No_name(s) -> Printf.fprintf !MyGamma.out_chan "%s" ("\n\nError: "^s^"\n")
	| MyGamma.Normalisation_error(s) -> Printf.fprintf !MyGamma.out_chan "%s" ("\n\nError: "^s^"\n")
	| MyGamma.Error_in_parsing(s) -> Printf.fprintf !MyGamma.out_chan "%s" ("\n\nError: "^s^"\n")
	| Myautomaton.Normalisation_problem(s) -> Printf.fprintf !MyGamma.out_chan "%s" ("\n\nError: "^s^"\n")
	| Myspec.No_approximation_of_that_name(s) -> Printf.fprintf !MyGamma.out_chan "%s" ("\n\nError: no approximation named "^s^" in the specification file.\n")
	| Sys_error (s) -> Printf.fprintf !MyGamma.out_chan "%s" ("\nError: "^s^"\n")

    else ()
  end
  
  
