(*
open Taml.Automaton
let print_time str func arg = print_string str;flush_all(); Mess.print_running_time func arg
let utility_cleaning aut = print_time "util" utility_cleaning aut
let accessibility_cleaning aut = print_time "access" accessibility_cleaning aut
let automatic_renum aut = print_time "automatic_renum"automatic_renum aut
let clean a = utility_cleaning (accessibility_cleaning a)
let simplify a = automatic_renum (clean a)
*)

let print_time str func arg = 
   print_string str;flush_all(); 
   let res = Mess.print_running_time func arg in
   print_string (Mess.aut_size_str res);
   res

let simplify a = 
   let st = print_time "sim-Taml" Taml.Automaton.simplify a in
   let si = print_time "sim-Inte" Interim.simplify_taml a in
   if not (Heuristics.are_equiv st si) then failwith"je to v rici";
   si
