(*some printing functions (usefull for debuging)*)
open Printf
open Taml

let str_state = Term.to_string;;
let print_state s = Format.print_string (str_state s);;

let str_SS set = sprintf "{%s}" (String.concat "," (List.map str_state (FixpointAntichain.SS.elements set)) );;
let print_SS set = Format.print_string (str_SS set);;

let str_SSS sset = sprintf "{%s}" (String.concat "," (List.map str_SS (FixpointAntichain.SSS.elements sset)));;
let print_SSS sset = Format.print_string (str_SSS sset);;

let str_eSS (e,set) = sprintf "(%s,%s)" (str_state e) (str_SS set);;
let print_eSS eset = Format.print_string (str_eSS eset);;

let str_SeSS seset = sprintf "{%s}" (String.concat "," (List.map str_eSS (Incl.Inclusion.AlgAch.EltSet.elements seset)));;
let print_SeSS seset = Format.print_string (str_SeSS seset);;

