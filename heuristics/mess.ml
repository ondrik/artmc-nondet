(*some mess, printing functions and so on*)
open Taml;;
open Unix;;

(*********************************************************************************************)
(*********************************************************************************************)
(*********************************************************************************************)
let bool_array_to_string a = String.concat "" (Array.to_list (Array.map (fun x -> if x then  "1" else "0") a))

let int_array_to_string a = String.concat  " " (Array.to_list (Array.map string_of_int a))

let bool_matrix_to_string m = String.concat "\n" (Array.to_list (Array.map bool_array_to_string m))

let print_bool_matrix m = print_string (bool_matrix_to_string m)
(*let print_bool_matrix m = ()*)

let print_bool = function true -> print_string "true" | false -> print_string "false";;

let aut_num_states aut = List.length (State_set.to_list (Automaton.get_states aut));;
let aut_num_trans aut = List.length (Rewrite.to_list (Automaton.get_transitions aut));;

let aut_size_str aut = 
  Printf.sprintf "[%d,%d]" (aut_num_states aut) (aut_num_trans aut);;
let print_aut_size aut = print_string (aut_size_str aut);;

let print_running_time f x =
	let t0 = (times()).tms_utime in 
	let result = f x in
	let t = ((times ()).tms_utime)-.t0 in
   print_float t;
   flush_all ();
   result;;

let string_of_int_list l = 
	Printf.sprintf "[%s]" (String.concat ";" (List.map string_of_int l)) 

let string_of_int_list_list ll =
	Printf.sprintf "[%s]" (String.concat ";" (List.map string_of_int_list ll))

(*********************************************************************************************)
(*********************************************************************************************)
(*********************************************************************************************)

let blah_around starting_blah ending_blah f arg =
	print_string (("-"^starting_blah arg)^"->");flush_all ();
	let res = f arg in
	print_endline (ending_blah res);flush_all ();
	res
;;

let nl () = print_newline ();;

let apply_blah name f a =
	blah_around (fun a -> name) (fun x -> "done. ") f a;;

let apply1_blah name f a =
	blah_around (fun a -> name^(aut_size_str a)) (fun x -> "done. ") f a;;

let size_blah name f a =
	blah_around (fun a -> name^(aut_size_str a)) (fun a -> (aut_size_str a)^" ") f a;;

let size_blahb name f a =
   print_string ("-"^name^(aut_size_str a)^"->");flush_all();
   let res = f a in
   print_bool res;print_newline();flush_all();
   res

let size_blah2 name f a1 a2 =
	print_string ("-"^name^(aut_size_str a1)^(aut_size_str a2)^"->");flush_all ();
	let res = f a1 a2 in
	print_string ((aut_size_str res)^"\n"); flush_all();
	res
;;
let size_blah2b name f a1 a2 =
	print_string ("-"^name^(aut_size_str a1)^(aut_size_str a2)^"->");flush_all ();
	let res = f a1 a2 in
	print_bool res;print_newline();flush_all();
	res
;;

let print_problem str = Printf.printf "\n&&&&&&&&&&&&&&&&&&&&&--%s--&&&&&&&&&&&&&&&&&&&&&&&\n" str;
			flush_all()
;;

(*********************************************************************************************)
(*********************************************************************************************)
(*********************************************************************************************)

open Specification
let name_aut_list_from_file file_name =
    let spec = Specification.file_parse file_name in
    spec.automata_list
;;

let aut_list_from_file file_name =
    List.map snd (name_aut_list_from_file file_name)
;;

(*********************************************************************************************)
(*********************************************************************************************)
(*********************************************************************************************)

type comparison = Less | Greater | Equal | Uncomparable

let comp_auts a1 a2 =
    let a1_in_a2 = Heuristics.is_included a1 a2 in
    let a2_in_a1 = Heuristics.is_included a2 a1 in
    match a1_in_a2,a2_in_a1 with
    true,true -> Equal
    | true,false -> Less
    | false,true -> Greater
    | false,false -> Uncomparable
;;

let comparison_to_str = function
    Equal -> "="
    | Less -> "<"
    | Greater -> ">"
    | Uncomparable -> "x"
;;

let print_comparison cmp = print_string (comparison_to_str cmp);;

let compare_and_print a1 a2 =  print_comparison (comp_auts a1 a2)


(*********************************************************************************************)
(*********************************************************************************************)
(*********************************************************************************************)

open Unix;;
let time() = (times ()).tms_utime;;


let empty_aut aut = 
        let f = Taml.Automaton.get_alphabet aut in
        Taml.automaton f "
        States
        Final States
        Transitions";;


let compare_fta verbose f1 f2 = 
   if verbose then (print_string "\nReading TA1 ... ";flush_all());
   let autlist1 = name_aut_list_from_file f1 in
   if verbose then (print_string "done. Reading TA2 ... ";flush_all());
   let autlist2 = name_aut_list_from_file f2 in
   if verbose then (print_string "done. Comparing ... ";flush_all());
   let result = comp_auts (snd (List.hd autlist1)) (snd (List.hd autlist2))
   in
   if verbose then (print_string "done. The result: ");
   print_comparison result;;


(*********************************************************************************************)
(*********************************************************************************************)
(*********************************************************************************************)

let aut_from_aut_and_final aut fin =
   Interim.simplify_taml (Automaton.make_automaton
         (Automaton.get_alphabet aut)
         (Automaton.get_state_ops aut)
         (Automaton.get_states aut)
         (State_set.add fin (State_set.empty))
         (Automaton.get_prior aut)
         (Automaton.get_transitions aut) );;

let get_aut_list aut =
   let states = State_set.to_list (Automaton.get_states aut) in
   List.map (aut_from_aut_and_final aut) states

let nonemty_intersections aut pred_aut =
   let aut_list = get_aut_list aut in
   let pred_list = get_aut_list pred_aut in
   let inter_list = 
      List.map (fun a_st ->
         List.map (fun p_st ->
            Automaton.is_language_empty (Automaton.inter a_st p_st)
         ) pred_list
      ) aut_list
   in
   inter_list

let nonempty_intersections aut pred_aut =
   let aut_list = get_aut_list aut in
   let inter_list = 
      List.map (fun a_st ->
         Automaton.is_language_empty (Automaton.inter a_st pred_aut)
      ) aut_list
   in
   inter_list

