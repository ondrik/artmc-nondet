open Taml;;
open Interim;;
let f = alphabet "a:0 b:1 c:2";;

let rec fn () =
let ta = (Gen.generate_automaton2 f 8 0.5 0.0) in
Printf.printf "\ngenerated automaton size: %s\n" (Mess.aut_size_str ta);
Simin.compare_relations ta;
fn()
;;

let main() = fn();;
main()
