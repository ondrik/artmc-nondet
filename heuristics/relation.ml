
let is_transitive rel =
   let result = ref true in
   let l = Array.length rel in
   for i=0 to l-1 do
      for j=0 to l-1 do
         for k=0 to l-1 do
            if rel.(i).(j) && rel.(j).(k) && not rel.(i).(k) then (
(*                     Printf.printf "\n%d,%d,%d\n" i j k;*)
               result:=false
            )
         done
      done
   done
   ;!result

let is_symmetric rel =
   let result = ref true in
   Array.iteri (fun i _ ->
      Array.iteri (fun j _ ->
         if rel.(i).(j)<>rel.(j).(i) then
            result:=false
      ) rel
   ) rel
   ;!result


let symmetric rel =
   let l = Array.length rel in
   let eq = Array.make_matrix l l false in
   for i = 0 to l-1 do
      for j = 0 to l-1 do
         eq.(i).(j) <- rel.(i).(j) && rel.(j).(i)
      done 
   done
   ; eq

let complement rel =
   let l = Array.length rel in
   let res = Array.make_matrix l l false in
   for i=0 to l-1 do
      for j=0 to l-1 do
         res.(i).(j)<-not rel.(i).(j)
      done 
   done;
   res

let contains rel1 rel2 =
   let l = Array.length rel2 in
   let contains = ref true in
   for i=0 to l-1 do 
      for j=0 to l-1 do 
         if not rel1.(i).(j) && rel2.(i).(j) then 
            contains:=false
      done
   done;
   !contains
         
let transitive_wrt refl keep =
   let tr = Array.map (Array.copy) refl in 

(*   if not (is_transitive keep) then failwith"get_transitive_wrt0"; *)
(*   if not (contains tr keep) then failwith"get_transitive_wrt00"; *)

   let l = Array.length tr in 
   let transitivity_broken i j k = tr.(i).(j) && tr.(j).(k) && not tr.(i).(k) in
   let rec recursive_cut i j k =
      let (x,y) = 
         if not keep.(i).(j) then (i,j)
         else if not keep.(j).(k) then (j,k)
         else failwith"recursive_cut"
      in
      tr.(x).(y)<-false;
      for n=0 to l-1 do
         if transitivity_broken x n y then
            recursive_cut x n y
      done
   in
   for i=0 to l-1 do 
      for j=0 to l-1 do 
         for k=0 to l-1 do
            if transitivity_broken i j k then
               recursive_cut i j k
         done
      done
   done;

(*   if not (contains tr keep) then failwith"get_transitive_wrt1"; *)
(*   if not (is_transitive tr) then failwith"get_transitive_wrt2"; *)

   tr

let cardinality matrix = 
   Array.fold_left (fun n row ->
      n -1 + (Array.fold_left (fun m r ->
         m + (if r then 1 else 0)
      ) 0 row)
   ) 0 matrix 

let composition rel1 rel2 =
   let l = Array.length rel1 in
   let rel = Array.make_matrix l l false in
   for i = 0 to l-1 do
      for j = 0 to l-1 do
         let exists_t = ref false in
         for t = 0 to l-1 do
            exists_t:= !exists_t || (rel1.(i).(t) && rel2.(j).(t));
         done;
         rel.(i).(j) <- !exists_t;
      done 
   done
   ; rel

let intersection rel1 rel2 = 
   Array.mapi (fun i _ ->
      Array.mapi (fun j _ ->
         rel1.(i).(j) && rel2.(i).(j)
      )rel1
   )rel1

let inversion rel = 
   let n = Array.length rel in
   let res = Array.make_matrix n n false in
   for i=0 to n-1 do
      for j=0 to n-1 do
         res.(i).(j)<-rel.(j).(i)
      done
   done
   ;res

let are_indenpendent rel1 rel2 =
   let result = ref true in
   let len = Array.length rel1 in
   for i = 0 to len-1 do 
      for j = 0 to len-1 do 
         for k = 0 to len-1 do  
            if rel1.(i).(k) && rel2.(j).(k) then (
               let s_exists = ref false in
               for s = 0 to len-1 do 
                  s_exists := !s_exists || (rel1.(s).(j) && rel2.(s).(i))
               done;
               if not !s_exists then (
(*						Printf.printf "%d\%d/%d\n" i k j;*)
                  result:=false
               )
            )
         done;
      done;
   done
;!result

(*compose h and s^-1, get usefull edges*)
let usefull h s =
	let n = Array.length h in 
	let c = Array.make_matrix n n false in 
	for i=0 to n-1 do 
		for j=0 to n-1 do
			for k=0 to n-1 do 
				if h.(i).(k) && s.(j).(k) then c.(i).(j) <- true
			done
		done 
	done;
(*	Mess.print_bool_matrix c;*)
(*	print_newline();*)
(*	print_newline();*)
	let u = Array.map Array.copy c in
	for i=0 to n-1 do 
		for j=0 to n-1 do
			for k=0 to n-1 do 
				if h.(i).(j) && u.(j).(k) && not c.(i).(k) then u.(j).(k) <- false;
				if u.(i).(j) && h.(j).(k) && not c.(i).(k) then u.(i).(j) <- false
			done
		done 
	done;
(*	if not (is_transitive u) then failwith"U is not transitive!";*)
	u

let identity n = 
        let id = Array.make_matrix n n false in
        for i=0 to n-1 do id.(i).(i) <- true done;
        id

