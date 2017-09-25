(*
open Taml;;
#use "/home/holik/ta/ARTMC/fromtom1/artmc-str_pres.ml";;
*)

(*
open Taml;;
#use "/home/holik/ta/ARTMC/fromtom1/nondet-artmc.ml";;
*)
open Taml;;
open Dxn;;
open Colapsing_v3;;

let token_passing  _ = 
print_string "
====================================================================================================
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
XXXXXX Simple bottom-up token passing
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
====================================================================================================
   ";
let sigma_str = "n:0 t:0 nn:2 tt:2" in
let init_str = "
  States p0:0 p1:0
  Final States p1
  Transitions
    n->p0 t->p1 nn(p0,p0)->p0 nn(p1,p0)->p1 nn(p0,p1)->p1" in
let tau_str = 
  (["q0"; "q1"; "q2"], ["q0"; "q2"],
   [("n", [], "n", "q0"); ("t", [], "n", "q1"); ("tt", ["q0"; "q0"], "nn", "q1"); ("nn", ["q1"; "q0"], "tt", "q2"); 
    ("nn", ["q0"; "q1"], "tt", "q2"); ("nn", ["q0"; "q0"], "nn", "q0"); ("nn", ["q2"; "q0"], "nn", "q2");
    ("nn", ["q0"; "q2"], "nn", "q2") ]) in
let bad_str = "
  States p0 p1 p2
  Final States p2
  Transitions
    n->p0 t->p1 nn(p0,p0)->p0 tt(p0,p0)->p1 nn(p1,p0)->p1 nn(p0,p1)->p1 tt(p1,p0)->p2 
    tt(p0,p1)->p2 nn(p1,p1)->p2 tt(p1,p1)->p2 nn(p2,p0)->p2 nn(p0,p2)->p2 tt(p2,p0)->p2 
    tt(p0,p2)->p2 nn(p2,p1)->p2 nn(p1,p2)->p2 tt(p2,p1)->p2 tt(p1,p2)->p2 nn(p2,p2)->p2 
    tt(p2,p2)->p2" in
let sigstar_str = "
  States p
  Final States p
  Transitions
    n->p t->p nn(p,p)->p tt(p,p)->p" 
in


print_endline"atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ]";
atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ];
(*0.020001x0.028002*)
print_endline" atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ] ";
atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ];
(*0.040003x0.088006*)
print_endline" atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ] ";
 atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ]; 
(*0.008001x0.048003*)
 print_endline" atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ] ";
 atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ]; 
(*0.028002x0.080005*)


(*print_endline"atrmc_strpres_fwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ bad_str ]";*)
(*atrmc_strpres_fwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ bad_str ]; *)
(*atrmc_strpres_fwcomp_bwcoll ~what_run:D sigma_str init_str tau_str bad_str [ bad_str ]; *)
(*loopingxlooping*)
(*atrmc_strpres_fwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ sigstar_str ]; *)
(*atrmc_strpres_fwcomp_bwcoll ~what_run:D sigma_str init_str tau_str bad_str [ sigstar_str ]; *)
(*loopingxlooping*)
print_endline"atrmc_strpres_bwcomp_bwcoll sigma_str init_str tau_str bad_str [ bad_str ] ";
atrmc_strpres_bwcomp_bwcoll sigma_str init_str tau_str bad_str [ bad_str ];
(*0.384024x0.168011*)
(*atrmc_strpres_bwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ sigstar_str ]; *)
(*atrmc_strpres_bwcomp_bwcoll ~what_run:D sigma_str init_str tau_str bad_str [ sigstar_str ]; *)
(*loopingxlooping*)
()

let two_way_token_passing  _ = 
print_string "
====================================================================================================
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
XXXXXX Two-way token passing
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
====================================================================================================
   ";

let sigma_str = "n:0 t:0 nn:2 tt:2" in
let init_str = "
  States p0:0 p1:0
  Final States p1
  Transitions
    n->p0 t->p1 nn(p0,p0)->p0 nn(p1,p0)->p1 nn(p0,p1)->p1" in
let tau_str = 
  (["q0"; "q1"; "q2"; "q3" ],
   ["q2"],
   [("n", [], "n", "q0"); ("t", [], "n", "q1"); ("n", [], "t", "q3");
    ("nn", ["q0"; "q0"], "nn", "q0"); ("tt", ["q0"; "q0"], "nn", "q1");
    ("nn", ["q0"; "q1"], "tt", "q2"); ("nn", ["q1"; "q0"], "tt", "q2");    
    ("nn", ["q0"; "q2"], "nn", "q2"); ("nn", ["q2"; "q0"], "nn", "q2"); 
    ("tt", ["q0"; "q3"], "nn", "q2"); ("tt", ["q3"; "q0"], "nn", "q2"); ("nn", ["q0"; "q0"], "tt", "q3") ]) in
let bad_str = "
  States p0 p1 p2
  Final States p2
  Transitions
    n->p0 t->p1 nn(p0,p0)->p0 tt(p0,p0)->p1 nn(p1,p0)->p1 nn(p0,p1)->p1 tt(p1,p0)->p2 
    tt(p0,p1)->p2 nn(p1,p1)->p2 tt(p1,p1)->p2 nn(p2,p0)->p2 nn(p0,p2)->p2 tt(p2,p0)->p2 
    tt(p0,p2)->p2 nn(p2,p1)->p2 nn(p1,p2)->p2 tt(p2,p1)->p2 tt(p1,p2)->p2 nn(p2,p2)->p2 
    tt(p2,p2)->p2" in
let sigstar_str = "
  States p
  Final States p
  Transitions
    n->p t->p nn(p,p)->p tt(p,p)->p" 
in
print_endline" atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ] ";
 atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ];
(*0.020001x0.064004*)
print_endline" atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ] ";
 atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ];
(*0.060004x0.108006*)
print_endline" atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ] ";
 atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ];
(*0.012001x0.048003*)
print_endline" atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ] ";
 atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ];
(*0.040003x0.096006*)
(* atrmc_strpres_fwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ bad_str ];; *)
(* atrmc_strpres_fwcomp_bwcoll ~what_run:D sigma_str init_str tau_str bad_str [ bad_str ];; *)
(*loopingxlooping*)
(* atrmc_strpres_fwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ sigstar_str ];; *)
(* atrmc_strpres_fwcomp_bwcoll ~what_run:D sigma_str init_str tau_str bad_str [ sigstar_str ];; *)
(*loopingxlooping*)
print_endline" atrmc_strpres_bwcomp_bwcoll sigma_str init_str tau_str bad_str [ bad_str ] ";
atrmc_strpres_bwcomp_bwcoll sigma_str init_str tau_str bad_str [ bad_str ];
(*0.440027x0.216014*)
(* atrmc_strpres_bwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ sigstar_str ];; *)
(* atrmc_strpres_bwcomp_bwcoll ~what_run:D sigma_str init_str tau_str bad_str [ sigstar_str ];; *)
(*loopingxlooping*)
 ()

let tree_arbiter  _ = 
print_string "
====================================================================================================
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
XXXXXX Tree arbiter
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
====================================================================================================
   ";
 
let sigma_str = "i:2 r:2 t:2 b:2 ii:0 rr:0 tt:0" in
let init_str = "
  States p0 p1
  Final States p1
  Transitions
    ii -> p0 i(p0,p0) -> p0 t(p0,p0) -> p1" in
let bad_str = "
  States p0 pt perr
  Final States perr p0
  Transitions
    rr -> p0 ii -> p0 tt -> pt i(p0,p0) -> p0 i(pt,p0) -> pt i(p0,pt) -> pt i(pt,pt) -> perr i(perr,p0) -> perr
    i(perr,pt) -> perr i(p0,perr) -> perr i(pt,perr) -> perr i(perr,perr) -> perr b(p0,p0) -> p0 b(pt,p0) -> pt
    b(p0,pt) -> pt b(pt,pt) -> perr b(perr,p0) -> perr b(perr,pt) -> perr b(p0,perr) -> perr b(pt,perr) -> perr
    b(perr,perr) -> perr r(p0,p0) -> p0 r(pt,p0) -> pt r(p0,pt) -> pt r(pt,pt) -> perr r(perr,p0) -> perr
    r(perr,pt) -> perr r(p0,perr) -> perr r(pt,perr) -> perr r(perr,perr) -> perr t(p0,p0) -> pt t(pt,p0) -> perr
    t(p0,pt) -> perr t(pt,pt) -> perr t(perr,p0) -> perr t(perr,pt) -> perr t(p0,perr) -> perr t(pt,perr) -> perr
    t(perr,perr) -> perr " in
let good_str = "States pi pr pt
  Final States pt
  Transitions
    tt -> pt rr -> pr ii -> pi i(pi,pi) -> pi r(pi,pr) -> pr r(pr,pi) -> pr r(pr,pr) -> pr t(pi,pi) -> pt
    t(pi,pr) -> pt t(pr,pi) -> pt t(pr,pr) -> pt b(pi,pt) -> pt b(pt,pi) -> pt b(pr,pt) -> pt b(pt,pr) -> pt" in 
let tau_str =
  (["qi";"qreq";"qrel";"qgrant";"qcomp"],
   ["qcomp"],
   [("ii" , [], "ii", "qi"); ("tt" , [], "ii", "qrel"); ("i", ["qreq";"qreq"], "r" , "qreq");
    ("r", ["qreq";"qi"], "t" , "qgrant"); ("t", ["qi";"qgrant"], "b" , "qcomp"); ("t", ["qi";"qreq"], "i" , "qrel");
    ("b", ["qi";"qrel"], "t" , "qcomp"); ("b", ["qi";"qcomp"], "b" , "qcomp"); ("ii", [], "rr", "qreq");
    ("i", ["qi";"qi"], "i" , "qi"); ("r", ["qreq";"qi"], "r" , "qreq"); ("r", ["qi";"qreq"], "t" , "qgrant");
    ("t", ["qgrant";"qreq"], "b" , "qcomp"); ("t", ["qreq";"qi"], "i" , "qrel");
    ("b", ["qrel";"qreq"], "t" , "qcomp"); ("b", ["qcomp";"qreq"], "b" , "qcomp"); ("rr", [], "rr", "qreq");
    ("i", ["qreq";"qi"], "r" , "qreq"); ("r", ["qi";"qreq"], "r" , "qreq"); ("r", ["qreq";"qreq"], "t" , "qgrant");
    ("t", ["qreq";"qgrant"], "b" , "qcomp"); ("t", ["qreq";"qreq"], "i" , "qrel");
    ("b", ["qreq";"qrel"], "t" , "qcomp"); ("b", ["qreq";"qcomp"], "b" , "qcomp"); ("rr", [], "tt", "qgrant");
    ("i", ["qi";"qreq"], "r" , "qreq"); ("r", ["qreq";"qreq"], "r" , "qreq"); ("t", ["qgrant";"qi"], "b" , "qcomp");
    ("t", ["qi";"qi"], "i" , "qrel"); ("b", ["qrel";"qi"], "t" , "qcomp"); ("b", ["qcomp";"qi"], "b" , "qcomp");
    ("t", ["qreq";"qreq"], "t" , "qcomp"); ("t", ["qi";"qi"], "t" , "qcomp"); ("t", ["qreq";"qi"], "t" , "qcomp");
    ("t", ["qi";"qreq"], "t" , "qcomp")]) in
let sigstar_str = "
  States pp
  Final States pp
  Transitions
    ii -> pp rr -> pp tt -> pp i(pp,pp) -> pp r(pp,pp) -> pp b(pp,pp) -> pp t(pp,pp) -> pp "
in
print_endline"atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ]";
atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ];
(*0.060003x0.264016*)
print_endline"atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ] ";
atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ];
(*1.240078x14.532908*)
print_endline"atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ]" ;
atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ];
(*0.040003x0.168010*)
print_endline"atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ]" ;
atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ];
(*0.140008x0.452029*)

print_endline" atrmc_strpres_fwcomp_bwcoll sigma_str init_str tau_str bad_str [ bad_str ]" ;
 atrmc_strpres_fwcomp_bwcoll sigma_str init_str tau_str bad_str [ bad_str ];
(*0.120007x0.308019*)
print_endline" atrmc_strpres_fwcomp_bwcoll sigma_str init_str tau_str bad_str [ sigstar_str ] ";
atrmc_strpres_fwcomp_bwcoll sigma_str init_str tau_str bad_str [ sigstar_str ];
(*1.156072x3.120195*)
(*atrmc_strpres_bwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ bad_str ];; *)
(*atrmc_strpres_bwcomp_bwcoll ~what_run:D sigma_str init_str tau_str bad_str [ bad_str ];; *)
(*looping x looping*)
(*atrmc_strpres_bwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ sigstar_str ];; *)
(*atrmc_strpres_bwcomp_bwcoll ~what_run:D sigma_str init_str tau_str bad_str [ sigstar_str ];; *)
(*looping x looping*)
()

let percolate  _ = 
print_string "
====================================================================================================
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
XXXXXX Percolate: o == 0, i == 1, u == still unknown
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
====================================================================================================
   ";


let sigma_str = "o:2 i:2 u:2 oo:0 ii:0" in
let init_str = "
  States p0 p1
	Final States p1
	Transitions
	  oo -> p0
          ii -> p0
	  u(p0,p0) -> p1
          u(p0,p1) -> p1
          u(p1,p0) -> p1
          u(p1,p1) -> p1
          u(p0,p0) -> p1 " in
let bad_str = "
       States q5:0 q4:0 q3:0 q2:0 q1:0 q0:0
       Final States q0 q3
       Transitions
         oo -> q2  o(q2,q2) -> q1  i(q2,q2) -> q1  u(q2,q2) -> q1  o(q2,q1) -> q1  i(q2,q1) -> q1  u(q2,q1) -> q1  o(q1,q2) -> q1 
         i(q1,q2) -> q1  u(q1,q2) -> q1  o(q1,q1) -> q1  i(q1,q1) -> q1  u(q1,q1) -> q1  i(q2,q2) -> q0  i(q2,q1) -> q0  
         i(q1,q2) -> q0  i(q1,q1) -> q0  oo -> q5  ii -> q4  o(q5,q5) -> q5  i(q5,q5) -> q5  u(q5,q5) -> q5  o(q5,q4) -> q4  
         i(q5,q4) -> q4  u(q5,q4) -> q4  o(q4,q5) -> q4  i(q4,q5) -> q4  u(q4,q5) -> q4  o(q4,q4) -> q4  i(q4,q4) -> q4  
         u(q4,q4) -> q4  o(q5,q4) -> q3  o(q4,q5) -> q3  o(q4,q4) -> q3 " in
let tau_str =
  (["q0";"q1";"qU";"qD"],
   ["qD"],
   [   	  ("oo" , [], "oo", "q0");          ("ii" , [], "ii", "q1");
          ("o", ["q0";"q0"], "o" , "q0");   ("i", ["q0";"q1"], "i" , "q1");
          ("i", ["q1";"q0"], "i" , "q1");   ("i", ["q1";"q1"], "i" , "q1");
          ("u", ["q0";"q0"], "u" , "qU");   ("u", ["q0";"q1"], "u" , "qU");
          ("u", ["q0";"qU"], "u" , "qU");   ("u", ["q1";"q0"], "u" , "qU");   
          ("u", ["q1";"q1"], "u" , "qU");   ("u", ["q1";"qU"], "u" , "qU");   
          ("u", ["qU";"q0"], "u" , "qU");   ("u", ["qU";"q1"], "u" , "qU");
          ("u", ["qU";"qU"], "u" , "qU");   ("u", ["q0";"qD"], "u" , "qD");   
          ("u", ["q1";"qD"], "u" , "qD");   ("u", ["qU";"qD"], "u" , "qD");   
          ("u", ["qD";"q0"], "u" , "qD");   ("u", ["qD";"q1"], "u" , "qD");
          ("u", ["qD";"qU"], "u" , "qD");   ("u", ["q0";"q0"], "o" , "qD");
          ("u", ["q0";"q1"], "i" , "qD");   ("u", ["q1";"q0"], "i" , "qD");
          ("u", ["q1";"q1"], "i" , "qD")    ] ) in
let sigstar_str = "
	States pp
	Final States pp
	Transitions
	oo -> pp
	ii -> pp
	o(pp,pp) -> pp
	i(pp,pp) -> pp
	u(pp,pp) -> pp  "
in
print_endline" atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ] ";
 atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ]; 
(*2.000125x6.436403*)
print_endline"atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ]";
atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ];
(*2.116132x1.428089*)
print_endline" atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ] ";
 atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ]; 
(*2.512157x12.936808*)
print_endline" atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ] ";
atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ] ;
(*0.304019x12.152759*)

(* atrmc_strpres_fwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ bad_str ];; *)
(* atrmc_strpres_fwcomp_bwcoll ~what_run:D sigma_str init_str tau_str bad_str [ bad_str ];; *)
(*loopingxlooping*)
(* atrmc_strpres_fwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ sigstar_str ];; *)
(* atrmc_strpres_fwcomp_bwcoll ~what_run:D sigma_str init_str tau_str bad_str [ sigstar_str ];; *)
(*loopingxlooping*)
(* atrmc_strpres_bwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ bad_str ];; *)
(* atrmc_strpres_bwcomp_bwcoll ~what_run:D sigma_str init_str tau_str bad_str [ bad_str ];; *)
(*loopingxlooping*)
(* atrmc_strpres_bwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ sigstar_str ];; *)
(* atrmc_strpres_bwcomp_bwcoll ~what_run:D sigma_str init_str tau_str bad_str [ sigstar_str ];; *)
(*loopingxlooping*)
()


let leader_election  _ = 
print_string "
====================================================================================================
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
XXXXXX Leader Election: qC -- a candidate is below, qN -- no candidates below, 
XXXXXX                  qEl -- the candidate to be elected is below, qU -- undefined yet
XXXXXX                  qJel -- just elected, qCh -- something changed below
XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
====================================================================================================
   ";

                                                                                                                
let sigma_str = "cc:0 nn:0 ee:0 c:2 n:2 e:2 u:2"in
let init_str = "
  States p0:0 p1:0
  Final States p0
  Transitions
  cc -> p0         u(p0,p1) -> p0
  nn -> p1         u(p1,p0) -> p0
  u(p0,p0) -> p0   u(p1,p1) -> p1  "in
let bad_str = "
  States p0:0 p1:0 p2:0 p3:0
  Final States p0 p3
  Transitions
  nn -> p0         u(p1,p0) -> p1   c(p1,p2) -> p2   u(p0,p3) -> p3   c(p2,p3) -> p3
  cc -> p1         n(p1,p1) -> p1   e(p1,p2) -> p2   n(p3,p0) -> p3   e(p2,p3) -> p3
  ee -> p2         c(p1,p1) -> p1   u(p1,p2) -> p2   c(p3,p0) -> p3   u(p2,p3) -> p3
  n(p0,p0) -> p0   e(p1,p1) -> p1   n(p2,p1) -> p2   e(p3,p0) -> p3   n(p3,p2) -> p3
  c(p0,p0) -> p0   u(p1,p1) -> p1   c(p2,p1) -> p2   u(p3,p0) -> p3   c(p3,p2) -> p3
  e(p0,p0) -> p0   n(p0,p2) -> p2   e(p2,p1) -> p2   n(p1,p3) -> p3   e(p3,p2) -> p3
  u(p0,p0) -> p0   c(p0,p2) -> p2   u(p2,p1) -> p2   c(p1,p3) -> p3   u(p3,p2) -> p3
  n(p0,p1) -> p1   e(p0,p2) -> p2   n(p2,p2) -> p3   e(p1,p3) -> p3   n(p3,p3) -> p3
  c(p0,p1) -> p1   u(p0,p2) -> p2   c(p2,p2) -> p3   u(p1,p3) -> p3   c(p3,p3) -> p3
  e(p0,p1) -> p1   n(p2,p0) -> p2   e(p2,p2) -> p3   n(p3,p1) -> p3   e(p3,p3) -> p3
  u(p0,p1) -> p1   c(p2,p0) -> p2   u(p2,p2) -> p3   c(p3,p1) -> p3   u(p3,p3) -> p3
  n(p1,p0) -> p1   e(p2,p0) -> p2   n(p0,p3) -> p3   e(p3,p1) -> p3
  c(p1,p0) -> p1   u(p2,p0) -> p2   c(p0,p3) -> p3   u(p3,p1) -> p3
  e(p1,p0) -> p1   n(p1,p2) -> p2   e(p0,p3) -> p3   n(p2,p3) -> p3"in
let tau_str = 
  (["qC";"qN";"qEl";"qU";"qJel";"qCh"],
   ["qEl";"qCh"],
   [ ("cc" , [], "cc", "qC"); ("cc" , [], "ee", "qJel"); ("nn" , [], "nn", "qN"); ("ee" , [], "ee", "qEl");
     ("c", ["qC";"qC"], "c" , "qC"); ("c", ["qC";"qN"], "c" , "qC"); ("c", ["qN";"qC"], "c" , "qC");
     ("c", ["qC";"qN"], "e" , "qJel"); ("c", ["qC";"qC"], "e" , "qJel"); ("c", ["qN";"qC"], "e" , "qJel");
     ("n", ["qN";"qN"], "n" , "qN"); ("u", ["qU";"qU"], "u" , "qU"); ("u", ["qN";"qU"], "u" , "qU"); ("u", ["qU";"qN"], "u" , "qU"); 
     ("u", ["qU";"qC"], "u" , "qU"); ("u", ["qC";"qU"], "u" , "qU"); ("u", ["qC";"qC"], "u" , "qU"); ("u", ["qN";"qN"], "u" , "qU"); 
     ("u", ["qN";"qC"], "u" , "qU"); ("u", ["qC";"qN"], "u" , "qU"); ("u", ["qCh";"qU"], "u" , "qCh"); ("u", ["qU";"qCh"], "u" , "qCh");
     ("u", ["qCh";"qN"], "u" , "qCh"); ("u", ["qN";"qCh"], "u" , "qCh"); ("u", ["qCh";"qC"], "u" , "qCh"); ("u", ["qC";"qCh"], "u" , "qCh"); 
     ("u", ["qC";"qC"], "c" , "qCh"); ("u", ["qN";"qC"], "c" , "qCh"); ("u", ["qC";"qN"], "c" , "qCh"); ("u", ["qN";"qN"], "n" , "qCh"); 
     ("e", ["qN";"qEl"], "e" , "qEl"); ("e", ["qEl";"qN"], "e" , "qEl"); ("e", ["qC";"qEl"], "e" , "qEl"); ("e", ["qEl";"qC"], "e" , "qEl"); 
     ("e", ["qN";"qJel"], "e" , "qEl"); ("e", ["qJel";"qN"], "e" , "qEl"); ("e", ["qC";"qJel"], "e" , "qEl"); ("e", ["qJel";"qC"], "e" , "qEl"); 
    ] )in
let sigstar_str = "
  States p:0
  Final States p
  Transitions
  nn -> p  n(p,p) -> p
  cc -> p  c(p,p) -> p
  ee -> p  e(p,p) -> p
           u(p,p) -> p  "
in
print_endline"atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ]";
atrmc_strpres_fwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ];
(*0.228014x0.972061*)
print_endline "atrmc_strpres_fwcomp_bwcoll_allstpred  sigma_str init_str tau_str bad_str [ sigstar_str ]";
 atrmc_strpres_fwcomp_bwcoll_allstpred  sigma_str init_str tau_str bad_str [ sigstar_str ];
(*too long x too long*)
print_endline" atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ] ";
 atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ bad_str ]; 
(*0.148009x1.140071*)
print_endline" atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ]"; 
 atrmc_strpres_bwcomp_bwcoll_allstpred sigma_str init_str tau_str bad_str [ sigstar_str ]; 
(*2.768173xtoo long*)

print_endline" atrmc_strpres_fwcomp_bwcoll sigma_str init_str tau_str bad_str [ bad_str ]";
 atrmc_strpres_fwcomp_bwcoll sigma_str init_str tau_str bad_str [ bad_str ]; 
(*0.356023x1.036064*)
print_endline" atrmc_strpres_fwcomp_bwcoll sigma_str init_str tau_str bad_str [ sigstar_str ]";
atrmc_strpres_fwcomp_bwcoll sigma_str init_str tau_str bad_str [ sigstar_str ];
(*0.540034x1.124070*)
(* atrmc_strpres_bwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ bad_str ]; *)
(* atrmc_strpres_bwcomp_bwcoll ~what_run:D sigma_str init_str tau_str bad_str [ bad_str ]; *)
(*loopingxlooping?*)
(* atrmc_strpres_bwcomp_bwcoll ~what_run:N sigma_str init_str tau_str bad_str [ sigstar_str ];*)
(* atrmc_strpres_bwcomp_bwcoll ~what_run:D sigma_str init_str tau_str bad_str [ sigstar_str ];; *)
(*13.088818xlooping?*)
()                                                                                                    
