open Taml;;
open Minimize_abstr_fin_length;;
open Colapsing_v3;;
open Transducer_st_pres;;

let alpha= alphabet "o:2 i:2 u:2 oo:0 ii:0";;

let init= automaton alpha "
	States p0 p1
	Final States p1
	Transitions
	  oo -> p0
          ii -> p0

	  u(p0,p0) -> p1
          u(p0,p1) -> p1
          u(p1,p0) -> p1
          u(p1,p1) -> p1
          u(p0,p0) -> p1  "
;;

let tau=
  (["q0";"q1";"qU";"qD"],
   ["qD"],
   [   	  ("oo" , [], "oo", "q0");
          ("ii" , [], "ii", "q1");

          ("o", ["q0";"q0"], "o" , "q0");

          ("i", ["q0";"q1"], "i" , "q1");
          ("i", ["q1";"q0"], "i" , "q1");
          ("i", ["q1";"q1"], "i" , "q1");
   
          ("u", ["q0";"q0"], "u" , "qU");   
          ("u", ["q0";"q1"], "u" , "qU");
          ("u", ["q0";"qU"], "u" , "qU");   
          ("u", ["q1";"q0"], "u" , "qU");   
          ("u", ["q1";"q1"], "u" , "qU");
          ("u", ["q1";"qU"], "u" , "qU");   
          ("u", ["qU";"q0"], "u" , "qU");   
          ("u", ["qU";"q1"], "u" , "qU");
          ("u", ["qU";"qU"], "u" , "qU");   

          ("u", ["q0";"qD"], "u" , "qD");   
          ("u", ["q1";"qD"], "u" , "qD");
          ("u", ["qU";"qD"], "u" , "qD");   
          ("u", ["qD";"q0"], "u" , "qD");   
          ("u", ["qD";"q1"], "u" , "qD");
          ("u", ["qD";"qU"], "u" , "qD");   

          ("u", ["q0";"q0"], "o" , "qD");

          ("u", ["q0";"q1"], "i" , "qD");
          ("u", ["q1";"q0"], "i" , "qD");
          ("u", ["q1";"q1"], "i" , "qD")    ]
);;

let tr = (compile_transducer tau);;

let res=apply_tr_aut tr init;;
