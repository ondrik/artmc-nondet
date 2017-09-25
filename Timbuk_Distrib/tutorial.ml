let f= alphabet "app:2 cons:2 nil:0 a:0 b:0";;
let v= varset "x y z u";;
let t= term f  v "cons(a, cons(b, nil))";;
let fvterm= term f v;;
let l= List.map fvterm ["app(cons(a, nil),cons(b, cons(b, nil)))"; "a"; "cons(a,nil)"];;
let tt= trs f v "app(nil, x) -> x   app(cons(x, y), z) -> cons(x, app(y, z))";;
let aut= automaton f "
States qa qb qla qlb qf
Final States qf
Transitions
        a -> qa
        b -> qb
        cons(qa, qla) -> qla
        nil -> qla
        cons(qb, qlb) -> qlb
        nil -> qlb
        app(qla,qlb) -> qf";;
let t1= List.hd l;;
let s= state "qf";;
run t1 s aut;;
let t2= Rewrite.left_inner_norm tt t1;;
let tt= read_trs "current_TRS" "comp.txt";;
let aut= read_automaton "completed_A0" "comp.txt";;
let aut_iff= irr f tt;;
let norm= inter aut aut_iff;;
let norm2= simplify norm;;
browse norm2;;
