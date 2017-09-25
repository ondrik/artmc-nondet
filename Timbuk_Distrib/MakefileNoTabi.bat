rem Tcl should be in the path set PATH= %PATH%;C:/Program Files/Tcl/bin
rem "Poor man's windows makefile"

set LIBP4= "%OCAMLLIB%\camlp4"

ocamlc -nolabels -c common.ml 
ocamlc      -c symbol.mli
ocamlc -nolabels -c symbol.ml 
ocamlc      -c variable.mli
ocamlc -nolabels  -c variable.ml 
ocamlc      -c alphabet.mli
ocamlc -nolabels -pp "camlp4o"       -c alphabet.ml 
ocamlc      -c variable_set.mli
ocamlc -nolabels -pp "camlp4o"       -c variable_set.ml 
ocamlc      -c term.mli
ocamlc -nolabels -pp "camlp4o"       -c term.ml 
ocamlc -nolabels -pp "camlp4o"       -c state_content.ml 
ocamlc      -c state_set.mli
ocamlc -nolabels -pp "camlp4o"       -c state_set.ml 
ocamlc      -c rewrite.mli
ocamlc -nolabels -pp "camlp4o"       -c rewrite.ml 
ocamlc      -c automaton.mli
ocamlc -nolabels -pp "camlp4o"       -c automaton.ml 
ocamlc      -c specification.mli
ocamlc -nolabels -pp "camlp4o"       -c specification.ml 
ocamlc      -c gamma.mli
ocamlc -nolabels -pp "camlp4o"       -c gamma.ml 
copy completion.ml temp2.ml
camlp4o -I %LIBP4% pa_ifdef.cmo -UTABI completion.ml > comptemp.ml
del completion.ml
ren comptemp.ml completion.ml
ocamlc -nolabels -c completion.ml
copy temp2.ml completion.ml
ocamlc -nolabels -pp "camlp4o"       -c main.ml 
ocamlc -o timbuk unix.cma common.cmo  symbol.cmo  variable.cmo  alphabet.cmo  variable_set.cmo  term.cmo  state_content.cmo  state_set.cmo  rewrite.cmo  automaton.cmo  specification.cmo  gamma.cmo  completion.cmo  main.cmo

copy taml.ml temp3.ml
camlp4o -I %LIBP4% pa_ifdef.cmo -UTABI taml.ml > comptemp.ml
del taml.ml
ren comptemp.ml taml.ml
ocamlc -nolabels -c taml.ml
copy temp3.ml taml.ml
ocamlmktop -o taml -I +labltk labltk.cma unix.cma common.cmo symbol.cmo variable.cmo alphabet.cmo variable_set.cmo term.cmo state_content.cmo state_set.cmo rewrite.cmo automaton.cmo specification.cmo gamma.cmo completion.cmo taml.cmo

copy taml-init.ml .ocamlinit
del comptemp.ml

