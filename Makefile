#make - builds binary and bytecody executable file and bytecode library
#make bin - binary executabe
#make byte - bytecode executable
#make lib - bytecode library (without experiments)
#make clean - ...
#make cleanall - make clean and make clean in Timbuk_Distrib dir., rm exec. and lib. files
#For building Taml libraries, add this into Taml Makefile:
#taml.cma: $(filter-out main.cmo, $(MAIN_TIMBUK_OBJS) taml-init.ml taml.cmo)
#	$(OCAMLC) -a -o taml.cma \
#	$(filter-out main.cmo, $(MAIN_TIMBUK_OBJS) taml.cmo)
#	cp -f taml-init.ml .ocamlinit

#taml.cmxa: $(filter-out main.cmx, $(NC_TIMBUK_OBJS) taml-init.ml taml.cmx)
#	$(OCAMLOPT) -a -o taml.cma \
#	$(filter-out main.cmx, $(NC_TIMBUK_OBJS) taml.cmx)
#	cp -f taml-init.ml .ocamlinit
#
# For binary version - comment lines 54,55,91,92,93 in taml.ml

OCAMLC=ocamlc -g#
OCAMLOPT=ocamlopt -inline 10# -p#
OCAMLDEP=ocamldep#

TAML_DIR=Timbuk_Distrib#
HEUR_DIR=heuristics#
ARTMC_DIR=artmc#
EXPR_DIR=experiments#

TAML_BYTE_LIB=taml.cma#timbuk sources byte code
TAML_BIN_LIB=taml.cmxa#timbuk sources binary

INCLUDES=-I $(TAML_DIR) -I $(HEUR_DIR) -I $(ARTMC_DIR) -I $(EXPR_DIR)#

HEUR_SRCS= \
	interim.ml \
	trlist.ml \
	gen.ml \
	fixpointAntichain.ml \
	incl.ml \
	algorithms.ml \
	bisimin.ml \
	merge.ml \
	hHK.ml \
	treeSimLTS.ml \
	heuristics.ml \
	mess.ml \
	relation.ml \
	simplesim.ml \
	simin.ml


ARTMC_SRCS= \
	minimize_abstr_fin_length.ml \
	automata_equal.ml \
	rotation.ml \
	create_transducers.ml \
	transducer_st_pres.ml \
	transducer_relab.ml \
	transducer_hom_v2.ml \
	transducer_main.ml \
	input.ml \
	colapsing_v3.ml \
	main_loop_utility.ml \
	main_loop.ml \
	simple_main_loop.ml \
	dxn.ml \
	predicate_generation.ml

#EXPR_SRCS= \
	rb_insert_rebalance.ml \
	main_rb_insert_rebalance.ml

#EXPR_SRCS= \
	rb_insert_rebalance_withGenTest.ml \
	main_rb_insert_rebalance_withGenTest.ml
	
#EXPR_SRCS= \
	rb_delete_rebalance.ml \
	main_rb_delete_rebalance.ml

#EXPR_SRCS= \
	dfs.ml \
	main_dfs.ml

EXPR_SRCS= \
	simple_artmc_exprm.ml \
	simple.ml


EXEC_BYTE=runbyte#
EXEC_BIN =runbin#
LIB_BYTE =tamlartmc.cma#

P_TAML_BYTE_LIB = $(addprefix $(TAML_DIR)/, $(TAML_BYTE_LIB))
P_TAML_BIN_LIB  = $(addprefix $(TAML_DIR)/, $(TAML_BIN_LIB))

P_HEUR_SRCS = $(addprefix $(HEUR_DIR)/, $(HEUR_SRCS))
P_HEUR_BYTE = $(patsubst %.ml, %.cmo, $(P_HEUR_SRCS))
P_HEUR_BIN  = $(patsubst %.ml, %.cmx, $(P_HEUR_SRCS))

P_ARTMC_SRCS = $(addprefix $(ARTMC_DIR)/, $(ARTMC_SRCS))
P_ARTMC_BYTE = $(patsubst %.ml, %.cmo, $(P_ARTMC_SRCS))
P_ARTMC_BIN  = $(patsubst %.ml, %.cmx, $(P_ARTMC_SRCS))

P_EXPR_SRCS = $(addprefix $(EXPR_DIR)/, $(EXPR_SRCS))
P_EXPR_BYTE = $(patsubst %.ml, %.cmo, $(P_EXPR_SRCS))
P_EXPR_BIN  = $(patsubst %.ml, %.cmx, $(P_EXPR_SRCS))

.SUFFIXES: .ml .mli .cmo .cmi .cmx

run:
	make lib
	ocaml -I $(TAML_DIR) -I heuristics -I artmc str.cma $(LIB_BYTE)
 
tamlbin:
	cd $(TAML_DIR);make $(TAML_BIN_LIB)

tamlbyte:
	cd $(TAML_DIR);make $(TAML_BYTE_LIB)

byte:
	make tamlbyte
	make $(EXEC_BYTE)

bin:
	make tamlbin
	make $(EXEC_BIN)

lib:
	make tamlbyte
	make $(LIB_BYTE)

$(P_TAML_BYTE_LIB): 
	cd $(TAML_DIR); make $(TAML_BYTE_LIB)

$(P_TAML_BIN_LIB): 
	cd $(TAML_DIR); make $(TAML_BIN_LIB)

.ml.cmo:
	$(OCAMLC) $(INCLUDES) $(P_TAML_BYTE_LIB) -c $< 

.ml.cmx:
	$(OCAMLOPT) $(INCLUDES) $(P_TAML_BIN_LIB) -c $< 


$(EXEC_BIN): $(P_TAML_BIN_LIB) $(P_HEUR_BIN) $(P_ARTMC_BIN) $(P_EXPR_BIN)
	$(OCAMLOPT) -o $(EXEC_BIN) \
	$(INCLUDES) \
	unix.cmxa str.cmxa $(P_TAML_BIN_LIB) $(P_HEUR_BIN) $(P_ARTMC_BIN) $(P_EXPR_BIN)

$(EXEC_BYTE): $(P_TAML_BYTE_LIB) $(P_HEUR_BYTE) $(P_ARTMC_BYTE) $(P_EXPR_BYTE)
	$(OCAMLC) -o $(EXEC_BYTE) \
	$(INCLUDES) \
	unix.cma str.cma $(P_TAML_BYTE_LIB) $(P_HEUR_BYTE) $(P_ARTMC_BYTE) $(P_EXPR_BYTE)

$(LIB_BYTE): $(P_TAML_BYTE_LIB) $(P_HEUR_BYTE) $(P_ARTMC_BYTE)
	$(OCAMLC) -a -o $(LIB_BYTE) \
	$(INCLUDES) \
	unix.cma str.cma  $(P_TAML_BYTE_LIB) $(P_HEUR_BYTE) $(P_ARTMC_BYTE)

# Clean up
RM=\
	rm -f comm;\
	rm -f *.cm[ioxa];\
	rm -f *.*~;\
	rm -f *~;\
	rm -f *.o;\
	rm -f *.a;\
	rm -f *.cmxa

cleanall:
	cd $(TAML_DIR);make clean
	make clean
	rm -f $(EXEC_BIN)
	rm -f $(EXEC_BYTE)
	rm -f $(LIB_BYTE)

clean:
	cd $(HEUR_DIR);$(RM)
	cd $(ARTMC_DIR);$(RM)
	cd $(EXPR_DIR);$(RM)

# Dependencies
depend:
		$(OCAMLDEP) $(INCLUDES) $(P_HEUR_SRCS) $(P_ARTMC_SRCS) $(P_EXPR_SRCS) > .depend


include .depend
