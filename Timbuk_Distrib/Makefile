# 'make'		produce a byte code version of timbuk and tabi (with tabi browsing activated in timbuk)

# 'make timbuk' 	produce a byte code version of timbuk alone
# 'make tabi'   	produce a byte code version of tabi alone

# 'make taml'   		produce a caml toplevel with tree automata functionalities
# 'make taml-tabi' 		produce a caml toplevel with tree automata and tabi functionalities

# 'make binary' produce a native code version of timbuk and tabi (with tabi browsing activated in timbuk)
# 'make timbuk-binary' produce a native code version of timbuk alone
# 'make tabi-binary' produce a native code version of tabi alone

# 'make debug' produce a byte code version of timbuk with debug information
# 'make clean' 	cleans all
# 'make depend' reinspect dependencies between files (file .depend must exist in
# the directory)


################################################################################

# From ocaml 3.03 stream parsing is no longer built-in
PREPROC=  -pp "camlp4o" 
PREPROCTABI=  -pp "camlp4o pa_macro.cmo -DTABI"
PREPROCNOTABI=  -pp "camlp4o pa_macro.cmo -UTABI"

# For ocaml 3.02 and lower stream parsers are builtins 
# PREPROC=  
# PREPROCTABI=  -pp "camlp4o pa_macro.cmo -DTABI"
# PREPROCNOTABI=  -pp "camlp4o pa_macro.cmo -UTABI"


################################################################################
#############################

OCAMLC=ocamlc
OCAMLOPT=ocamlopt
OCAMLTOP=ocamlmktop
OCAMLTOPOP=ocamlmktop -custom 

OCAMLDEP=ocamldep
INCLUDES=                 # all relevant -I options here
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) -ccopt -O3 # add other options for ocamlopt here

TIMBUK_SOURCES= \
	common.ml     \
	symbol.ml      \
	variable.ml      \
	alphabet.ml      \
	variable_set.ml    \
	term.ml     \
	state_content.ml \
	state_set.ml      \
	rewrite.ml \
	automaton.ml        \
	specification.ml     \
	gamma.ml             \
	completion.ml		\
	main.ml		


TABI_SOURCES= 		\
	specifs.ml \
	gest.ml \
	cotes.ml \
	evts.ml \
	visu.ml \
	main-tabi.ml

TIMBUK_TABI_SOURCES= \
	common.ml     \
	symbol.ml      \
	variable.ml      \
	alphabet.ml      \
	variable_set.ml    \
	term.ml     \
	state_content.ml \
	state_set.ml      \
	rewrite.ml \
	automaton.ml        \
	specification.ml     \
	gamma.ml             \
	specifs.ml \
	gest.ml \
	cotes.ml \
	evts.ml \
	visu.ml \
	completion.ml		\
	main.ml		


MAIN_TIMBUK_OBJS= $(patsubst %.ml, %.cmo, $(TIMBUK_SOURCES))

NC_TIMBUK_OBJS=  $(patsubst %.ml, %.cmx, $(TIMBUK_SOURCES))

TIMBUK_INTERFACES= $(patsubst %.ml, %.mli, $(TIMBUK_SOURCES))


TIMBUK_TABI_OBJS= $(patsubst %.ml, %.cmo, $(TIMBUK_TABI_SOURCES))

NC_TIMBUK_TABI_OBJS= $(patsubst %.ml, %.cmx, $(TIMBUK_TABI_SOURCES))


MAIN_TABI_OBJS= $(patsubst %.ml, %.cmo, $(TABI_SOURCES))

NC_TABI_OBJS=  $(patsubst %.ml, %.cmx, $(TABI_SOURCES))

TABI_INTERFACES= $(patsubst %.ml, %.mli, $(TABI_SOURCES))


main all: 
	$(MAKE) timbuk TABI=true
	$(MAKE) taml TABI=true
	$(MAKE) tabi 


ifeq ($(TABI), true)
timbuk: $(TIMBUK_TABI_OBJS) 
	$(OCAMLC) -o timbuk $(OCAMLFLAGS)        \
	-I +labltk labltk.cma unix.cma \
	$(TIMBUK_TABI_OBJS)
else
timbuk: $(MAIN_TIMBUK_OBJS)
	$(OCAMLC)                      \
	-o timbuk $(OCAMLFLAGS)        \
	$(MAIN_TIMBUK_OBJS)
endif

tabi: $(filter-out main.cmo completion.cmo, $(MAIN_TIMBUK_OBJS)) $(MAIN_TABI_OBJS) 
	$(OCAMLC)                      \
	-o tabi $(OCAMLFLAGS)        \
	-I +labltk labltk.cma unix.cma \
	$(filter-out main.cmo completion.cmo, $(MAIN_TIMBUK_OBJS)) $(MAIN_TABI_OBJS) 

taml-tabi: 
	$(MAKE) taml TABI=true

ifeq ($(TABI), true)
taml: $(filter-out main.cmo, $(TIMBUK_TABI_OBJS) taml-init.ml taml.cmo)
	$(OCAMLTOP) -o taml \
	-I +labltk labltk.cma unix.cma \
	$(filter-out main.cmo, $(TIMBUK_TABI_OBJS) taml.cmo)
	cp -f taml-init.ml .ocamlinit
else
taml: $(filter-out main.cmo, $(MAIN_TIMBUK_OBJS) taml-init.ml taml.cmo)
	$(OCAMLTOP) -o taml \
	$(filter-out main.cmo, $(MAIN_TIMBUK_OBJS) taml.cmo)
	cp -f taml-init.ml .ocamlinit
endif

taml.cma: $(filter-out main.cmo, $(MAIN_TIMBUK_OBJS) taml-init.ml taml.cmo)
	$(OCAMLC) -a -o taml.cma \
	$(filter-out main.cmo, $(MAIN_TIMBUK_OBJS) taml.cmo)
	cp -f taml-init.ml .ocamlinit

taml.cmxa: $(filter-out main.cmx, $(NC_TIMBUK_OBJS) taml-init.ml taml.cmx)
	$(OCAMLOPT) -linkall -a -o taml.cmxa $(OCAMLOPTFLAGS) \
	$(filter-out main.cmx, $(NC_TIMBUK_OBJS) taml.cmx)
	cp -f taml-init.ml .ocamlinit



debug: OCAMLC= ocamlc -g

# we only debug timbuk
debug: $(MAIN_TIMBUK_OBJS)			
	$(OCAMLC)                      \
	-o timbuk-debug $(OCAMLFLAGS)  \
	$(MAIN_TIMBUK_OBJS)

binary: 
	$(MAKE) timbuk-binary TABI=true
	$(MAKE) taml TABI=true
	$(MAKE) tabi-binary



ifeq ($(TABI), true)
timbuk-binary: $(NC_TIMBUK_TABI_OBJS) 
	$(OCAMLOPT) -o timbuk $(OCAMLOPTFLAGS)        \
	-I +labltk labltk.cmxa unix.cmxa \
	$(NC_TIMBUK_TABI_OBJS)
else
timbuk-binary: $(NC_TIMBUK_OBJS)
	$(OCAMLOPT)                      \
	-o timbuk $(OCAMLOPTFLAGS)        \
	$(NC_TIMBUK_OBJS)
endif


tabi-binary: $(filter-out main.cmx completion.cmx, $(NC_TIMBUK_OBJS)) $(NC_TABI_OBJS) $(NC_VISU_OBJS)
	$(OCAMLOPT)                      \
	-o tabi $(OCAMLOPTFLAGS)        \
	-I +labltk labltk.cmxa unix.cmxa \
	$(filter-out main.cmx completion.cmx, $(NC_TIMBUK_OBJS)) $(NC_TABI_OBJS) $(NC_VISU_OBJS)


.SUFFIXES: .ml .mli .cmo .cmi .cmx


# visu.ml and cotes.ml need labeltk and labels and thus should be compiled separately

visu.cmo: visu.ml cotes.cmo evts.cmi gest.cmo specifs.cmo
	$(OCAMLC) -I +labltk labltk.cma $(PREPROC) $(OCAMLFLAGS) -c visu.ml

cotes.cmo: cotes.ml gest.cmo specifs.cmo 
	$(OCAMLC) -I +labltk labltk.cma $(PREPROC) $(OCAMLFLAGS) -c cotes.ml


visu.cmx: visu.ml cotes.cmx evts.cmi evts.cmx gest.cmx specifs.cmx
	$(OCAMLOPT) -I +labltk labltk.cmxa $(PREPROC) $(OCAMLOPTFLAGS) -c visu.ml

cotes.cmx: cotes.ml gest.cmx specifs.cmx 
	$(OCAMLOPT) -I +labltk labltk.cmxa $(PREPROC) $(OCAMLOPTFLAGS) -c cotes.ml


# Completion depends or not on Visu (if visualisation with tabi is activated or not) 

ifeq ($(TABI), true)
completion.cmo: completion.ml common.cmo visu.cmo specifs.cmo
	$(OCAMLC)  $(PREPROCTABI) $(OCAMLFLAGS) -c completion.ml
completion.cmx: completion.ml common.cmx visu.cmx specifs.cmx
	$(OCAMLOPT)  $(PREPROCTABI) $(OCAMLOPTFLAGS) -c completion.ml	
else
completion.cmo: completion.ml common.cmo 
	$(OCAMLC)  $(PREPROCNOTABI) $(OCAMLFLAGS) -c completion.ml
completion.cmx: completion.ml common.cmx
	$(OCAMLOPT)  $(PREPROCNOTABI) $(OCAMLOPTFLAGS) -c completion.ml	
endif


# Taml depends or not on Visu (if visualisation with tabi is activated or not) 

ifeq ($(TABI), true)
taml.cmo: taml.ml alphabet.cmi automaton.cmi completion.cmo gamma.cmi rewrite.cmi \
    specification.cmi state_content.cmo state_set.cmi symbol.cmi term.cmi \
    variable.cmi variable_set.cmi visu.cmo 	
	$(OCAMLC)  $(PREPROCTABI) $(OCAMLFLAGS) -c taml.ml
else
taml.cmo: taml.ml alphabet.cmi automaton.cmi completion.cmo gamma.cmi rewrite.cmi \
    specification.cmi state_content.cmo state_set.cmi symbol.cmi term.cmi \
    variable.cmi variable_set.cmi
	$(OCAMLC)  $(PREPROCNOTABI) $(OCAMLFLAGS) -c taml.ml
endif


.ml.cmo:
	$(OCAMLC)  $(PREPROC) $(OCAMLFLAGS) -c $< 

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT)  $(PREPROC) $(OCAMLOPTFLAGS) -c $< 

# Clean up
clean:
	rm -f tabi timbuk timbuk-debug taml .ocamlinit
	rm -f *.cm[iox]
	rm -f *.*~
	rm -f *~
	clear

# Dependencies
depend:
		$(OCAMLDEP) $(PREPROC) $(INCLUDES)  $(filter-out completion.ml, $(TIMBUK_SOURCES)) $(TIMBUK_INTERFACES) \
								$(TABI_SOURCES) $(TABI_INTERFACES) > .depend


include .depend



