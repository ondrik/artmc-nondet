(* Timbuk - Tree Automata completion and Reachability testing 
   Copyright (C) 2000-2004 Thomas Genet and Valérie Viet Triem Tong

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU Library General Public License version 2, as
   published by the Free Software Foundation.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

   See the GNU Library General Public License version 2 for more details
   (enclosed in the file LGPL).


   Version 2.0. Last modification 21/01/04
*)

(* Timbuk - Tree Automata completion and Reachability testing 
   Copyright (C) 2000-2004 Thomas Genet and Valérie Viet Triem Tong

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU Library General Public License version 2, as
   published by the Free Software Foundation.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.

   See the GNU Library General Public License version 2 for more details
   (enclosed in the file LGPL).


   Version 2.0. Last modification 21/01/04
*)

(*i Be careful! Some comments of this file are formatted for ocamlweb. *)


(*i*) 
open Common 
(*i*)

(* This is the interface for bottom-up tree automata. A bottom-up tree automata
   is usually defined as a tuple: $\aut$ where $\F$ is an
   alphabet of symbols, $\Q$ is a set of states, $\Q_f$ a set of final
   states and $\Delta$ is a set of transitions (also called a
   transition table). Here, the tree automata module is defined 
   w.r.t. 
   \begin{itemize}
   \item a symbol type

   \item an alphabet type (the type of $\F$) whose
   symbols are of symbol type

   \item a variable type. It is used for defining variables occuring
   in matching on tree automata

   \item a configuration type i.e. left-hand side of transitions

   \item a state content type which can be anything assigned to 
   states: formulas, or simply text

   \item a transition type which is a term rewriting system and
   defined the type of $\Delta$ we use

   \item a state set type defining the type of $\Q$ and $\Q_f$ we
   use. In fact, in practice its major role is to assign state
   contents to states.

   \end{itemize}*)


module TreeAutomata
  (Symbol_type: PRINTABLE_TYPE)
  (Alphabet_type: ALPHABET_TYPE with type symbol= Symbol_type.t)
  (Variable_type: PRINTABLE_TYPE)
  (Configuration_type: TERM_TYPE with type symbol= Symbol_type.t 
				 and type variable= Variable_type.t
				 and type alphabet= Alphabet_type.t)
  (State_content: STATE_CONTENT_TYPE)
  (Transition_type: TRS_TYPE with type alphabet= Alphabet_type.t 
			     and type term= Configuration_type.t)
  (State_set_type: STATE_SET_TYPE with type state= Configuration_type.t 
				  and type state_content= State_content.t 
				  and type alphabet= Alphabet_type.t 
				  and type symbol= Symbol_type.t):
sig

  exception Not_a_state of string
  exception Not_in_folder
  exception Multiply_defined_symbol of string
  exception Linearity_problem of string
  exception Normalisation_problem of string
    
  type symbol= Symbol_type.t
  type alphabet= Alphabet_type.t
  type term= Configuration_type.t
  type rule= Transition_type.rule
  type substitution= Configuration_type.substitution

  type mini_subst= (term * term)	       

  type sol_filt=  
    | Empty
    | Bottom
    | S of mini_subst   
    | Not of sol_filt
    | And  of sol_filt * sol_filt  
    | Or of sol_filt * sol_filt       

  type state= term
  type state_set= State_set_type.t

  type transition_table = Transition_type.t
  type tree_automata

  type t = tree_automata
  type ('a, 'b) folder

  (*s Constructor of tree automata. The main difference with usual definitions
    of tree automata is that we here use an extended definition of states. States are
    terms (gasp!). States are terms constructed on a specific alphabet which is 
    what we call {\em state operators}. This make no difference with usual definition
    of states and tree automata if you consider only state operators
    of arity 0 (i.e. constant state symbol) then if q, state123, q0,
    q1, etc... are state operators of arity 0, then q, state123, q0,
    q1, etc... are states. However, if you define a state operator q
    of arity 1, and qa of arity 0, then qa, q(qa), q(q(qa)), ... are
    states. In fact, you can even define more complicated states,
    since state operators can transform any term (constructed on the alphabet and
    on state operators) into a state. For example, assume that your
    alphabet $\F$ contains operators: f of arity 2 and b of arity 0, and
    your state operators contain at least q of arity 1 and qa of arity
    0, then a, q(qa), q(q(qa)), q(b), q(f(b,b)), q(f(qa, b)), q(q(f(q(qa),
    b))), etc... are states.

    In most cases, state operators of arity
    greater than 0 are not needed. Nevertheless, note that to define a simple tree
    automaton with state set $\Q= \{q0, q2, q3\}$ and final states
    $\Q_f= \{ q2\}$, you will need to define state operators $q0, q2,
    q3$ of arity 0, and to give to the [make_automaton] function the
    state operators (of alphabet type), the state set corresponding to $\Q$ and then the
    set of final states representing $\Q_f$. However, it is much
    easier to use the parsing function of tree automata or, even
    simpler, the parsing function of the specification module, please
    have a look to the file [tutorial.mlml] for more details. *)

  val make_automaton:
     alphabet ->
       alphabet ->
        state_set ->
           state_set ->
             transition_table -> 
	       transition_table -> t

  (* build an automaton from a finite term list, a string label for states and an integer *)

  val term_set_to_automaton: alphabet -> term list ->  string ->  int -> (t * int) 
    
  (*s accessors of automata *)
  val get_alphabet : t -> alphabet
  val get_state_ops : t -> alphabet
  val get_states : t -> state_set
  val get_final_states : t -> state_set
  val get_transitions : t -> transition_table
  val get_prior : t -> transition_table
      
  (*s Prettyprint of tree automata. The first thing to be able to do with an
   automaton is to display it. *)      

  val print: t -> unit

  val to_string : t -> string


  (*s Now, we find the {\bf boolean operations} on tree automata. *)
  (* First of all, intersection of two tree automata.
     This function produces a tree automaton with structured states
     (states that are in fact products of states) and structured
     state sets (symbolic form of state set products). In order
     to obtain a full tree automaton with constructed state sets, 
     apply accessibility cleaning (defined in the following) on it. *)

  val inter : t -> t -> t

  (* union of two tree automata 
     (by renaming and union of transition tables, state set, 
     final state sets etc...). *)

  val union : t -> t -> t


  (* The complement operation. *)

  val inverse : t -> t
      
   (* The automaton recognizing the subtraction of langages: subtract L(a2) to L(a1)  *)

  val subtract : t -> t -> t

  (* Decision of inclusion between two langages: is L(a1) included in L(a2)? *)

  val is_included : t -> t -> bool

  (* Decision of the emptyness of a {\em language} recognized by a 
     tree automaton. *)

  val is_language_empty : t -> bool

  (* Are the transitions recursive? *)

  val is_recursive : transition_table -> bool


  (* Is the recognised language finite? *)

  val finite_recognized_language : t -> bool

  (*s Make a run of a tree automaton: verify if a term [t] rewrites into 
     state [q] with regards to transitions of automaton [a]. This is not the 
     usual definition of a run, but the usual one can easily be obtained from
     this one. *)

  val run : term -> state -> t -> bool


  (*s The determinisation function: given a tree automaton it gives an
     equivalent deterministic one. *)

  val determinise : t -> t


  (*s Completion of tree automaton... in a non-deterministic way i.e.,
     the result is a non-deterministic tree automaton. If a
     deterministic one is needed, it needs to be determinised afterwards. *)

  val make_complete : t -> t


  (*s Construction of an automaton recognizing {\em reducible terms}. 
     Starting from an alphabet [a] and a TRS [r] built on [a], this function
     constructs the tree automaton recognizing terms reducible by [r]. *)

  val make_red_automaton :
    alphabet -> Transition_type.t -> t


  (*s Construction of an automaton recognizing {\em irreducible terms}. 
    Starting from an alphabet [a] and a TRS [r] built on [a], this function
    constructs the tree automaton recognizing terms irreducible by [r].
    The result is a deterministic complete tree automaton, it may be 
    cleant afterwards with [simplify] if necessary.

    This implements a standard algorithm that is usually not efficient at all.
    For a better efficiency, use the next function called [nf_opt]. *)

	 
  val nf_automaton :
    alphabet -> transition_table -> t


  (* This one is usually more efficient than the previous one
     in practice. However the result is also slightly different: the produced
     tree automaton is not necessarily deterministic nor complete! *)
	
  val nf_opt :
    alphabet -> transition_table -> t


  (*s Cleaning of tree automata *)
      
  (* Accessibility cleaning of tree automaton: 
     retrieves all states that do not recognize any term. *)

  val accessibility_cleaning : t -> t
      

  (* Utility cleaning:
     retrieves all dead states.
     For utility cleaning on an automaton with structured state sets
     (obtained for example by application of an intersection operation
     use [accessibility_cleaning] before this one. *)

  val utility_cleaning : t -> t


  (* Accessibility cleaning followed by utility cleaning *)

  val clean : t -> t


  (* Simplification of tree automaton: a renumbering of the result of
     cleaning (accessibility + utility) of the tree automaton.
     Useful for deciding if the langage recognized by an automaton
     a is empty. If it is then [is_emtpy(simplify a)] is [true] *)

  val simplify : t -> t


  (*s State Renumbering *)


  (* This function rewrites state labels in a tree 
     automaton [a] thanks to a term rewriting system [r] on states. 
     Be careful!  for state sets including states q1, q2 for
     example and if you use structured states labels like q(f(q1,q2)),
    if q1 and q2 are to be renamed into q3 and q4 respectively, then
     so is q(f(q1,q2)) which is renamed into q(f(q3,q4))!!*)
      
  val rewrite_state_labels :
    t -> transition_table -> t
	
  (* This function transforms a rewriting rule list (over states) used for state rewriting 
     into an equivalent terminating one (by building some equivalence classes first) *)

  val simplify_equivalence_classes : rule list -> rule list
	

  (* Automatic renumbering of a tree automaton.
     To apply this function on an automaton with structured state 
     sets (obtained by intersection for example),
     use [accessibility_cleaning] before this one. *)

  val automatic_renum : t -> t 

  (*s For saving an automaton to disk, see function
    [save_automaton] in the module specification. *)

  (* \par \bigskip 

     \hrulefill\ {\Large \bf                   Low level functions      } \hrulefill\ \par \bigskip *)
  
  (*s Emptyness of an {\em automaton}, i.e. emptyness of its transition table. 
     For checking of the language apply simplify function before) i.e.,
     a is a tree automaton recognizing an empty langage if and only if
     [is_empty(simplify a)] is [true]. *)

  val is_empty : t -> bool

  (*s Modification of final state set. *)

  val modify_final : t -> state_set -> t


  (*s Modification of prior transitions. *)

  val modify_prior : t -> transition_table -> t

 (*s Modification of state operators. *)

  val modify_state_ops : t -> alphabet -> t

 (*s Modification of state set. *)

  val modify_states : t -> state_set -> t

 (*s Modification of state operators. *)

  val modify_transitions : t -> transition_table -> t


  (*s Construction of a state from a symbol with arity 0. Recall that
    a state is a term! *)

  val make_state : symbol -> state


  (*s Construction of a state config from a state. A state
     config is a configuration (i.e. a lhs or a rhs of a transition) that is
     a state. For example: in $q1 \rw q2$,  $q1$ is a state configuration. *)

  val make_state_config : state -> term

      
  (*s Construction of a new transition *)

  val new_trans : symbol -> state list -> state -> rule
    

  (*s Is a configuration a state configuration? A state
     config is a configuration (i.e. a lhs or a rhs of a transition) that is
    a state. For example: in $q1 \rw q2$,  $q1$ is a state configuration. *)

  val is_state_config : term -> bool

      
  (*s State label of a state in a state configuration. *)

  val state_label : term -> state

  val lhs : rule -> term
  val rhs : rule -> term

      
  (*s Top symbol of a transition *)

  val top_symbol :
    rule -> symbol

	
  (*s Is a transition normalized? i.e. of the form $f(q1, \ldots,qn)
    \rw q'$ where $q1, \ldots,qn$ are states. *)

  val is_normalized : rule -> bool


  (*s Construction of the list of states of the left hand side of a transition. *) 

  val list_state : rule -> state list


  (*s Construction of the state set formed by the states of all the transition of the
    transition table. *)

  val states_of_transitions :
    transition_table -> state_set


  (*s Normalization of epsilon transitions of the form [q1]$\rw$[q2]
    with regards to a given transition table [delta]. *)

  val normalize_epsilon :
    state ->
      state ->
        transition_table -> transition_table
	    

  (*s Normalization of a transitions table [ltrans] with new 
     states whose labels are [label^j] where [j] starts
     from [i]. It returns a triple with the new normalized transition
     table and the new state operator alphabet as well as the integer
     n+1 where n is the number of the last assigned new state. [delta] is simply 
     used to normalise epsilon transitions found in [ltrans] *)

  val normalize :
    transition_table ->
      transition_table ->
        string -> int -> transition_table * int * alphabet


  (*s Similar to normalize but produces a deterministic set of transition *)

  val normalize_deterministic :
    transition_table ->
      transition_table ->
        string -> int -> transition_table * int * alphabet

  (*s Matching of a term (ground or with variables) on a 
     tree automaton configuration with regard to a transition list
     (here given as a folder of transitions sorted by top symbol
     and right-hand side (state). *)

  val matching :
     term ->
       term ->
        (symbol, (state, rule list) folder) folder ->
          substitution list

	    
  (*s Puts a [sol_filt] (matching solution) in disjunctive normal form *)    
  val dnf : sol_filt -> sol_filt

  (*s checks if a list of associations is a substitution i.e., a same variable cannot 
      be mapped to different values. The substitution has to be given in a singleton list. The result
      is the empty list if the substitution is not valid *)

  val check_subst : substitution list -> substitution list

	
  (*s Simplification of matching solutions, by propagating Bottom solutions into
     the formula and retrieving Bottom occuring in disjunctions and retrieving
     conjunctions where Bottom occurs *)

  val simplify_sol : sol_filt -> sol_filt
	    
  (*s Constructs the disjointness constraint.  This is used to check
  that there is no non-linear lhs of a rule (say f(x,x)) and no lhs of
  a transition (say f(q1,q2)) such that the language recognized by q1
  and q2 are not disjoint. The non-linear lhs are given in a list of
  terms [l], the transitions are given as a folder [f] of transitions
  sorted by top symbol and right-hand side (state), and the result is
  a list of list of states whose disjointness has to be checked. *)


  val disjointness_constraint :
    term list ->
      (symbol, (state, rule list) folder) folder ->
        state list list 
	  

  (*s Is a term [t1] rewritten into a state [q] (special term) by transitions
     contained in the folder [f].*)

  val is_recognized_into :
    term ->
      state ->
        (symbol, (state, rule list) folder) folder -> bool


  (*s similar to the [is_recognized_into] but in the particular case where the transition 
     is an epsilon transition 
     [q1]$\rw$[q2], this consists in verifying that all the
    transitions going to [q1] are already going to [q2]. Transitions
    are given into a transition table [delta].
     *)

  val is_covered :
    Configuration_type.t ->
      Configuration_type.t ->
	transition_table -> bool

  (*s Parsing of a tree automaton with regards to an alphabet. For
    syntax, have a look to the [example.txt] file. See also the
    [file_parse] function of the module specification [specification.mli].*) 

  val parse : alphabet -> Genlex.token Stream.t -> t


  (*i*)
  (* ------- FOLDER manipulation functions ------------------------------- *)

  (* cartesian product of transition folder (for intersection and unions) *)
  val folder_cartesian_product : (symbol, rule list) folder -> (symbol, rule list) folder -> rule list
  (* head and tail of a folder *)
  val folder_hd : ('a, 'b) folder -> ('a * 'b)
  val folder_tail : ('a, 'b) folder -> ('a, 'b) folder 

  (* is a folder empty *)

  val is_empty_folder : ('a, 'b) folder -> bool

  (* folder assoc is similar to List.assoc *)
  val folder_assoc : 'a -> ('a, 'b) folder -> 'b

  (* adding a transition into a folder according to a given criteria 
     (top symbol or rhs state) *)
  val folder_add :
    'a -> 'b -> (('b , 'a list) folder) -> ('b , 'a list) folder

 (* replacing the whole set of element of a folder associated with a 
    given criteria *)
  val folder_replace : 'a -> 'b -> ('b , 'a) folder -> ('b , 'a) folder
      
  (* a [bi_folder] is a folder of folder, for adding we thus need 2 
     criteria *)
  val bi_folder_add :
    'a ->
      'b ->
         'c ->
           ('b , ('c , 'a list) folder) folder -> ('b , ('c , 'a list) folder) folder

  (* membership of a transition in a [bi_folder] of transitions 
     categorized by symbol and then by state *)
  val bi_folder_mem :
    rule ->
      (symbol ,
       (state , rule list) folder) folder -> bool

  (* adding a list of transition to a folder ... transitions are not 
     added if they are already in the folder *)
  val bi_folder_add_trans_list :
    rule list ->
      (symbol ,
       (state , rule list) folder) folder ->
        (symbol ,
       (state , rule list) folder) folder

 (* Obtain configurations from a bifolder corresponding to a given top 
    symbol symb (of the lhs) and a state q (the rhs) *)
  val configs_from_symbol_to_state :
     'a ->
       'b ->
        ('a , ('b , rule list) folder) folder ->
          term list

  (* flattens a folder into a transition list *)
  val folder_flatten : ('a , 'b list) folder -> 'b list

  val bi_folder_flatten : ('a , ('b , 'c list) folder) folder -> 'c list
      
  (* [transitions_by_symbol] returns the folder of transitions in trs
     gathered according to the top symbol of the lhs of each rule *)
  val transitions_by_symbol :
    rule list ->
      (symbol , rule list) folder
      
  (* [transitions_by_state]returns the folder of transitions in trs
     gathered according to the rhs of each rule (a state) *)
  val transitions_by_state :
    rule list ->
      (state , rule list) folder

  (* [transitions_by_state_by_symbol] returns the folder of folders of
     transitions in trs gathered according to its top symbol and then
     according to the rhs of each rule (a state)*)
  val transitions_by_state_by_symbol :
    rule list ->
      (symbol ,
       (state , rule list) folder) folder

  (* Rough union of two tree automata 
     (using an union of transition table...). *)

  val make_fast_union : t -> t -> t

(*i*)
end 

