(* Tabi - A Tree Automata Browsing Interface
   Copyright (C) 2004 Thomas Genet and [Boinet Matthieu, Brouard Robert, 
        Cudennec Loic, Durieux David, Gandia Sebastien, Gillet David, 
        Halna Frederic, Le Gall Gilles, Le Nay Judicael, Le Roux Luka, 
        Mallah Mohamad-Tarek, Marchais Sebastien, Martin Morgane, 
        Minier François, Stute Mathieu] -- aavisu project team for
        french "maitrise" level (4th University year) 2002-2003 at
	IFSIC/Universite de Rennes 1. 


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

(* Tabi - A Tree Automata Browsing Interface
   Copyright (C) 2004 Thomas Genet and [Boinet Matthieu, Brouard Robert, 
        Cudennec Loic, Durieux David, Gandia Sebastien, Gillet David, 
        Halna Frederic, Le Gall Gilles, Le Nay Judicael, Le Roux Luka, 
        Mallah Mohamad-Tarek, Marchais Sebastien, Martin Morgane, 
        Minier François, Stute Mathieu] -- aavisu project team for
        french "maitrise" level (4th University year) 2002-2003 at
	IFSIC/Universite de Rennes 1. 


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

(*****************************************************************************************
*                         visualisation group                                            *
*                                                                                        *
*                  - Le Nay Judicael                                                     *
*                  - Halna Frederic                                                      *
*                  - Gandia Sebastien                                                    *
*                  - Mallah Mohamad-Tarek                                                *
******************************************************************************************)



(************************************
*          opening of Tk            *
*************************************)

open Evts;;
open Gest;;
open Tk;;
open Specifs;;



(**************************************************
* function to get the nieme element of the listbox*
***************************************************)

let rec recupnieme = function 
  ([],i)-> ""
  |(a::l,0) ->a
  |(a::l,i)-> (recupnieme (l,(i-1)))
;;

let rec list_string_to_string = function 
    [] -> ""
   | a::l -> a^(list_string_to_string l);;


(**************************************************
* function to browse the historic and the random  *
***************************************************)

let rec concat = 
  function ([],[]) -> []
    |(l,[]) -> l
    |([],l) -> l
    |( a::m , l) -> a::(concat (m,l))
;;

let rec regroupehist  = 
  function
      []    ->[]
    |e::[]->(parcourshist1 e)
    |e::l -> concat((parcourshist1 e ),","::(regroupehist l))

and
    
parcourshist1 = 
  function
      State {symbol = a; fromstate =_ ; zone = (x1,y1,_,_); ident = _; linear = _ } -> a::[]
(*traitement d une feuille*)
    |(Node ({symbol = a; fromstate =_ ; zone =(x1,y1,_,_) ; ident =_; linear = _ }, [] ))->
a::(regroupehist [])
    |(Node ({symbol = a; fromstate =_ ; zone =(x1,y1,_,_) ; ident =_; linear = _ }, l ))->
concat(a::"("::(regroupehist l),")"::[])

and

parcourshist = 
  function
      State {symbol = a; fromstate =_ ; zone =(x1,y1,_,_) ; ident = _; linear = _ } -> a::[]
(*traitement d une feuille*)
    |(Node ({symbol = a; fromstate =_ ; zone =(x1,y1,_,_) ; ident =_; linear = _ }, [] ))->
	a::(regroupehist [])
    |(Node ({symbol = a; fromstate =_ ; zone =(x1,y1,_,_) ; ident =_; linear = _ }, l ))->
	concat((a::"("::(regroupehist l)),")"::[]);;

let rec termtostringhist  = 
  function 
      []-> ""
    |e::[] -> e
    |e::l -> e^(termtostringhist l)
;;

let rec list_term_to_list_stringhist = 
  function
      [] -> []
    | e::[] -> (termtostringhist (parcourshist e))::[]
    | e::l  -> (termtostringhist (parcourshist e))::(list_term_to_list_stringhist l);;

let rec get_term_list = 
  function
      [] -> []
    | (term,ident)::l -> term::(get_term_list l);;



let launch(a: automaton)=
  let toplevel = openTk() in
(************************************
*           Title setting           *
*************************************)

    Wm.title_set toplevel " Tabi ";


(************************************
*           global variables         *
*************************************)
    let presenthelp = ref 0 in
    let presente = ref 0 in (* presente=1 when a listbox of choices is opened *)
    let historic = ref 0 in (* historic=1 when historic is opened *)
    let readybrowser = ref 0 in(* readybrowser=1 when a browser is opened *)
    let num_undo = ref 0 in (* number of undo *)
    let decalTextRecX = ref 0 in (* horizontal position of the term *)
    let decalTextRecY = ref 0 in (* vertical position of the term *)
    let list_f = ref ["Arial 9";"Arial 18";"Arial 36"; "Arial 72"] in (* list of font *)
    let i_font = ref "Arial 9" in (* font current *)
    let ran_depth = ref 100 in
    let ran_time = ref 2.0 in
    let ran_number = ref 50 in

(* state names for interactive state merging *)
    let first_merge_state= ref "" in
    let second_merge_state= ref "" in
    let merge_list= ref ([]: string list) in
      
      
    (************************************
     * creation of the general canvas    *
     *************************************)
      
    let width = Evts.canvas_width in
    let height = Evts.canvas_height in
    let autozoom= Evts.zoom_auto in
    let menu_bar_height= 20 in
      
    let can = 
      Canvas.create 
      ~width: !width
      ~height: !height
      ~borderwidth:1 
      ~scrollregion:(0,0,!width,!height) 
      ~confine:true
      ~relief:`Sunken 
      ~background:`White 
	toplevel in
      
    let remove_merge_sel ()=
      begin
	Canvas.delete can [(`Tag "merge_sel")];
	first_merge_state:= "";
	second_merge_state:= ""
      end in
      
    let alert mesg= 
      let top_message= Toplevel.create toplevel in
	Wm.title_set top_message "Message";
	let can_m= Canvas.create
		   ~width: 600
		   ~height: 70
		   ~borderwidth:1
		   ~confine: true
		   ~relief:`Sunken
		   ~background: `White
		     top_message
	in 
	let texte_m=
	  Canvas.create_text
	  ~x:10
	  ~y:10
	  ~font: "Arial 16"
	  ~anchor: `Nw
	  ~text: mesg
	    can_m
	in 
	  (Canvas.addtag can_m
	   ~tag: "texte_m"
	   ~specs: [`Withtag texte_m];
	   pack
	   ~fill: `Both
	   ~expand: true
	     [can_m]);
	  update();
	  top_message in
      
    let load_message ()=
      begin
	let texte_m= 
	  Canvas.create_text
	  ~x: 10
	  ~y: 10
	  ~font: "Arial 16"
	  ~anchor: `Nw
	  ~text: "Loading! Please wait..." 
	    can
	in
	  (Canvas.addtag can
	   ~tag: "load"
	   ~specs: [`Withtag texte_m];
	   pack
	   ~fill: `Both
	   ~expand: true
	     [can]);
	  update();
      end
    in
    let message mesg=
      let top_error = Toplevel.create toplevel
      in
	Wm.title_set top_error "Message!";
	let butquit = Button.create
		      ~width:2
		      ~text: "Ok"
		      ~command: (function _ -> destroy top_error)
			top_error
	in
	let can_e= Canvas.create
		   ~width: 600
		   ~height: 180
		   ~borderwidth:1
		   ~confine: true
		   ~relief:`Sunken
		   ~background: `White
		     top_error;
	in 
	let texte_e=
	  Canvas.create_text
	  ~x:10
	  ~y:10
	  ~font: "Arial 16"
	  ~anchor: `Nw
	  ~text: mesg
	    can_e
	in 
	  (Canvas.addtag can_e
	   ~tag: "texte_e"
	   ~specs: [`Withtag texte_e];
	   pack
	   ~side: `Bottom
	     [butquit];
	   pack
	   ~fill: `Both
	   ~expand: true
	     [can_e];
	   update()) in
      
      
    let confirmation mesg (yes: unit -> unit) (no: unit -> unit)=
      let top_conf = Toplevel.create toplevel in
	(Wm.title_set top_conf "Confirmation";
	 let butok = Button.create
		     ~width:2
		     ~text: "OK"
		     ~command: (fun _ -> destroy top_conf; yes())
		       top_conf
	 in
	 let butcancel = Button.create
			 ~width:2
			 ~text: "Cancel"
			 ~command: (fun _ -> destroy top_conf; no())
			   top_conf
	 in
	 let can_e= Canvas.create
		    ~borderwidth:1
	       ~confine: true
		    ~relief:`Sunken
		    ~background: `White
		      top_conf;
    in 
	 let texte_e=
      Canvas.create_text
	   ~x:10
	   ~y:10
	   ~font: "Arial 16"
	   ~anchor: `Nw
      ~text: mesg
	can_e
	 in 
	   (Canvas.addtag can_e
	    ~tag: "texte_e"
	    ~specs: [`Withtag texte_e];
	    pack
	    ~side: `Left
	      [butok];
	    pack
	 ~side: `Right
	      [butcancel];
	    pack
	    ~fill: `Both
	    ~expand: true
	      [can_e] ;
	    update())) in


    let browsing_style ()=
      let top_conf = Toplevel.create toplevel in
	(Wm.title_set top_conf "Browsing style";
	 let butok = Button.create
		     ~width:7
		     ~text: "Final states"
		     ~command: (fun _ -> Gest.augmentAutoFinal();destroy top_conf)
		       top_conf
	 in
	 let butcancel = Button.create
			 ~width:7
			 ~text: "All states"
			 ~command: (fun _ -> Gest.augmentAutoAll();destroy top_conf)
			   top_conf
	 in
	   (pack
	    ~side: `Left
	      [butok];
	    pack
	    ~side: `Right
	      [butcancel];
	    update())) in



(***************************************************
* creation of the scrollbars of the general canvas *
****************************************************)

    let scrhc = Scrollbar.create ~background:`Blue toplevel 
    in
    let scroll_link_can_gen_h 
      (sb2:Widget.scrollbar Widget.widget) 
      (c2:Widget.canvas Widget.widget) : (unit) =
      Canvas.configure 
      ~xscrollcommand:(Scrollbar.set sb2) 
	c2;
      Scrollbar.configure 
      ~command:(Canvas.xview c2)  
      ~orient:`Horizontal
	sb2 
    in
      scroll_link_can_gen_h scrhc can;
      
      let scrvc = Scrollbar.create 
		  ~background:`Blue 
		    toplevel 
      in
      let scroll_link_can_gen_v 
	(sb:Widget.scrollbar Widget.widget) 
	(c:Widget.canvas Widget.widget) : (unit) =
	Canvas.configure 
	~yscrollcommand:(Scrollbar.set sb) 
	  c;
	Scrollbar.configure 
	~command:(Canvas.yview c)
	~orient:`Vertical 
	  sb
      in
	scroll_link_can_gen_v scrvc can;
	
	pack 
	~side:`Right  
	~fill:`Y 
	  [scrvc];
	pack 
	~side:`Bottom 
	~fill:`X 
	  [scrhc] ;


(************************************
*    function to display the term   *
*************************************)
  
	let place_texte (c:string) (x:int) (y:int) (z:int) (t:int) (f:font) :(unit) =
	  
	  let item = 
	    Canvas.create_text
	    ~text:c
	    ~font: f
	    ~tags: ["box"]
	    ~x:(x+ ((Cotes.largPixelsString c f)/2)+ !decalTextRecX)
	    ~y:(y+ ((Cotes.hautPixelsString c f)/2)+ !decalTextRecY)
	    ~fill:(`Color "Black")
	      can
	  in
	    Canvas.addtag can 
	    ~tag:"term" 
	    ~specs:[`Withtag item]
	in 
	  
	let place_texte_parenth (c:string) (x:int) (y:int) (z:int) (t:int) (f:font) :(unit) =
	  
	  let item = 
	    Canvas.create_text 
	    ~text:(c^"(") 
	    ~font: f 
	    ~tags: ["box"]
	    ~x:(x + (((Cotes.largPixelsString c f) + (Cotes.largPixelsString "(" f))/2) + !decalTextRecX) 
	    ~y:(y + ((Cotes.hautPixelsString c f)/2) + !decalTextRecY) 
	    ~fill:(`Color "Black") 
	      can
	  in
	    Canvas.addtag can 
	    ~tag:"term" 
	    ~specs:[`Withtag item];
	    
	    let item =    
	      Canvas.create_text 
	      ~text:(")")
	      ~font:f
	      ~tags: ["box"]
	      ~x:(z- ((Cotes.largPixelsString ")" f)/2)+ !decalTextRecX)
	      ~y:(y+ ((Cotes.hautPixelsString c f)/2)+ !decalTextRecY)
	      ~fill:(`Color "Black")
		can
	    in
	      Canvas.addtag can 
	      ~tag:"term" 
	      ~specs:[`Withtag item]
	in
	  
	let place_texte_centre (c:string) (x:int) (y:int) (z:int) (t:int) (f:font) :(unit) =
	  
	  let item = 
	    Canvas.create_text
	    ~text:c
	    ~font:f
	    ~tags: ["box"]
	    ~x:(x+ ((z-x)/2)+ !decalTextRecX)
	    ~y:(y+ ((Cotes.hautPixelsString c f)/2)+ !decalTextRecY)
	    ~fill:(`Color "Black")
	      can
	  in
	    Canvas.addtag can 
	    ~tag:"term" 
	    ~specs:[`Withtag item]
	in
	  
	  
	(*******************************************************
	 *  function to browse the tree with two different mode *
	 ********************************************************)
	  
	let trace_trait l =  
	  let gug = Canvas.create_line ~xys:l ~tags: ["box"] can in 
	    Canvas.addtag can ~tag:"term" ~specs:[`Withtag gug] in
  
let rec parcFils1 (l: term list) (font: font) : (unit) =
  (* When the father is in linear mode *)
  match l with 
    | []    -> ()
    | t::[] ->
	parcours2 t font
    |  t::l  ->
	 begin
	   match t with
	     | State elem 
	     | Node (elem, _) ->
		 let (x1,y1,x2,y2) = elem.zone in
		   parcours2 t font;
		   place_texte (",") (x2) (y1) (x2) (y2) (font);
		   parcFils1 l font;
	 end
	  and
      
      parcFils2 (l: term list) (font : font) (abs:int) (ord:int): (unit) =
	 (*  When the father is in tree mode *)
	 match l with 
	   | []    -> ()
	   | t::[] ->
	       begin
		 match t with
		   | State elem
		   | Node (elem, _) ->
		       let (x1,y1,x2,y2) = elem.zone in
		       let xmiddle = (x1+((x2-x1)/2)) in
			 trace_trait [ 
			   abs+(!decalTextRecX),ord+(!decalTextRecY);
			   xmiddle+(!decalTextRecX),y1+(!decalTextRecY);];
			 parcours2 t font
	       end
	   | t::l  ->
	       begin
		 match t with
		   | State elem
		   | Node (elem, _) ->    
		       let (x1,y1,x2,y2) = elem.zone in
		       let xmiddle = (x1+((x2-x1)/2)) in
			 trace_trait [
			   abs+(!decalTextRecX),ord+(!decalTextRecY); 
			   xmiddle+(!decalTextRecX),y1+(!decalTextRecY);];
			 parcours2 t font;
			 parcFils2 l font abs ord
	       end
	       
		 and
	     
	     parcours2 (t:term) (font:font) : (unit) =
		match t with
		  | State {symbol=a ; fromstate=_ ;zone = (x1,y1,x2,y2);ident = _; linear = _} ->
		      place_texte a x1 y1 x2 y2 font
			
		  | Node ({symbol=a ; fromstate=_ ;zone = (x1,y1,x2,y2);ident = _; linear = valeur}, l) ->
		      if (valeur)
		      then
			begin
			  if (l=[])
			  then place_texte (a) (x1) (y1) (x2) (y2) (font)
			  else place_texte_parenth (a) (x1) (y1) (x2) (y2) (font);
			  parcFils1 l font
			end
		      else
			begin
	  let xmiddle = (x1+((x2-x1)/2)) in
	    begin
	      place_texte_centre a x1 y1 x2 y2 font;
	      let abs= xmiddle in
	      let ord= y1 + ( Cotes.hautPixelsString "" font) in
		parcFils2 l font abs ord
	    end
			end in

  
let parcours (t:term) (font:font) : (unit) =
  match t with
    | State {symbol=_ ; fromstate=_ ;zone = (x1,y1,x2,y2);ident = _; linear = _} 
    | Node ({symbol=_ ; fromstate=_ ;zone = (x1,y1,x2,y2);ident = _; linear = _}, _) ->
	begin
	  if ((!width - (x2 - x1)) > 0)
	  then 
	    begin
	      decalTextRecX := (!width - (x2 - x1))/ 2;
	      if ((!height - (y2 - y1)) > 0)
	      then decalTextRecY := (!height - (y2 - y1))/ 2
	    end;
	  parcours2 (t) (font);
	  let box= Canvas.create_rectangle 
		   ~x1: (x1+ !decalTextRecX)
		   ~x2: (x2+ !decalTextRecX)
		   ~y1: (y1+ !decalTextRecY)
		   ~y2: (y2+ !decalTextRecY)
		   ~fill:`White
		   ~outline:`White
		     can in
	    Canvas.addtag can ~tag:"box" ~specs: [`Withtag box];
	    Canvas.raise can (`Tag "term")
	end in



(************************************
* order bind to the random          *
*************************************)

let send_order_rand (o :Specifs.order) :(Specifs.return_code) = 
  match o with
  |Refresh(t, f) ->  
      let trouve = Canvas.find can [`All] 
      in
      Canvas.delete can trouve ;
      i_font:=f;
    let _ =parcours t f 
  in 
    Return_Refresh 
 |_ ->  failwith "Ordre non implemente a ce jour desole une prochaine fois peut etre, merci d'etre passe"
in
  
(*************************************************
 *     creation of the window of the random       *
 **************************************************)
  
let show_random (liste_terme:term list) :unit= 
  let top_rand = Toplevel.create toplevel 
  in
    Wm.title_set top_rand "Random" ;
    
    let liste_r = list_term_to_list_stringhist liste_terme 
    in
    let listbr = 
      Listbox.create 
      ~height:14 
      ~width:70 
	top_rand
    in
      Listbox.insert listbr 
      ~index:`End 
      ~texts:liste_r;
      
      let scrh = 
	Scrollbar.create   
	~background:`Red 
	  top_rand
      in
      let scroll_link_rand_h (sb2 :Widget.scrollbar Widget.widget) (lb2 :Widget.listbox Widget.widget) :unit =
    Listbox.configure 
      ~xscrollcommand:(Scrollbar.set sb2) 
      lb2;
	Scrollbar.configure 
      ~command:(Listbox.xview lb2) 
	~orient:`Horizontal 
	  sb2
      in
	scroll_link_rand_h scrh listbr;
	
	let scr = 
	  Scrollbar.create 
	  ~background:`Red 
	    top_rand
	in
	let scroll_link_rand (sb :Widget.scrollbar Widget.widget) (lb :Widget.listbox Widget.widget) :unit =
	  Listbox.configure 
	  ~yscrollcommand:(Scrollbar.set sb) 
	    lb;
	  Scrollbar.configure 
	  ~command:(Listbox.yview lb)
	  ~orient:`Vertical 
	    sb
	in
  scroll_link_rand scr listbr;
	  
	  let button_quit = 
	    Button.create 
	    ~text:"quit random" 
	    ~command:(fun () -> 
			destroy top_rand;
			presente:=0)
	      top_rand 
	  in
  
	    pack 
	    ~side:`Bottom 
	      [button_quit];
	    pack 
	    ~side:`Right 
	    ~fill:`Y 
	      [scr];
	    pack 
	    ~side:`Bottom 
	    ~fill:`X 
	      [scrh];
	    pack 
	    ~side:`Left 
	    ~expand:true
	    ~fill:`Both
	      [listbr];
	    
	    bind listbr
	    ~events:[`Destroy]
	    ~action: (function _ -> presente:=0);
	    
	    bind listbr 
	    ~events:[`ButtonPress]
	    ~fields:[`MouseY]
	    ~action:(function x -> 
		       let result = Listbox.nearest 
				      listbr 
				    ~y:x.ev_MouseY 
		       in
		       let num = (* obtain the integer from the [`Num of int] *)
			 match result with
			   | `Num num -> num
      in 
			 (try
			    (Evts.get_coord_in_box  
	      (fun t f -> send_order_rand(Refresh (t,f)) )
			       num)
			  with
			      Gest.Exn_error m | Evts.Erreur m -> message m);
			 destroy top_rand;
			 presente:=0) in


(************************************
*   function to get relative origin *
*************************************)
  
let originx = function (a,b) -> (int_of_float (a*.5000.0)) in
let originy = function (a,b) -> (int_of_float (a*.5000.0)) in
  

(************************************
 * order bind to the created listbox *
 *************************************)
  
let send_order_box (o :Specifs.order) :(Specifs.return_code) = 
  match o with
    |Refresh(t, f) ->  
       let trouve = Canvas.find can [`All] 
       in
	 Canvas.delete can trouve ;
	 i_font:=f;
	 let _ =parcours t f 
	 in 
	   Return_Refresh 
    |SendRandom (listterm) -> 
       let _ = 
	 show_random listterm;
       in Return_SendRandom
    |_ ->  failwith "Ordre non implemente a ce jour desole une prochaine fois peut etre, merci d'etre passe"
in


(************************************
* management of the historic        *
*************************************)
  
let show_historic (liste_terme:term list):unit= 
  
  let top_hist = Toplevel.create toplevel 
  in
    Wm.title_set top_hist "History" ;
    
    let liste_h = list_term_to_list_stringhist liste_terme 
    in
    let listb = 
      Listbox.create 
      ~height:14 
      ~width:70 
	top_hist
    in
      Listbox.insert listb 
      ~index:`End 
      ~texts:(List.rev liste_h);
      
      let scrh = 
	Scrollbar.create   
	~background:`Red 
	  top_hist
      in
      let scroll_link_hist_h (sb2 :Widget.scrollbar Widget.widget) (lb2 :Widget.listbox Widget.widget) :unit =
	Listbox.configure 
	~xscrollcommand:(Scrollbar.set sb2) 
	  lb2;
	Scrollbar.configure 
	~command:(Listbox.xview lb2) 
	~orient:`Horizontal 
	  sb2
      in
	scroll_link_hist_h scrh listb;
	
	let scr = 
	  Scrollbar.create 
	  ~background:`Red 
	    top_hist
	in
	let scroll_link_hist (sb :Widget.scrollbar Widget.widget) (lb :Widget.listbox Widget.widget) :unit =
	  Listbox.configure 
	  ~yscrollcommand:(Scrollbar.set sb) 
	    lb;
	  Scrollbar.configure 
	  ~command:(Listbox.yview lb)
      ~orient:`Vertical 
	    sb
	in
	  scroll_link_hist scr listb;
	  
	  let button_quit = 
	    Button.create 
      ~text:"quit history" 
	    ~command:(fun () -> destroy top_hist; historic:=0) 
      top_hist 
	  in
	    
	    pack 
	    ~side:`Bottom 
	      [button_quit];
	    pack 
	    ~side:`Right 
	    ~fill:`Y 
	      [scr];
	    pack 
	    ~side:`Bottom 
	    ~fill:`X 
	      [scrh];
	    pack 
	    ~side:`Left 
	    ~expand:true
	    ~fill:`Both
	      [listb];
	    
	    bind listb
	    ~events:[`Destroy]
	    ~action: (function _ -> historic:=0);
	    
	    bind listb 
	    ~events:[`ButtonPress]
	    ~fields:[`MouseY]
	    ~action:(function x -> 
		       let result = Listbox.nearest 
				      listb 
				    ~y:x.ev_MouseY 
		       in
		       let num = (* obtain the integer from the [`Num of int] *)
			 match result with
			   | `Num num -> num
		       in 
      let number_undo = (Listbox.size listb) - (num+1)- !num_undo 
      in
	num_undo:=!num_undo + number_undo;
	
	if number_undo<0 
	then 
	  Evts.redo (fun t f -> send_order_box(Refresh (t,f))) (-number_undo)
	else 
	  (try
	     (Evts.undo (fun t f -> send_order_box(Refresh(t,f))) number_undo)
	   with
	       Gest.Exn_error m | Evts.Erreur m -> message m);
	destroy top_hist;
	historic:=0) in



(************************************
*     creation of the merging rules listbox  
*************************************)
  
let mergelistbox (l :string list):(unit)=
  let toplist = Toplevel.create toplevel  
  in
    Wm.title_set toplist "Merging rules" ;
    let canlis = 
      Canvas.create 
      ~width:50 
      ~height:100 
	toplist 
    in
    let lis = Listbox.create 
	      ~height:5 
		canlis
    in
      Listbox.insert lis 
      ~index:`End 
      ~texts:l ;  
      let scr = 
	Scrollbar.create 
	~background:`Red 
	  canlis 
      in
      let scroll_link_choices (sb :Widget.scrollbar Widget.widget) (lb :Widget.listbox Widget.widget) :(unit) =
	Listbox.configure 
	~yscrollcommand:(Scrollbar.set sb) 
	  lb;
	Scrollbar.configure 
	~command:(Listbox.yview lb) 
	~orient:`Vertical 
	  sb 
      in
	scroll_link_choices scr lis;
	let button_quit = 
	  Button.create 
	  ~width:20 
	  ~text:"OK" 
	  ~command:(fun () -> 
		      destroy canlis;
		      destroy lis;
		      destroy scr;
		      destroy toplist;
		      presente:=0) 
	    canlis 
	in
	  pack 
	  ~expand:true    
	  ~fill:`Both
	    [canlis];
	  pack 
	  ~side:`Bottom 
	    [button_quit];
	  pack 
	  ~side:`Right 
	  ~fill:`Y 
	    [scr];
	  pack 
	  ~side:`Left 
	  ~expand:true
	  ~fill:`Both
	    [lis] ;
	  bind lis
	  ~events:[`Destroy]
	  ~action: (function _ -> presente:=0) in
  
  
(************************************
*     creation of the listbox       *
 *************************************)

let creerlistbox (l :string list) (coordx :int ) (coordy :int) :(unit)=
  
  let toplist = Toplevel.create toplevel  
  in
    Wm.title_set toplist "Choices" ;
    let canlis = 
      Canvas.create 
      ~width:50 
      ~height:100 
	toplist 
    in
    let lis = Listbox.create 
	      ~height:5 
		canlis
    in
      Listbox.insert lis 
      ~index:`End 
      ~texts:l ;
      
      let scrh = 
	Scrollbar.create 
	~background:`Red 
	  canlis 
      in
      let scroll_link_choices_h (sb2 :Widget.scrollbar Widget.widget) (lb2 :Widget.listbox Widget.widget) :(unit)  =
	Listbox.configure 
	~xscrollcommand:(Scrollbar.set sb2) 
	  lb2;
	
	Scrollbar.configure 
	~command:(Listbox.xview lb2) 
	~orient:`Horizontal 
	  sb2 
      in
	scroll_link_choices_h scrh lis;
	
	let scr = 
	  Scrollbar.create 
	  ~background:`Red 
	    canlis 
	in
	let scroll_link_choices (sb :Widget.scrollbar Widget.widget) (lb :Widget.listbox Widget.widget) :(unit) =
	  Listbox.configure 
	  ~yscrollcommand:(Scrollbar.set sb) 
	    lb;
	  Scrollbar.configure 
	  ~command:(Listbox.yview lb) 
	  ~orient:`Vertical 
	    sb 
	in
	  scroll_link_choices scr lis;
	  let button_random =
	    Button.create 
	    ~width:20
	    ~text:"choose random"
	    ~command:(fun () -> 
			destroy canlis;
			destroy lis;
			destroy scr;
			destroy scrh;
			destroy toplist;
			let top_alert= alert "Computing random terms of the language..." in
			  (try
			     (Evts.random  
				(fun l -> send_order_box(SendRandom l))
				!ran_depth
				!ran_time
				!ran_number)
			   with 
			       Gest.Exn_error m | Evts.Erreur m -> message m;presente:=0);
			  destroy top_alert)
	      canlis
	  in
	  let button_quit = 
	    Button.create 
	    ~width:20 
	    ~text:"close listbox" 
	    ~command:(fun () -> 
			destroy canlis;
			destroy lis;
			destroy scr;
			destroy scrh;
			destroy toplist;
			presente:=0) 
	      canlis 
	  in
	    pack 
	    ~expand:true    
	    ~fill:`Both
	      [canlis];
	    pack 
	    ~side:`Bottom 
	      [button_quit];
	    pack 
	    ~side:`Bottom 
	      [button_random];
	    pack 
	    ~side:`Right 
	    ~fill:`Y 
	      [scr];
	    pack 
	    ~side:`Bottom 
	    ~fill:`X 
	      [scrh] ;
	    pack 
	    ~side:`Left 
	    ~expand:true
	    ~fill:`Both
	      [lis] ;
	    
	    bind lis
	    ~events:[`Destroy]
	    ~action: (function _ -> presente:=0);
	    
	    bind lis 
	    ~events:[`ButtonPress]
	    ~fields:[`MouseY]
	    ~action:(function x -> 
		       let result = 
			 Listbox.nearest lis 
			 ~y:x.ev_MouseY 
		       in
		       let num = (* obtain the integer from the [`Num of int] *)
			 match result with
			   | `Num num -> num
		       in 
		       let listitem = Canvas.find can [`All]  
		       in 
			 Canvas.delete can listitem;
			 
			 Evts.get_coord_in_box  
			   (fun t f -> send_order_box(Refresh(t,f))) 
			   num ;
			 destroy toplist;
			 presente:=0; () ) in


(************************************
 *        postscript generation      *
 *************************************)
  
let write_postscript ()=
  let _= Canvas.postscript 
	 ~file:"tabi.ps" 
	   can 
  in ()
in
  
    
(************************************
 *         browser                   *
 *************************************)

    
let dos2unixpath (s: string): string=
  let i= ref 0 in
  let s2= String.create (String.length s) in
  (while !i < String.length s do
      (if s.[!i]='\\' then String.set s2 !i '/'
      else String.set s2 !i s.[!i];
      i:= !i+1)
  done;
  s2)

in
let base_path= ref ["/"] in
let is_dos (s: string): bool=
  if String.length s <=1 
  then
    (base_path:= ["/"];
    false)
  else 
    if (String.get s 1)=':'
    then
      (base_path:= [(String.sub s 0 3)];
       true)
    else 
      (base_path:= ["/"];
    false)
in
  
let cwd_path_list()=
  let rec paux (p: string): string list=
    try( 
      let i= String.index p '/' 
      in
	(String.sub p 0 i)::(paux (String.sub p (i+1) ((String.length p) - i -1)))
    )
    with Not_found -> [p]
  in
  let ps= Unix.getcwd() 
  in
    if is_dos ps 
    then paux ps
    else paux (String.sub ps 1 ((String.length ps) - 1))
  in
let funcslach (pathlist: string list): string list= 
let rec aux = function 
    [] -> []
  |a::l -> ("/"^a)::(aux l)
in
  match pathlist with
    [] -> []
  |s::l -> 
    if is_dos s then s::(aux l)
    else ("/"^s)::(aux l)
in
    
let current_path =ref (funcslach (cwd_path_list ())) in
let listdir = ref [] in
let listxml = ref [] in
  
let browser= function _ ->
  let top_browser = Toplevel.create toplevel 
  in
    Wm.title_set top_browser "Browser" ;
    
    let frame_bro = Frame.create top_browser
    in
      
    let can4 = 
      Canvas.create
      ~width:400 
      ~height:20 
      ~borderwidth:1
    in 
    let mess = 
      Message.create 
      ~width:200 
      ~text:" " 
	top_browser 
    in
    let entree = Entry.create frame_bro
    in
    let but = 
      Button.create
      ~text:"OK"
	frame_bro
    in
    let but2 = 
      Button.create
      ~text:"cancel"
      ~command:(fun () -> destroy top_browser;readybrowser:=0;current_path:=(funcslach (cwd_path_list ()));
		  listdir:=[];
		  listxml:=[])
	frame_bro
    in
    let can2 = 
      Canvas.create
      ~width:200 
      ~height:200 
      ~borderwidth:1 
      ~scrollregion:(0,0,200,200) 
      ~confine:true 
      ~relief:`Sunken 
      ~background:`White top_browser
    in  
    let lis2 = Listbox.create 
	       ~height:20 
		 can2
    in
      Listbox.insert 
      ~index:`End
      ~texts:[]
     lis2; 
      
      let scrh2 = 
	Scrollbar.create 
	~background:`Red 
	  can2
      in
      let scroll_link_choices_h2 (sb2 :Widget.scrollbar Widget.widget) (lb2 :Widget.listbox Widget.widget) :(unit)  =
	Listbox.configure 
	~xscrollcommand:(Scrollbar.set sb2) 
	  lb2;
    
	Scrollbar.configure 
	~command:(Listbox.xview lb2) 
	~orient:`Horizontal 
	  sb2 
      in
	scroll_link_choices_h2 scrh2 lis2;
	
	let scr2 = 
	  Scrollbar.create 
	  ~background:`Red 
	    can2 
	in
	let scroll_link_choices2 (sb :Widget.scrollbar Widget.widget) (lb :Widget.listbox Widget.widget) :(unit) =
	  Listbox.configure 
	  ~yscrollcommand:(Scrollbar.set sb) 
       lb;
	  
	  Scrollbar.configure 
	  ~command:(Listbox.yview lb) 
	  ~orient:`Vertical 
	    sb 
	in
	  scroll_link_choices2 scr2 lis2;
	  
	  let can3 = 
	    Canvas.create
	    ~width:200 
	    ~height:200 
	    ~borderwidth:1 
	    ~scrollregion:(0,0,200,200) 
	    ~confine:true 
	    ~relief:`Sunken 
	    ~background:`White top_browser
	  in   
	  let lis3 = 
	    Listbox.create 
	    ~height:20 
	      can3
	  in
	    Listbox.insert lis3 
	    ~index:`End
	    ~texts:[]; 
	    
	    let scrh3 = 
	      Scrollbar.create 
	      ~background:`Red 
		can3
	    in
	    let scroll_link_choices_h3 (sb2 :Widget.scrollbar Widget.widget) (lb2 :Widget.listbox Widget.widget) :(unit)  =
	      Listbox.configure 
	      ~xscrollcommand:(Scrollbar.set sb2) 
		lb2;
	      
	      Scrollbar.configure 
	      ~command:(Listbox.xview lb2) 
	      ~orient:`Horizontal 
		sb2 
	    in
	      scroll_link_choices_h3 scrh3 lis3;
	      
	      let scr3 = 
		Scrollbar.create 
		~background:`Red 
		  can3 
	      in
	      let scroll_link_choices3 (sb :Widget.scrollbar Widget.widget) (lb :Widget.listbox Widget.widget) :(unit) =
		Listbox.configure 
		~yscrollcommand:(Scrollbar.set sb) 
		  lb;
		
		Scrollbar.configure 
		~command:(Listbox.yview lb) 
		~orient:`Vertical 
		  sb 
	      in
		scroll_link_choices3 scr3 lis3;
		
		let my_ls path =
		  let dh = Unix.opendir path 
		  in
		    try
		      while (true) do
			begin
			  let tex=(Unix.readdir dh) in
(*
  if (Filename.check_suffix tex ".txt") or (Filename.check_suffix tex ".aut") 
  then
  listxml:=((tex::(!listxml)))
  else *)
			    if (Filename.check_suffix tex "..") 
			    then
			      listdir:=((tex::(!listdir)))	  
			    else
			      begin
				match ((Unix.stat ((list_string_to_string !current_path)^"/"^tex)).Unix.st_kind) with 
				    Unix.S_DIR ->	 listdir:=((tex::(!listdir)));  
				  |_ -> listxml:=((tex::(!listxml)));
  			      end;
			end
		      done
		    with End_of_file -> Unix.closedir dh 
		in
		  my_ls (list_string_to_string !current_path);
		  (Listbox.insert lis2 `End (List.sort String.compare !listdir));
		  (Listbox.insert lis3 `End (List.sort String.compare !listxml));
		  Message.configure mess ~text:(list_string_to_string !current_path);
		  
		  
		  pack 
		  ~side:`Bottom 
		    [frame_bro];
		  pack
		  ~side:`Right
		    [but2];
		  pack
		  ~side:`Right
		    [but];
		  pack
		  ~side:`Left 
		    [entree];
		  pack 
		  ~side:`Bottom 
		    [mess];
		  pack 
		  ~side:`Left 
		    [can2];
		  pack 
		  ~side:`Right 
		  ~fill:`Y 
		    [scr2];
		  pack 
		  ~side:`Bottom 
		  ~fill:`X 
		    [scrh2] ;
		  pack 
		  ~side:`Left 
		  ~expand:false 
		    [lis2];
		  pack 
		  ~side:`Right 
		    [can3];
		  pack 
		  ~side:`Right 
		  ~fill:`Y 
		    [scr3];
		  pack 
		  ~side:`Bottom 
		  ~fill:`X 
		    [scrh3] ;
		  pack 
		  ~side:`Left 
		  ~expand:false 
		    [lis3];
		  
		  bind top_browser
		  ~events:[`Destroy]
		  ~action: (function _ -> readybrowser:=0);
		  
		  bind lis2
		  ~events:[`ButtonPress]
		  ~fields:[`MouseY]
		  ~action:(function x -> 
			     let result = 
			       Listbox.nearest 
				 lis2 
			       ~y:x.ev_MouseY
			     in
			     let num = (* obtain the integer from the [`Num of int] *)
			       match result with
				 | `Num num -> num
			     in
			     let listpath = Listbox.get_range lis2 (`Num 0) `End 
			     in
			       if (recupnieme (listpath,num))="." 
			       then ()
			       else
				 begin
				   Listbox.delete lis2 (`Num 0) `End ;
				   Listbox.delete lis3 (`Num 0) `End ;
				   if (recupnieme (listpath,num))=".."
				   then
				     begin
				       current_path:=List.rev (List.tl (List.rev !current_path));
				       if (List.length(!current_path)=0) 
				       then current_path:=!base_path
				       else ();
				     end
				   else
				     current_path:=(concat (!current_path, ["/"^(recupnieme (listpath,num))]));
				   listdir:=[];
				   listxml:=[];
				   my_ls (list_string_to_string !current_path);
				   (Listbox.insert lis2 `End (List.sort String.compare !listdir));
				   (Listbox.insert lis3 `End (List.sort String.compare !listxml));
				   Message.configure mess ~text:(list_string_to_string !current_path);
				 end;
			       ());
		  
		  bind lis3
		  ~events:[`ButtonPress]
		  ~fields:[`MouseY]
		  ~action:(function x -> 
			     let result = 
			       Listbox.nearest lis3 
			       ~y:x.ev_MouseY
			     in
			     let num = (* obtain the integer from the [`Num of int] *)
			       match result with
				 | `Num num -> num
			     in
			     let listpath = Listbox.get_range lis3 (`Num 0) `End 
			     in
			       Listbox.delete lis3 (`Num 0) `End ;
			       current_path:=(concat (!current_path, ["/"^(recupnieme (listpath,num))]));
			       destroy top_browser; 
			       readybrowser:=0;
			       Canvas.delete can (Canvas.find can [`All]);
			       load_message();
			       (try(
				  Evts.file_open 
				      (fun t f -> send_order_box(Refresh(t,f))) 
				      (list_string_to_string !current_path);
				  merge_list:=[])
				  
				with
				    _ -> 
				      message "Bad automata file format!");
			       Canvas.delete can [(`Tag "load")];
			       update();
			       current_path:=(funcslach (cwd_path_list ()));
			       listdir:=[];
			       listxml:=[];
			       ());
		  
		  bind but
		  ~events:[`ButtonPress]
		  ~fields:[`MouseX;`MouseY]
		  ~action:(function x -> 
			     if ((Entry.get entree)=".") 
			     then ()
			     else
			       begin
				 if ((Entry.get entree)="..")
				 then
				   begin
				     current_path:=List.rev (List.tl (List.rev !current_path));
				     if (List.length(!current_path)=0) 
				     then current_path:=!base_path
				     else ();
				   end
				 else
				   current_path:=(concat (!current_path, ["/"^(Entry.get entree)])); 
				 Entry.delete_range entree (`Num 0) `End ;
				 Listbox.delete lis2 (`Num 0) `End ;
				 Listbox.delete lis3 (`Num 0) `End ;
				 listdir:=[];
				 listxml:=[];
				 my_ls (list_string_to_string !current_path);
				 (Listbox.insert lis2 `End (List.sort String.compare !listdir));
				 (Listbox.insert lis3 `End (List.sort String.compare !listxml));
				 Message.configure mess ~text:(list_string_to_string !current_path);
			       end;
			     ());
		  
		  bind entree
		  ~events:[`KeyPressDetail "Return"]
		  ~fields:[`MouseX;`MouseY]
		  ~action:(function x ->
			     if ((Entry.get entree)=".") 
			     then ()
			     else
			       begin
				 if ((Entry.get entree)="..")
				 then
				   begin
				     current_path:=List.rev (List.tl (List.rev !current_path));
				     if (List.length(!current_path)=0) 
				     then current_path:=!base_path
				     else ();
				   end
				 else
				   current_path:=(concat (!current_path, ["/"^(Entry.get entree)])); 
				 Entry.delete_range entree (`Num 0) `End ;
				 Listbox.delete lis2 (`Num 0) `End ;
				 Listbox.delete lis3 (`Num 0) `End ;
				 listdir:=[];
				 listxml:=[];
				 my_ls (list_string_to_string !current_path);
				 (Listbox.insert lis2 `End (List.sort String.compare !listdir));
				 (Listbox.insert lis3 `End (List.sort String.compare !listxml));
				 Message.configure mess ~text:(list_string_to_string !current_path);
			       end;
			     ()) in


(************************************
*    management of the orders       *
 *************************************)
  
let send_order_general (can:Widget.canvas Widget.widget)(o: order)  :return_code = 
  match o with
    | Refresh (term,font) ->
	let trouve = Canvas.find can [`All] 
      in
	  Canvas.delete can trouve ;
	  i_font:= font;
	  let _= parcours term font 
	  in  
	    Return_Refresh
	      
    | Choices (id,listtermident,x,y) -> 
	let _ = 
	  if !presente=0 
	  then 
	    begin
	      creerlistbox  (list_term_to_list_stringhist listtermident) x y ; 
	      presente:=1;
              num_undo:=0;
	    end
	  else ()
	in Return_Choices 
	     
    | SendHistory (listtermident) -> 
	let _ = 
	  if !historic=0
	  then 
	    begin 
	      show_historic (get_term_list (listtermident));
	      historic:=1;
	    end
	  else ()
	in Return_SendHistory 
	     
    | Refresh_without_autozoom (term,font) -> 
	let trouve = Canvas.find can [`All] 
	in
	  Canvas.delete can trouve ;
	  i_font:=font;
	  let _= parcours term font in Return_Refresh 
					 
    | _ -> failwith "Ordre non_ implemente a ce jour desole une prochaine fois peut etre, merci d'etre passe"
in

let send_order = send_order_general can in
  
  
(************************************
 *         help window               *
 *************************************)
  
let help = function _ -> 
  let top_help = Toplevel.create toplevel 
  in
    Wm.title_set top_help "Help" ;
    
    let butquit = Button.create
		  ~width:2
		  ~text:"Quit"
		  ~command:(fun _ -> destroy top_help;presenthelp:=0)
		    top_help
    in
    let can_h = Canvas.create 
		~width: 600
		~height: 140
		~borderwidth:1 
		~confine:true
		~relief:`Sunken 
		~background:`White 
		  top_help;
    in
      
    let texte_h = 
      Canvas.create_text 
      ~x:10
      ~y:10
      ~font:"Arial 16"
      ~anchor:`Nw
      ~text:
	"
Left_click                --> Unfold a state
Right_click             --> Fold a term
CTRL + Left_click   --> Tree mode for a whole subterm
SHIFT + Left_click  --> Term mode for a whole subtree
SHIFT + Right_click --> Term/Tree mode switch on one level
CTRL + Right_click  --> Select terms to merge
"
	
	can_h
    in 
      Canvas.addtag can_h
      ~tag:"texte_h"
      ~specs:[`Withtag texte_h];
      
      pack
      ~side:`Bottom
	[butquit];
      pack 
      ~fill:`Both
      ~expand:true
	[can_h] in
	
(************************************
*      depth of random              *
 *************************************)
let change_ran_depth = 
  function _ -> 
    let top_ran_d = Toplevel.create toplevel 
    in
      Wm.title_set top_ran_d "random maximum depth" ;
      let mes = 
	Message.create 
	~width:200 
	~text:("current value : "^(string_of_int(!ran_depth))) 
	  top_ran_d 
      in
      let entree = Entry.create top_ran_d
      in
      let but = 
	Button.create
	~text:"OK"
	~command:
	  (fun () -> 
	     (try
		(if (int_of_string(Entry.get entree)<1)
		 then 
		   ran_depth:=1
		 else ran_depth:=int_of_string(Entry.get entree))
	      with Failure ("int_of_string") -> ());
	     destroy top_ran_d)
	  top_ran_d
      in
	pack 
	~side:`Top 
	  [mes];
	pack 
	~side:`Left 
	  [but];
	pack 
	~side:`Right 
	  [entree] in
    
    
(************************************
 *      time of random              *
*************************************)
let change_ran_time = 
  function _ -> 
    let top_ran_t = Toplevel.create toplevel 
    in
      Wm.title_set top_ran_t "random time" ;
      let mes = 
	Message.create 
	~width:200 
	~text:("current value :  "^(string_of_float(!ran_time))) 
	  top_ran_t 
      in
      let entree = Entry.create top_ran_t
		     (* in
			Entry.configure !ran_time*)
      in
      let but = 
	Button.create
	~text:"OK"
	~command:(fun () -> 
		    (try
		       (if (float_of_string(Entry.get entree)<1.0)
			then ()
			else 
			  ran_time:=float_of_string(Entry.get entree))
		     with Failure "float_of_string" -> ());
		    destroy top_ran_t)
	  top_ran_t
      in
	pack
	~side:`Top
	  [mes];
	pack 
	~side:`Left 
	  [but];
	pack 
	~side:`Right 
	  [entree] in

(************************************
 *      ratio of random              *
*************************************)
let change_ran_num = 
  function _ -> 
    let top_ran_r = Toplevel.create toplevel 
    in
      Wm.title_set top_ran_r "random term number" ;
      let mes = 
	Message.create 
	~width:200 
	~text:("current value :"^(string_of_int(!ran_number))) 
	  top_ran_r 
      in
      let entree = Entry.create top_ran_r
      in
      let but = 
	Button.create
	~text:"OK"
	~command:
	  (fun () -> 
	     (try
		(if (int_of_string(Entry.get entree)<1)
		 then ()
		 else (); 
		 ran_number:=int_of_string(Entry.get entree))
	      with
		  Failure "int_of_string" -> ());
	     destroy top_ran_r)
	  top_ran_r
      in
	pack
	~side:`Top
	  [mes];
	pack 
	~side:`Left 
	  [but];
	pack 
	~side:`Right 
	  [entree] in
  
(************************************
 *         frame                     *
 *************************************)
  
let frame = Frame.create ~borderwidth: 1 toplevel in
  
  
(************************************
 *        menu bar                   *
 *************************************)
  
let barre = 
  Frame.create 
  ~background: `Red
  ~borderwidth:2
    (*~relief:`Raised *)
    frame 
in 
  
  
  
(************************************
 *    menubutton                     *
 *************************************)
  
let menubutton1 = 
  Menubutton.create 
  ~text:"File" 
  ~justify:`Left 
    barre 
in
  
let menu_file = 
  Menu.create  menubutton1 
in
  
  Menu.add_command 
  ~label:"Open File" 
  ~command:(fun _ -> 
	      if 
		
		((!readybrowser=1)
		 ||(!presente=1)
		 ||(!historic=1))
		
	      then ()
	      else 
		begin
		  readybrowser:=1;
		  browser();
		end;) 
    menu_file;
  
  Menu.add_command 
  ~label:"Print" 
  ~command:(fun () -> write_postscript()) 
    menu_file;
  
  Menu.add_command 
  ~label:"Exit" 
  ~command:(fun () ->  
	      confirmation "Do you really want to quit Tabi?"
		(fun () -> closeTk() ; merge_list:=[]) (fun () -> ()))
    menu_file;
  
  Menubutton.configure 
  ~menu:menu_file 
    menubutton1;
  
  let menubutton2 = 
    Menubutton.create 
    ~text:"Options" 
    ~justify:`Left 
      barre 
in
    
  let menu_options = 
    Menu.create menubutton2 
  in

    Menu.add_command 
  ~label:"Undo" 
    ~command:(fun () -> num_undo:=!num_undo+1;
		(try (Evts.undo (fun t f -> send_order (Refresh(t,f))) 1)
		 with
		     Gest.Exn_error m | Evts.Erreur m -> message m))
      
      menu_options;
    
    Menu.add_command 
    ~label:"Redo" 
    ~command:(fun () -> num_undo:=!num_undo-1;
		(try (Evts.redo (fun t f -> send_order (Refresh(t,f))) 1)
		 with
		     Gest.Exn_error m | Evts.Erreur m -> message m))
      menu_options;
    
    
    Menu.add_command 
    ~label:"Browsing style" 
    ~command:(fun () -> browsing_style())
      menu_options;
    
    
    Menu.add_command 
    ~label:"See merging rules" 
    ~command:(fun () -> if !presente=0 then (presente:=1; mergelistbox !merge_list))
      menu_options;
    
    
    Menu.add_command 
    ~label:"Random max depth" 
    ~command:(fun () -> change_ran_depth()) 
      menu_options;
    
    Menu.add_command 
    ~label:"Random max time" 
    ~command:(fun () -> change_ran_time()) 
      menu_options;
    
    Menu.add_command 
    ~label:"Random max term number" 
    ~command:(fun () -> change_ran_num()) 
      menu_options;
    
    Menu.add_command 
    ~label:"Show History" 
    ~command:(fun () -> 
		try (Evts.history (fun l -> (send_order (SendHistory l))))
		with
		    Gest.Exn_error m | Evts.Erreur m -> message m)
      menu_options;
    
    Menu.add_command 
    ~label:"Help"
    ~command:(fun () -> if !presenthelp=0 then begin
		help();presenthelp:=1;
	      end
	      else ())
      menu_options;
    
    Menubutton.configure 
    ~menu:menu_options 
      menubutton2;
    
    



    pack 
    ~side:`Left 
      [menubutton1];
    pack 
    ~side:`Left 
      [menubutton2];
    
    pack 
    ~fill:`X 
    ~side:`Left 
      [barre] ;
  
  
(************************************
 *       function for font           *
 *************************************)
let num_in_listf (f:font) :int =
  match f with
    | "Arial 9"  -> 1
    | "Arial 18" -> 2
    | "Arial 36" -> 3
    | "Arial 72" -> 4
    | _ -> 2
in
let font_in_listf (i:int) :font =
  match i with
    | 1 -> "Arial 9"
    | 2 -> "Arial 18"
	| 3 -> "Arial 36"
	| 4 -> "Arial 72"
	| _ -> "Arial 18"
in
  

(************************************
 *          radiobutton              *
 *************************************)
  
  
let tv2 = Textvariable.create () in
  
(* for the change of mode *)
let tv = Textvariable.create () 
in
  Textvariable.set tv "1";
  
  let radf = Frame.create frame 
  in
  let rads = List.map (fun (t,v) -> 
			 Radiobutton.create 
			 ~text:t 
			 ~value:v 
			 ~variable:tv 
			 ~command: (fun () ->
				      if ((int_of_string(Textvariable.get tv))=1) 
				      then Evts.change_mod_lin() 
				      else Evts.change_mod_arbre())
			   radf)
	       [("linear mode","1") ; ("tree mode  ","2")] 
  in
    
    (*for change of zoom*)
    
    Textvariable.set tv2 "3";
    
    let radf2 = Frame.create frame 
    in
    let rads2 = List.map (fun (t,v) -> 
			    Radiobutton.create 
			    ~text:t 
			    ~value:v 
			    ~variable:tv2 
			    ~command:
			      (fun _ -> 
				 if ((int_of_string (Textvariable.get tv2))=3)
				 then (Canvas.xview ~scroll: (`Moveto 0.) can; 
				       Canvas.yview ~scroll: (`Moveto 0.) can;
				       Evts.change_mod_zoom(fun t f -> send_order_box(Refresh(t,f))) true)
				 else  Evts.change_mod_zoom(fun t f -> send_order_box(Refresh(t,f))) false;
				 (* update_auto_zoom *)
				 if !autozoom 
				 then (Textvariable.set tv2 "3")
				 else (Textvariable.set tv2 "4")) radf2 )
		  [("autozoom   ","3");("zoom          ","4")] 
    in
      
      pack 
      ~side:`Right 
	[radf];
      pack 
      ~side:`Right 
	[radf2];
      
      pack  rads2;
      pack  rads;
      


(************************************
*          button +/-               *
*************************************)


      let fbutt = Frame.create  frame 
      in
      let plus_font = 
	Button.create 
	~width:2
	~text:" + "
	~command:(fun _ -> 
		    let ind_font = num_in_listf !i_font
		    in
		      if ind_font=4 
		      then ()
		      else 
			begin
			  Evts.change_font (fun t f -> send_order (Refresh(t,f))) (recupnieme (!list_f,(ind_font)));
			  Textvariable.set tv2 "4";
			  i_font := font_in_listf (ind_font+1);
			end)
	  fbutt
      in
	
      let moins_font = 
	Button.create
	~width:2
	~text:" - "
	~command:(fun _ ->
		    let ind_font = num_in_listf !i_font
		    in
		      if ind_font=1 
		      then ()
		      else 
	begin 
	  Evts.change_font (fun t f -> send_order (Refresh(t,f))) (recupnieme (!list_f, (ind_font-2)));
	  Textvariable.set tv2 "4";
	  i_font := font_in_listf (ind_font-1);
	end)
	  fbutt 
      in 
      let restart_but = 
	Button.create 
	~width:3
	~text:"Restart"
	~command:
	  (fun _ -> 
	     Canvas.xview ~scroll: (`Moveto 0.) can; 
	     Canvas.yview ~scroll: (`Moveto 0.) can;
	     Evts.restart(fun t f -> send_order_box(Refresh(t,f)));
	     (* update_auto_zoom *)
	     if !autozoom 
	     then (Textvariable.set tv2 "3")
	     else (Textvariable.set tv2 "4"))
	  fbutt
      in
      let merge_but = 
	Button.create 
	~width:3
	~text:"Merge"
	~command:
	  (fun _ -> 
	     if !first_merge_state="" or !second_merge_state=""
	     then message "Select two terms with CTRL + Right_Click before merging"
	     else 
	       begin
		 merge_list:= (!first_merge_state ^ " -> " ^ !second_merge_state)::(!merge_list);
		 remove_merge_sel ()
	       end)
	  fbutt
      in
      let apply_merge_but = 
	Button.create 
	~width:8
	~text:"Apply merge"
	~command:
	  (fun _ ->
	     confirmation ("Do you really want to quit Tabi and do merging?\n (for avoiding merging choose 'Exit' in the file menu)\nMerging rules:\n"^(List.fold_right (function s1 -> function s2 -> (s1^"\n"^s2)) !merge_list "."))
	       (fun () -> closeTk()) (fun () -> ()))
	  fbutt
      in
	
	pack ~side:`Left [plus_font;moins_font;restart_but;merge_but;apply_merge_but];
	pack ~side:`Right [fbutt] ;



let update_auto_zoom ((): unit): unit =
  begin
    if !autozoom 
    then (Textvariable.set tv2 "3")
    else (Textvariable.set tv2 "4");
    update()
  end 
in

(************************************
*   event / global bind             *
*************************************)

(*  binding for canvas resizing *)

  bind 
  ~events: [`Configure]
  ~fields: [`Width;`Height]
  ~action:
    (function x -> 
       width:= x.ev_Width;
       height:= x.ev_Height;
       if !autozoom 
       then
	 (Evts.change_mod_zoom(fun t f -> send_order_box(Refresh(t,f))) true;
	  update_auto_zoom())
       else ())
    can ;


(* Last bounding box highlighted *)



let (default_bb: zone)= (0,0,0,0) in
let last_box= ref default_bb in
  
  Canvas.bind 
  ~events:[`Motion]
  ~fields:[`MouseX;`MouseY]
  ~extend: true
  ~action: 
    (function x -> 
       let (fs,(x1,y1,x2,y2),te,fr) = 
	 Evts.get_fromstate 
	   (x.ev_MouseX-(!decalTextRecX)+(originx (Canvas.xview_get can))) 
	   (x.ev_MouseY-(!decalTextRecY)+(originy (Canvas.yview_get can))) 
       in
	 if (x1, y1, x2, y2)= !last_box then ()
	 else 
	   begin
	     last_box:= (x1, y1, x2, y2);
	     Canvas.delete can [(`Tag "highlight");(`Tag "from_s")]; 
	     let from_s = Canvas.create_text ~text:fs
			  ~x:(x2-15+(!decalTextRecX))
			  ~y:(y2-(y2-y1+10)+(!decalTextRecY))  
			  ~fill:`Red
			  ~font:"Arial 14"
			    can  
	     in 
	       Canvas.addtag can 
	       ~tag:"from_s" 
	       ~specs:[`Withtag from_s] ;
	       let highlight = 
		 Canvas.create_rectangle
		 ~x1:(x1+(!decalTextRecX))
		 ~y1:(y1+(!decalTextRecY))
		 ~x2:(x2+(!decalTextRecX))
		 ~y2:(y2+(!decalTextRecY))
		 ~fill:`Green
		 ~tags: ["box"]
		 ~outline:`Green
		   can
	       in 
		 Canvas.addtag can 
		 ~tag:"highlight" 
		 ~specs:[`Withtag highlight] ;
		 
		 Canvas.raise can (`Tag "merge_sel");
		 Canvas.raise can (`Tag "term") end)
    
    can
    (`Tag "box") ;

  
  Canvas.bind 
  ~events:[`Leave]
  ~fields:[`MouseX;`MouseY]
  ~extend: true
  ~action: 
    (function x -> 
       let (_,(x1,y1,x2,y2),_,_) = 
	 Evts.get_fromstate 
	   (x.ev_MouseX-(!decalTextRecX)+(originx (Canvas.xview_get can))) 
	   (x.ev_MouseY-(!decalTextRecY)+(originy (Canvas.yview_get can))) 
       in
	 if (x1, y1, x2, y2)= !last_box then ()
	 else 
	   begin
	     last_box := default_bb; 
	     Canvas.delete can [(`Tag "highlight");(`Tag "from_s")]
	   end)
    can
    (`Tag "box");


  Canvas.bind 
  ~events:[`ButtonPress]
  ~fields:[`MouseX;`MouseY]
  ~extend: true  
  ~action:(function x -> 
	     (remove_merge_sel();
	      (*	      let symb= Evts.get_symbol (x.ev_MouseX-(!decalTextRecX)+(originx (Canvas.xview_get can))) 
			      (x.ev_MouseY-(!decalTextRecY)+(originy (Canvas.yview_get can))) in
			      if symb = !Gest.start_symb (* The Start symbol has been clicked *)
			      then (* we need to choose between browsing final states or all states *)
			      browsing_style ()
			      else (); *)
	      
	      Evts.get_coord_unfold (fun t f -> send_order_box(Refresh(t,f)))
		(fun i tl x y -> send_order(
		   Choices(i,tl,(x-(originx (Canvas.xview_get can))),
			     (y-(originy (Canvas.yview_get can))))))
		(x.ev_MouseX-(!decalTextRecX)+(originx (Canvas.xview_get can))) 
		(x.ev_MouseY-(!decalTextRecY)+(originy (Canvas.yview_get can)))))
    can
    (`Tag "box");


(* Right click = fold *)

  Canvas.bind ~events:[`ButtonPressDetail 3]
  ~fields:[`MouseX;`MouseY]
  ~extend: true
  ~action:
    (function x -> 
       remove_merge_sel();
       if !presente=0 
       then
	 (Evts.get_coord_fold 
	    (fun t f -> send_order(Refresh(t,f))) 
	    (fun i tl x y -> send_order(Choices (i,tl,x,y)))
	    (x.ev_MouseX-(!decalTextRecX)+(originx (Canvas.xview_get can))) 
	    (x.ev_MouseY-(!decalTextRecY)+(originy (Canvas.yview_get can)))) 
       else () )
    can
    (`Tag "box");


(* Shift + Right click  => linear/tree mode on one level *)

  Canvas.bind ~events:[`Modified ([`Shift], `ButtonPressDetail 3)]
  ~fields:[`MouseX;`MouseY]
  ~extend: true
  ~action:(function x -> 
	     remove_merge_sel();
	     if !presente=0
	     then
	       (Evts.change_to_one_level 
		  (fun t f -> send_order(Refresh(t,f))) 
		  (x.ev_MouseX-(!decalTextRecX)+(originx (Canvas.xview_get can))) 
		  (x.ev_MouseY-(!decalTextRecY)+(originy (Canvas.yview_get can)))) 
	     else ();
	     update_auto_zoom())
    can
    (`Tag "box");
  
  
  
  (* CTRL + Right-click => Merge select *)
  
   Canvas.bind ~events: [`Modified ([`Control], `ButtonPressDetail 3)] (* [`Modified ([`Alt],`ButtonPress)] *)
  ~fields:[`MouseX;`MouseY]
  ~extend: true
  ~action:(function x -> 
	     let (fs,(x1,y1,x2,y2),te,fr) = 
	       Evts.get_fromstate 
		 (x.ev_MouseX-(!decalTextRecX)+(originx (Canvas.xview_get can))) 
		 (x.ev_MouseY-(!decalTextRecY)+(originy (Canvas.yview_get can))) in
	       if fs="" then ()
	       else 
		 begin
		   if !second_merge_state = "" then () else Canvas.delete can [(`Tag "merge_sel")];
		   if !first_merge_state = "" then first_merge_state:= fs
		   else 
		     if !second_merge_state = "" then second_merge_state := fs
		     else (second_merge_state:= ""; first_merge_state:= fs);
		   let from_s =
		     Canvas.create_text ~text:fs
		     ~x:(x1+(if !first_merge_state="" then 0 else 15)+(!decalTextRecX))
		     ~y:((y1-10)+(!decalTextRecY))
		     ~fill:`Blue
		     ~font:"Arial 14"
		       can  
		   in 
		     Canvas.addtag can 
		     ~tag:"merge_sel" 
		     ~specs:[`Withtag from_s] ;
		     let merge_sel =
		       Canvas.create_line
		       ~xys:[((x1+(!decalTextRecX)),(y1+(!decalTextRecY)));
			     ((x2+(!decalTextRecX)),(y1+(!decalTextRecY)));
			     ((x2+(!decalTextRecX)),(y2+(!decalTextRecY)));
			     ((x1+(!decalTextRecX)),(y2+(!decalTextRecY)));
			     ((x1+(!decalTextRecX)),(y1+(!decalTextRecY)))]
		       ~tags: ["merge_sel"]
		       ~fill:`Blue
			 can
		     in 
		       Canvas.addtag can 
		       ~tag:"merge_sel" 
		       ~specs:[`Withtag merge_sel] ;    
		       Canvas.raise can (`Tag "merge_sel");
		       Canvas.raise can (`Tag "term")
		 end)
    
    can
    (`Tag "box");


(* CTRL + Left-click  => tree mode for the whole subterm *)
  Canvas.bind ~events:[`Modified ([`Control],`ButtonPress)]
  ~fields:[`MouseX;`MouseY]
  ~extend: true
  ~action:(function x -> 
	     remove_merge_sel();
	     if !presente=0
	     then
	       (Evts.change_total_arborisation
		  (fun t f -> send_order(Refresh(t,f))) 
		  (x.ev_MouseX-(!decalTextRecX)+(originx (Canvas.xview_get can))) 
		  (x.ev_MouseY-(!decalTextRecY)+(originy (Canvas.yview_get can)))) 
	     else ();
	     update_auto_zoom())
    can
    (`Tag "box");


(* SHIFT + Left-click  => Linear mode for the whole sub-tree *)
  
  Canvas.bind ~events:[`Modified ([`Shift],`ButtonPress)]
  ~fields:[`MouseX;`MouseY]
  ~extend: true
  ~action:(function x -> 
	     remove_merge_sel();
	     if !presente=0
	     then
	       (Evts.change_total_linearisation
		  (fun t f -> send_order(Refresh(t,f))) 
		  (x.ev_MouseX-(!decalTextRecX)+(originx (Canvas.xview_get can))) 
		  (x.ev_MouseY-(!decalTextRecY)+(originy (Canvas.yview_get can)))) 
	     else ();
	     update_auto_zoom() )
    can
    (`Tag "box");

(******************
 *     frame       *
*******************)
  
  pack 
    [frame];
  pack 
  ~side:`Bottom 
  ~fill:`Both  
    [can];

(**********************************************
*  Initialisation of the font measures tables *
***********************************************)

  Cotes.table_init();
  if not (a.q=[]) then
    begin
      load_message ();
      Evts.automaton_open (fun t f -> send_order_box(Refresh(t,f)))  a;				 
      Canvas.delete can [(`Tag "load")]
    end;
  mainLoop();
  !merge_list
  
  
  (************************************
   *          mainloop                 *
   *************************************)
  
  
let main(): unit=
  let _ = launch({q=[];f=[];t=[]}) in ()


let tabi_call (a: automaton): string =
  let _= Evts.default_term:= init_term in 
  let merge_list= launch(a) in
    List.fold_right (function s1 -> function s2 -> (s1^"\n"^s2)) merge_list ".";;

