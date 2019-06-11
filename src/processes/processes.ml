(* ========================================================================= *)
(* Defined/stored processes management.                                      *) 
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2011 - 2019                               *)
(* ========================================================================= *)

(* Dependencies *)

needs ("tools/lib.ml");;
needs (!serv_dir ^ "support/support.ml");;
needs (!serv_dir ^ "processes/process_calculus.ml");;
needs (!serv_dir ^ "CLL/CLL_prover.ml");;
needs (!serv_dir ^ "processes/actions.ml");; 

module type Process_type =
sig
  type t = {
    name : string;
    inputs : (term * term) list;
    output : term * term;
    prov : provtree;
    proc : term; (* TODO: remove this - keep only frees? *)
    actions : Action.t list;
    copier : bool;
    intermediate : bool;
  }
  val proctp : hol_type
  val chantp : hol_type 
  val try_proc_type : term -> term
  val mk_chan : string -> term
  val mk_call : string -> term list -> term
  val mk_proc_def : string -> term list -> term -> term
  val gen_proc : term -> term
  val get_proc_raw : t -> term
  val get_prov : t -> (string * provtree)
  val prove_subs : term list -> t -> thm
  val get_cll_def : t -> term
  val get_cll : t -> term
  val get_cll_raw : t -> term
  val get_dep_strings : t -> string list
  val get_deps : (string * t) list -> t -> t list
  val check_copier : term list -> term -> bool
  val define :
    string ->
    bool -> 
    (term * term) list -> 
    term * term -> 
    provtree ->
    term -> 
    Action.t list -> t
  val create : string -> term list -> term -> t
  val from_cll : string -> bool -> Action.t list -> provtree option -> term -> t
  val compose1 : Action.t -> t -> t -> t * Actionstate.t
  val prove :
    string ->
    t list ->
    Action.t list ->
    string ->
    instantiation * thm * (Actionstate.t * t) list * Actionstate.t
  val compose :
    string ->
    t list ->
    Action.t list ->
    t * (Actionstate.t * t) list * Actionstate.t
end;;

module Process (Cll : Cllproc_type) : Process_type =
  struct
  type t = {
    name : string;
    inputs : (term * term) list;
    output : term * term;
    prov : provtree;
    proc : term;
    actions : Action.t list;
    copier : bool;
    intermediate : bool;
  }

  let proctp = Cll.Pcalc.tp
  let chantp = Cll.Pcalc.chantp

  let try_proc_type tm = try_type Cll.Pcalc.tp tm
(* TODO improve - enforce (used at json/composer.ml to_agent *)

  let mk_chan s = mk_var (s,Cll.Pcalc.chantp)

  let mk_call name args = 
    if (args = []) then mk_var(name,Cll.Pcalc.tp) else
      let procname = mk_var (name,mk_type ("fun",[`:A`;Cll.Pcalc.tp])) in
      let argtuple = itlist (fun x y -> mk_pair (x,y)) (butlast args) (last args) in
      mk_icomb (procname,argtuple)

  let mk_proc_def name args proc =
    mk_eq (mk_call name args,proc)
	  
  let gen_proc proc =
    let chans = (dest_tuple o rand o lhs) proc in
    list_mk_forall (chans,proc)

		   
  let get_proc_raw (x:t) =
    let lh = (fst o dest_comb) x.proc in
    let proc' = (Cll.Pcalc.sub_reduce o rhs o concl o REWRITE_CONV Cll.CLL_PROCS o rhs) x.proc in
    mk_comb (lh,proc')
								      
  let prove_subs deps (x:t) =
    let deps = map gen_proc deps in
    RAND_CONV (REWRITE_CONV Cll.CLL_PROCS THENC Cll.Pcalc.sub_conv deps) x.proc

	      
  let get_cll_def (x:t) =
    Cll.mk_cll_def_raw x.name x.inputs x.output

  let get_cll (x:t) =
    let proc = if (x.intermediate)
	       then rhs x.proc
	       else lhs x.proc in
    Cll.mk_cll (get_cll_def x) proc

  let get_cll_raw (x:t) =
    Cll.mk_cll (get_cll_def x) (rhs x.proc)


  let get_dep_strings (x:t) =
    let fold_act (a:Action.t) (l,d) = ([a.Action.larg;a.Action.rarg] @ l,a.Action.res :: d) in
    let l,d = itlist fold_act x.actions ([],[]) in
    filter (fun x -> not (mem x d)) (setify l)

  let get_deps (l:(string * t) list) (x:t) =
    map (C assoc l) (get_dep_strings x)
	   
  let check_copier inprops outprop =
    try (
    let outprops = (setify o flat_tensor) outprop in
    (length inprops = 1 && inprops = outprops)
    ) with Failure _ -> false

  let define name intermediate inputs output prov proc actions =
    ({name = name; 
      inputs = inputs ;
      output = output ;
      prov = prov ;
      proc = mk_proc_def name ((map snd inputs) @ [snd output]) proc ;
      actions = actions ;
      copier = check_copier (map fst inputs) (fst output) ;
      intermediate = intermediate ;
     }:t)
			
  let create name ins out =
    let ins = map (try_type `:LinProp`) ins
    and out = try_type `:LinProp` out in
    let incs = Cll.linprops_to_chans ("c"^name) ins
    and outc = Cll.linprop_to_chan ("o"^name) "" out 
    and prov = prov_of_tm name out in
    let inpairs = zip ins incs in
    let proc = Cll.cll_to_proc (Cll.mk_cll_def_raw name inpairs (out,outc)) in
    define name false inpairs (out,outc) prov proc []


  let get_proc_deps proc =
    (* WARNING: This assumes at least 2 channel arguments! Maybe we should relax this? *)
    let procty = mk_type ("fun",[mk_type ("prod",[Cll.Pcalc.chantp;`:A`]);Cll.Pcalc.tp]) in
    let fast_type_test tm = try (
			    let _ = (hd o tl o snd o dest_type o type_of) tm = Cll.Pcalc.tp in
			    true ) with Failure _ -> false in
    let type_test tm = try (let _ = type_match procty (type_of tm) [] in true) with Failure _ -> false in
    let myfind tm = is_var tm && fast_type_test tm && type_test tm in
    find_terms myfind proc

  let get_prov proc = (proc.name,proc.prov)
  
  let get_prov_from_state name state = 
    try ( Some(assoc name state.Actionstate.prov) )
    with Failure _ -> (
      warn true ("State contains no output provenance for: " ^ name) ;
      None
    )
 
  let from_cll name intermediate actions provenance cll =
    let proc = Cll.process_of_term cll in (* also does a sanity check *)
    (* let deps = map (fst o dest_var) (get_proc_deps proc) in *)
    let intms = find_input_terms cll
    and outtm = find_output_term cll in
    let desttm input tm =
      let lh,rh = dest_comb tm in
      if (input)
      then (rand o rand) lh,rh
      else rand lh,rh in
    let ins = map (desttm true) intms
    and out = desttm false outtm in
    let prov = match provenance with
      | Some (p) -> p
      | None -> prov_of_tm name (fst out) in
    define name intermediate ins out prov proc actions

 
  let (compose1 : Action.t -> t -> t -> t * Actionstate.t) =
    fun comp lp rp ->
    let state = Actionstate.set_prov [get_prov lp; get_prov rp] (Actionstate.create comp.Action.res)
    and tml = (gen_ll_channels o get_cll) lp
    and tmr = (gen_ll_channels o get_cll) rp in
    
    let (gl:goal) = [],itlist (curry mk_imp) [tml;tmr] (genvar `:bool`) in
    (* [(larg,ASSUME tml);(rarg,ASSUME tmr)],genvar `:bool`) in *)
    ( print_goal gl ;
      (* Ignoring metas (TODO: for now?) *)
      let (_,(asl,_)::_,_),s' =
	EEVERY [
  	    Actionstate.ASTAC (DISCH_THEN (META_SPEC_ALL_LABEL_TAC lp.name));
	    Actionstate.ASTAC (DISCH_THEN (META_SPEC_ALL_LABEL_TAC rp.name));
	    Action.apply comp] state gl in    
      let prov = get_prov_from_state comp.Action.res s' in
      (from_cll comp.Action.res true [comp] prov o concl) (assoc comp.Action.res asl),s')

    
  let prove label deps acts res =
    print_string ("*** Composing: " ^ res) ; print_newline () ; reset_time() ;
    let state = Actionstate.set_prov (map get_prov deps) (Actionstate.create label)
    and asms = map (gen_ll_channels o get_cll) deps
    and labels = map (fun x -> x.name) deps in
    let newvar = genvar `:bool` in
    let glvar = mk_undered_var [newvar] newvar in
    let gltm = mk_exists (glvar,glvar) in
    let gl = itlist (fun x y -> mk_imp (x,y)) asms gltm in
    let gs = [mk_goalstate([],gl),state] in

    let inittac = Actionstate.ASTAC (MAP_EVERY (fun s -> (DISCH_THEN (META_SPEC_ALL_LABEL_TAC s))) labels THEN
				  REPEAT META_EXISTS_TAC) in
    let gs' = apply_etac inittac gs in
    print_string ("*** Goal setup complete." ^ " (" ^ (string_of_float (rget_time())) ^ ")") ; print_newline ();

    let rec apply_acts gstack procs acts =
      match acts with
	  [] -> gstack,procs
	| h::t ->
	  let gst,st = hd gstack in
	  let gst' = gst,Actionstate.reset st in
	  let (newgst,newst) as res = eby (EVALID (Action.apply h)) gst' in
      let newprov = get_prov_from_state h.Action.res newst in
	  let newproc = (from_cll h.Action.res true [h] newprov o concl o
			     assoc h.Action.res o
			     fst o hd o snd3) newgst in
	  print_string ("*** Action complete: " ^ (Action.string_of_act h) ^ " (" ^ (string_of_float (rget_time())) ^ ")")  ; print_newline ();
	  apply_acts (res::gstack) (newproc::procs) t in

    let gs'',procs = apply_acts gs' [] acts in

    let states = (map snd o butlast o butlast) gs'' in
    (* and metas =  (fst o fst3 o fst o hd) gs'' in *)

    (*  let resgs = apply_etac (ETAC (Cll.ll_meta_lbl_asm res metas)) gs''  in*)
    let tac =  ETAC (USE_THEN res (UNIFY_ACCEPT_TAC [glvar] o NORMALIZE_MULTISET))in
    let resgs = apply_etac tac gs'' in
    print_string ("*** Unification complete." ^ " (" ^ (string_of_float (rget_time())) ^ ")")  ; print_newline ();

    let thm,state' = get_ethm resgs 
    and inst = (snd o fst3 o fst o hd) resgs in
    print_string ("*** Theorem reconstruction complete." ^ " (" ^ (string_of_float (rget_time())) ^ ")")  ; print_newline ();
    inst,thm,zip states procs,state'

  let compose name deps acts =
    let inst,thm,inter,state' = prove name deps acts name in
    let rescll = ((instantiate inst) o snd o strip_exists o concl o UNDISCH_ALL) thm in
    let prov = get_prov_from_state name state' in
    from_cll name false acts prov rescll,rev inter,state'

(* TODO: Do a sanity check by matching dependencies from get_proc_deps with those inferred from the actions. *)
				     
end;;
