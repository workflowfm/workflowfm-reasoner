(* ========================================================================= *)
(* Composition actions.                                                      *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2011 - 2019                               *)
(* ========================================================================= *)

(* Dependencies *)

needs ("embed/sequent.ml");;
needs (!serv_dir ^ "support/support.ml");;
needs (!serv_dir ^ "processes/provenance.ml");;


(* ========================================================================= *)
(* Composition actions.                                                      *)
(* ------------------------------------------------------------------------- *)
(* These are standardized as named actions that correspond to a HOL Light    *)
(* tactic.                                                                   *)
(* Composition actions are binary. They involve two named components which   *)
(* can be either existing atomic or composite processes or intermediate      *)
(* compositions (see below).                                                 *)
(* The component names are given as arguments larg (left argument) and rarg  *)
(* (right argument). Two selector strings lsel and rsel are also given.      *)
(* These define a selection for a part of the corresponding component.       *)
(* e.g. if the user selected a particular input or output that the           *)
(* composition action must be applied on.                                    *)
(* The res argument corresponds to the name of the resulting intermediate    *)
(* composition.                                                              *)
(* ------------------------------------------------------------------------- *)
(* Note that not all current composition tactics make use of the selector    *)
(* arguments.                                                                *)
(* TENSOR does not need to.                                                  *)
(* WITH needs the selection of the particular input types that will be       *)
(* involved in the conditional.                                              *)
(* JOIN does not use selectors but will be updated to do so.                 *)
(* ========================================================================= *)

module Actionmap = Map.Make(String);;

module Actionstate = struct
  type t = {
      label : string;
      ctr : int;
      metas : term list;
      merged : (term * string * string) list;
      iprov : (term * provtree) list;
      prov : (string * provtree) list;
    }
	   
  let create lbl = ({ label = lbl ; ctr = 0 ; metas = [] ; merged = [] ; iprov = [] ; prov = [] }:t)

  let reset s = ({ s with merged = [] }:t)

  let label s = s.label
		   
  let set_label l s =
    ({ s with label = l }:t)   
   
  let ctr s = s.ctr
		   
  let set_ctr c s =
    ({ s with ctr = c }:t)
    
  let inc i s = set_ctr (s.ctr + i) s

  let set_metas l s =
    ({ s with metas = l }:t)

  let add_merged tm (cl,cr) s =
    ({ s with merged = (tm,string_of_term cl,string_of_term cr) :: s.merged }:t)

  let get_merge chan s = 
    let str = string_of_term chan in
    let search (tm,l,r) = l = str || r = str in
    find search s.merged
 	      
  let add_prov n p s =
    ({ s with prov = assoc_add n p s.prov }:t)

  let set_prov pm s =
    ({ s with prov = pm }:t)

  let add_iprov n p s =
    ({ s with iprov = (n,p) :: s.iprov }:t)
    
  let set_iprov pm s =
    ({ s with iprov = pm }:t)


  let from_seqstate (l,i,m) s = 
    ({ s with label = l ; ctr = i ; metas = m }:t)

  let to_seqstate s = (s.label,s.ctr,s.metas)
      
  let (print:t -> unit) =
    fun st -> 
      let stml tml = String.concat ", " (map string_of_term tml)
        and prmerged (tm,l,r) = ( print_string (" " ^ l ^ " = "^ r ^ " (" ^ (string_of_term tm) ^ ")") ; print_newline() )
      and prprov (n,p) = ( print_string (" " ^ n ^ " -> " ^ (string_of_prov p)) ; print_newline() ) 
      and priprov (n,p) = ( print_string (" " ^ (string_of_term n) ^ " -> " ^ (string_of_prov p)) ; print_newline() )
 in
    print_string "-----";
    print_newline ();
    print_string ("Label = " ^ st.label);
    print_newline ();
    print_string ("Ctr = " ^ (string_of_int st.ctr));
    print_newline ();
    print_string ("Metas = " ^ (stml st.metas));
    print_newline ();
    print_string ("Merged = ");
    ignore(map prmerged st.merged);
    print_newline ();
    print_string ("IProv = ") ;
    ignore(map priprov st.iprov) ;
    print_newline ();
    print_string ("Prov = ") ;
    ignore(map prprov st.prov) ;
    print_newline ();
    print_newline ();
    print_string "-----";
    print_newline()
	
  let (TAC:t etactic -> tactic) =
    fun atac -> ETAC_TAC' print (create "") atac

  let (CLL_TAC:seqtactic -> t etactic) =
    fun tac -> LIFT_ETAC to_seqstate from_seqstate tac

  let (ASTAC:tactic -> t etactic) = CLL_TAC o SEQTAC

  let (ADD_PROV_TAC:string -> provtree -> t etactic) =
    fun n p -> ALL_ETAC' (fun s -> add_prov n p s)
			 
  let (UPDATE_PROV_TAC:((string * provtree) list -> (string * provtree) list) -> t etactic) =
    fun f -> ALL_ETAC' (fun s -> set_prov (f s.prov) s)
			 
  let (ADD_IPROV_TAC:term -> provtree -> t etactic) =
    fun n p -> ALL_ETAC' (fun s -> add_iprov n p s)
			 
  let (TIMES_IPROV_TAC:term -> term -> t etactic) =
    fun l r ->
      let update s = try (
        let (_,lp),rest = remove (fun (i,p) -> i = l) s.iprov in
	let (_,rp),rest = remove (fun (i,p) -> i = r) rest in
	set_iprov ((list_mk_comb(`LinTimes`,[l;r]),provtimes lp rp) :: rest) s
		     ) with Failure _ -> (
		       warn true ("Failed to tensor iprov: " ^ (string_of_term l) ^ " - " ^ (string_of_term r)) ;
		       s) in
      ALL_ETAC' update

  let (PLUS_IPROV_TAC:term -> term -> t etactic) =
    fun l r ->
    let update s = try (
	let (_,lp),rest = remove (fun (i,p) -> i = l) s.iprov in
	let (_,rp),rest = remove (fun (i,p) -> i = r) rest in
	set_iprov ((list_mk_comb(`LinPlus`,[l;r]),provplus lp rp) :: rest) s
		     ) with Failure _ -> (
		       warn true ("Failed to add iprov: " ^ (string_of_term l) ^ " - " ^ (string_of_term r)) ;
		       s) in
      ALL_ETAC' update

  let (SET_CTR_TAC: int -> t etactic) =
    fun c -> ALL_ETAC' (fun s -> set_ctr c s)

  let (SET_LABEL_TAC: string -> t etactic) =
    fun l -> ALL_ETAC' (fun s -> set_label l s)

  let (UPDATE_LABEL_TAC: (string -> string) -> t etactic) =
    fun f s ->  SET_LABEL_TAC (f s.label) s

  let (TEMP_LABEL_THEN: (string -> string) -> t etactic -> t etactic) =
    fun f tac s -> EEVERY [
                       SET_CTR_TAC 0 ;
                       UPDATE_LABEL_TAC f ;
                       tac ;
                       SET_LABEL_TAC s.label ; 
                       SET_CTR_TAC s.ctr
                     ] s
			     
end;;		   

type astactic = Actionstate.t etactic;;


(* ------------------------------------------------------------------------- *)
(* REFRESH_CHANS_TAC renames all the channels in a process to keep them fresh*)
(* ------------------------------------------------------------------------- *)
(* The use of INSTANTIATE below will fail for composite processes as their   *)
(* channels are not universally quantified. REFRESH_CHANS_TAC will only      *)
(* succeed for atomic processes.                                             *)
(* ------------------------------------------------------------------------- *)
(*
let REFRESH_CHANS_TAC:string -> astactic =
  fun lbl st (asl,_ as gl) ->
    let thm = try ( assoc lbl asl ) with Failure _ -> failwith ("REFRESH_CHANS_TAC") in 
    let chans = get_ll_channels (concl thm) in
    let new_chan c = number_var st.Actionstate.ctr (mk_undered_var [c] c) in
    let nchans = map new_chan chans in
    let pairs = List.combine chans nchans in
    let mk_inst = fun t1,t2 -> term_match [] t1 t2 in
    let inst = itlist compose_insts (map mk_inst pairs) null_inst in
    let tac = REMOVE_THEN lbl (fun x -> LABEL_TAC lbl (INSTANTIATE inst x)) in
    let ((metas,insts),goals,just),st' = ETAC tac (Actionstate.inc 1 st) gl in
    ((nchans @ metas,insts),goals,just),Actionstate.add_chanmap pairs st';;
 *)    
  
module Action = struct

  type t = {
    act : string;
    larg : string;
    lsel : string;
    rarg : string;
    rsel : string;
    res : string ;
  }

  type tac = t -> thm -> thm -> astactic
						      

  let actions = ref Actionmap.empty;;
				  
  let get_all () = Actionmap.fold (fun k v l -> (v::l)) (!actions) []
  
  let names () = Actionmap.fold (fun k v l -> (k::l)) (!actions) []
  
  let get name = try ( Actionmap.find name (!actions) )
		 with Not_found -> failwith ("No such action '" ^ name ^ "'")

  let delete name = actions := Actionmap.remove name (!actions)

  let string_of_act (a:t) =
    a.act ^ ": " ^
    a.larg ^ " (" ^ a.lsel ^ ") " ^
    a.rarg ^ " (" ^ a.rsel ^ ") -> " ^ a.res 
    
  let (add:Actionmap.key->tac->unit) =
    fun name act ->
    warn (try (let _ = get name in true) with Failure _ -> false)
	 ("add_action: Overwriting action '" ^ name ^ "'.") ;
    actions := Actionmap.add name act (!actions)

  let (create:string -> string -> string -> string -> string -> string -> t) =
    fun act larg lsel rarg rsel res ->
    ({ act = act; larg = larg; lsel = lsel; rarg = rarg; rsel = rsel; res = res }:t)

  let apply: t -> astactic =
    fun act s gl ->
    let tac s (asl,w as gl) =
	  let name = String.uppercase act.act in
	  let atac = get name
	  and thml = try ( assoc act.larg asl )
	             with Failure _ -> failwith ("APPLY ACTION '"^name^"': No such process '"^act.larg^"'")
	  and thmr = try ( assoc act.rarg asl )
	             with Failure _ -> failwith ("APPLY ACTION '"^name^"': No such process '"^act.rarg^"'") in
	  atac act thml thmr s gl in
    
    let temp_label l = 
      if (l = "") then ("c"^act.res) else String.concat "__" ["c"^l;act.res;""] in

    EEVERY [
        (*	ETRY (REFRESH_CHANS_TAC act.rarg);
	        ETRY (REFRESH_CHANS_TAC act.larg); *)	
	    Actionstate.TEMP_LABEL_THEN temp_label tac
      ] s gl
    
 
(*  let (TAC:t -> tactic) =
    fun act -> Actionstate.TAC (apply act)
*)
    
  let root_deps (l:t list) =
    let split_act a = [a.larg; a.rarg], a.res in
    let splits = map split_act l in
    let deps,results = unzip splits in
    subtract (setify (flat deps)) results

end;;

type actiontactic = Action.tac;;

