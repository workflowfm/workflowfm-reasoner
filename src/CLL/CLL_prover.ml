(* ========================================================================= *)
(* A natural deduction meta-logic framework framework for CLL proofs with    *)
(* process calculus construction.                                            *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2009-2019                                 *)
(* ========================================================================= *)

(* Dependencies *)

needs "IsabelleLight/make.ml";;
needs "tools/make.ml";;
needs "embed/sequent.ml";;
needs "tools/Library/lists.ml";;
needs "tools/Library/sets.ml";;
needs "tools/Library/multisets.ml";;
needs (!serv_dir ^ "support/support.ml");;
needs (!serv_dir ^ "CLL/CLL.ml");;
needs (!serv_dir ^ "processes/process_calculus.ml");;


(* Given a process calculus, we automatically define linear consequence. *)

(* ------------------------------------------------------------------------- *)
(* Linear consequence                                                        *)
(* ------------------------------------------------------------------------- *)
(* We use a one-sided sequent calculus, process calculus proof terms and     *)
(* include the process calculus translations for each rule.                  *)
(* Instead of having an Exchange rule, we use multisets. Our embedded prover *)
(* then does the matching automatically thus keeping our proofs nice and     *)
(* clean.                                                                    *)
(* ------------------------------------------------------------------------- *)
(* The MALL version of CLL is considered. The rules for the exponentials are *)
(* not included.                                                             *)
(* ------------------------------------------------------------------------- *)


module type Cllproc_type =
sig
  module Pcalc:Process_calculus

  val cll_to_proc : term -> term
  (* A converter from a CLL specification       *)
  (* (multiset of CLL terms) to a corresponding *)
  (* process calculus term.                     *)

  (* 
     val fake_subs : term -> term  (* A method to calculate substitutions in a  *)
     (* term efficiently using OCaml.             *)
     val    prove_subs : term list->term->thm (* A method to prove the correctness *)
   (* of the above calculation, given the defs  *)
    (* of any component agents.                  *)
   *)  

  val ID_PROC : thm
  val TIMES_PROC : thm
  val PAR_PROC : thm
  val WITH_PROC : thm
  val PLUSL_PROC : thm
  val PLUSR_PROC : thm
  val CUT_PROC : thm

  val CLL_PROCS : thm list

  val linear_RULES : thm
  val linear_INDUCT : thm
  val linear_CASES : thm 

  val ll_id : thm
  val ll_times : thm
  val ll_par : thm
  val ll_plus1 : thm 
  val ll_plus2 : thm
  val ll_with : thm
  val ll_cut : thm

  val hide_procs : unit -> unit
  val show_procs : unit -> unit

  val linprop_to_name : term -> string
  val linprop_to_chan : string -> string -> term -> term
  val linprops_to_chans : string -> term list -> term list
    
  val mk_cll: term -> term -> term
  val mk_cll_def_raw: string -> (term * term) list -> term * term -> term
  val mk_cll_def: string -> term list -> term -> term
   
  val process_of_term: term -> term
  val process_of_asm : string -> goalstack -> term

  val llcut_tac : (term * term) list -> thm -> seqtactic
  val llcut : thm -> seqtactic
  val llid : term -> seqtactic
end;;

module Cllproc (Proc : Process_calculus) : Cllproc_type =
struct
  module Pcalc = Proc
  let chan_type = Proc.chantp
  let proc_type = Proc.tp
  let cll_type = type_subst [(Proc.chantp,`:CHANTP`)] `:((CHANTP)LinTerm)multiset`
  let proc_fn = Proc.fn
  let proc_bn = Proc.bn
  let proc_names = Proc.names
  let proc_fn_conv = Proc.fn_conv
  let proc_bn_conv = Proc.bn_conv
  let proc_names_conv = Proc.names_conv
  let proc_sub_conv = Proc.sub_conv

 (* let fake_subs = Proc.fake_subs
  let prove_subs = Proc.prove_subs*)

  (* Convert a CLL term to a serialised name without spaces. *)
  (* Primarily used to build channel names. *)
  let rec linprop_to_name tm =
    try
      if (tm = `LinOne`) then "1"
      else if (tm = `LinZero`) then "0"
      else if (tm = `Top`) then "T"
      else if (tm = `Bottom`) then "_I_"
      else
	let comb,args = strip_comb tm in
	if (is_var comb) then 
	  string_of_term comb
	else if (comb = `NEG`) then
	  linprop_to_name (hd args)
	else if (comb = `LinTimes`) then
	  "lB_" ^ (linprop_to_name (hd args)) ^ "_x_" ^ (linprop_to_name ((hd o tl) args)) ^ "_rB"
	else if (comb = `LinPar`) then
	  "lB_" ^ (linprop_to_name (hd args)) ^ "_Par_" ^ (linprop_to_name ((hd o tl) args)) ^ "_rB"
	else if (comb = `LinPlus`) then
	  "lB_" ^ (linprop_to_name (hd args)) ^ "_Plus_" ^ (linprop_to_name ((hd o tl) args)) ^ "_rB"
	else if (comb = `LinWith`) then
	  "lB_" ^ (linprop_to_name (hd args)) ^ "_With_" ^ (linprop_to_name ((hd o tl) args)) ^ "_rB"
	else failwith ""
    with Failure s -> failwith ("linprop_to_name (" ^ string_of_term(tm) ^ ") :" ^ s)

  let cll_to_proc = Proc.cll_to_proc linprop_to_name
			       
  let linprop_to_chan prefix postfix tm =
    if (String.length prefix = 0)
    then mk_var ((linprop_to_name tm)^"_"^postfix,chan_type)
    else mk_var (prefix^"_"^(linprop_to_name tm)^"_"^postfix,chan_type)			       

  let linprops_to_chans prefix tms =
    let mk_chan (n,i) = linprop_to_chan prefix (string_of_int i) n in
    map mk_chan (zip tms (1--(length tms)))
 		
  let ID_PROC = new_definition (Cll_terms.mk_id_proc Proc.tp Proc.chantp Proc.llid)
  let TIMES_PROC = new_definition (Cll_terms.mk_times_proc Proc.tp Proc.chantp Proc.lltimes)
  let PAR_PROC = new_definition (Cll_terms.mk_par_proc Proc.tp Proc.chantp Proc.llpar)
  let WITH_PROC = new_definition (Cll_terms.mk_with_proc Proc.tp Proc.chantp Proc.llwith)   
  let PLUSL_PROC = new_definition (Cll_terms.mk_plusL_proc Proc.tp Proc.chantp Proc.llplusL)  
  let PLUSR_PROC = new_definition (Cll_terms.mk_plusR_proc Proc.tp Proc.chantp Proc.llplusR)  
  let CUT_PROC = new_definition (Cll_terms.mk_cut_proc Proc.tp Proc.chantp Proc.llcut)

  let CLL_PROCS = [ID_PROC;TIMES_PROC;PAR_PROC;WITH_PROC;PLUSL_PROC;PLUSR_PROC;CUT_PROC]

  let linear_RULES,linear_INDUCT,linear_CASES =
    new_inductive_definition (
    Cll_terms.mk_cll_rules Proc.consequence Proc.tp Proc.chantp
			   ID_PROC TIMES_PROC PAR_PROC WITH_PROC PLUSL_PROC PLUSR_PROC CUT_PROC)
  let [ll_id;
       ll_times;
       ll_par;
       ll_with;
       ll_plus1; ll_plus2;
       ll_cut ] = 
    map (MIMP_RULE o SPEC_ALL o REWRITE_RULE[IMP_CONJ]) 
      (CONJUNCTS linear_RULES)

  let oper = (fst o strip_comb o concl) ll_id

  
  (* ========================================================================= *)
      
  (* Pretty printing to hide process calculus term. *)

  let (string_of_cll:term -> string) =
    fun tm ->
      let c,args = strip_comb tm in
	try let _ = term_match [] oper c in 
	  (Proc.consequence ^ (string_of_term (hd args)) ^ " (...)")
	with Failure _ -> failwith "Not a CLL judgement."


  let print_cll fmt = pp_print_string fmt o string_of_cll

  let hide_procs,show_procs =
    (fun () -> install_user_printer ("print_cll",print_cll)),
    (fun () -> try delete_user_printer "print_cll"
     with Failure _ -> failwith ("show_procs: " ^
                                   "Process calculus is already being shown normally."))

(* ------------------------------------------------------------------------- *)
(* Creates the CLL |-- statement/speficiation of the given process.          *)
(* ------------------------------------------------------------------------- *)

  let mk_cll cll proc = list_mk_comb (oper,[try_type cll_type cll;try_type proc_type proc])

(* ------------------------------------------------------------------------- *)
(* Creates a multiset of CLL terms corresponding to a process with a list of *)
(* inputs ins and an output out, all of type LinProp.                        *)
(* ------------------------------------------------------------------------- *)
(* It automatically generates channel names using the name proc of the       *)
(* process and linprop_to_name.                                              *)
(* Channel names are also fresh with respect to the avoids list avoids.      *)
(* ------------------------------------------------------------------------- *)
					   
  let mk_cll_def_raw proc ins (out,outc) = 
    let ins,incs = unzip ins in

    (*  let cleanup s = (* String.trim *) s in (* TODO add more escaping etc here *)
      let ins = map cleanup ins
      and out = cleanup out in
      
      let mk_ll_ty n = mk_var (n,`:LinProp`) in
      let ins' = map mk_ll_ty ins
      and out' = mk_ll_ty out in
   *)
    
    (*
let mk_linprop tm = try_type `:LinProp` tm in
    let ins' = map mk_linprop ins
    and out' = mk_linprop out in
     *)
    
    let mk_inm (t,c) = mk_msing (list_mk_icomb "LL" [mk_llneg t;c])
    and mk_outm t c = mk_msing (list_mk_icomb "LL" [t;c]) in
    
    itlist (curry mk_munion) (map mk_inm (zip ins incs)) (mk_outm out outc)

  (* Assumes ins and out are of type :LinProp *)
  (* Process.create is used instead! *)
  let mk_cll_def proc ins out = 
    let incs = linprops_to_chans ("c"^proc) ins
    and outc = linprop_to_chan ("o"^proc) "" out in
    mk_cll_def_raw proc (zip ins incs) (out,outc)

					 
(* Simple term validation and retrieval of the process P from |-- (...) P.   *)

let (process_of_term:term -> term) =
  fun tm ->
    let c,args = strip_comb tm in
    try let _ = term_match [] oper c in (hd o tl) args
    with Failure _ -> failwith "Inappropriate term"


(* Retrieve process calculus term for a labelled assumption.  *)

let (process_of_asm:string -> goalstack -> term) =
  fun lbl -> process_of_term o concl o (assoc lbl) o top_asms


(* ------------------------------------------------------------------------- *)
(* Tactic to cut with an known CLL lemma.                                    *)
(* ------------------------------------------------------------------------- *)

let llcut_tac =
  fun setlist thm (i,metas) ->
    let thm = (UNDISCH_ALL o MIMP_TO_IMP_RULE o SPEC_ALL) thm in
    let primed_ll_cut = inst_meta_rule_vars [] (mk_meta_rule ll_cut) (thm_frees thm) in
    let cut_term = (hd o tl o hyp o thd3) primed_ll_cut in
    let cut_ins = seq_match (thm_frees thm) metas cut_term (concl thm) in
    let new_rule = inst_meta_rule (cut_ins) primed_ll_cut in
    apply_seqtac rulem_seqtac setlist new_rule (i,metas)


(*
let llcut_tac = 
  fun setlist thm ->
    let thm = (UNDISCH_ALL o MIMP_TO_IMP_RULE o SPEC_ALL) thm in
    let primed_ll_cut = thm_mk_primed_vars (thm_frees thm) ll_cut in
    let cut_term = (snd o dest_conj o fst o dest_mimp o concl) primed_ll_cut in
    let cut_ins = ll_rule_match (thm_frees thm) cut_term (concl thm) in
    let ll_cut_inst = INSTANTIATE cut_ins primed_ll_cut in
    let ADD_DISCH d t = DISCH d (ADD_HYP (ASSUME d) t) in
    let new_rule = MIMP_RULE (List.fold_right ADD_DISCH (fst (dest_thm thm)) ll_cut_inst) in
    llapply (llrulem_tac setlist (mk_meta_rule new_rule)) ;;
*)

let llcut = llcut_tac []

(* Added functionality to indirectly store buffer types. *)
(* This is useful for the pilib (typed) code generation. *)

let llid tm = 
  let name = ((String.uncapitalize o fst o dest_var) tm) ^ "_" in
  let new_var = mk_var (name,`:num`) in
  let ll_id' = INSTANTIATE (term_match [] `a:num` new_var) ll_id in
  rule_seqtac [`A:LinProp`,tm] ll_id'

end;;


(* ------------------------------------------------------------------------- *)
(* TODO: Can we factor these in the module? *)
(*
let split_cllprocseq tm =
  let comb,args = strip_comb tm in
  (fst o dest_const) comb,[hd args],[(hd o tl) args];;
  
add_split_seq_fun "|--" split_cllprocseq;;
*)


(* ========================================================================= *)

(* Getter functions for processes. *)
(* These need to be here because both module Proc and Clltactics need these! *)

(* props = propositions (types). *)

(* Get all types in a CLL process specification (|--). *)
let get_ll_props = 
 map (rand o rator o rand) o (filter is_msing) o flat_munion o rand o rator;;

(* Get all types that satisfy f. *)
let find_ll_props f = 
  (filter f) o get_ll_props;;

(* Get the first type that satisfies f. *)
let find_ll_prop f = 
  (find f) o get_ll_props;;

(* Find the output of a process.                                             *)
(* ------------------------------------------------------------------------- *)
(* We assume there is exactly one output in every process.                   *)
(* It would be interesting to consider processes with *no* outputs           *)
(* (terminators), but these cannot be joined by tensor with any other        *)
(* process or buffer!                                                        *)
(* Processes with two or more outputs cannot communicate all their outputs   *)
(* simultaneously through cut.                                               *)

let find_output =
  find_ll_prop 
    ( fun x -> try (let _ = find_term ((=) `(NEG)`) x in false ) with Failure _ -> true);;

(* Find a list of inputs. *)
let find_inputs =
  (map rand) o (find_ll_props is_llneg);;


(* Terms = types annotated with channels. *)

(* Get all terms in a CLL process specification (|--). *)
let get_ll_terms = 
 map (rand) o (filter is_msing) o flat_munion o rand o rator;;

(* Get all terms whose types satisfy f. *)
let find_ll_terms f = 
  (filter (f o rand o rator)) o get_ll_terms;;

(* Get the first term whose type satisfies f. *)
let find_ll_term f = 
  (find (f o rand o rator)) o get_ll_terms;;

(* Get the (single) output term. *)
let find_output_term =
  find_ll_term 
    ( fun x -> try (let _ = find_term ((=) `(NEG)`) x in false ) with Failure _ -> true);;

(* Get the list of input terms. *)
let find_input_terms =
  (find_ll_terms is_llneg);;

(* Get the list of free channels input terms. *)
let get_ll_channels = 
 map (rand o rand) o (filter is_msing) o flat_munion o rand o rator;;

let gen_ll_channels tm =
  list_mk_forall (get_ll_channels tm,tm);;







(* ------------------------------------------------------------------------- *)
(* Some printers for LaTeX.                                                  *)
(* ------------------------------------------------------------------------- *)
(* TODO : move to module ? *)

let rec linprop_to_latex tm =
  try 
    let comb,args = strip_comb tm in
    if (is_var comb) then 
      string_of_term comb
    else if (comb = `NEG`) then
      ((linprop_to_latex (hd args)) ^ "^\\bot")
    else if (comb = `LinTimes`) then
      "(" ^ ((linprop_to_latex (hd args)) ^ " \otimes " ^ (linprop_to_latex ((hd o tl) args))) ^ ")"
    else if (comb = `LinPar`) then
      "(" ^ ((linprop_to_latex (hd args)) ^ " \parr " ^ (linprop_to_latex ((hd o tl) args))) ^ ")"
    else if (comb = `LinPlus`) then
      "(" ^ ((linprop_to_latex (hd args)) ^ " \oplus " ^ (linprop_to_latex ((hd o tl) args))) ^ ")"
    else if (comb = `LinWith`) then
      "(" ^ ((linprop_to_latex (hd args)) ^ " \with " ^ (linprop_to_latex ((hd o tl) args))) ^ ")"
    else failwith ""
  with Failure s -> failwith ("linprop_to_latex (" ^ string_of_term(tm) ^ ") :" ^ s);;

let string_of_seq_latex x =
  let _,args = strip_comb x in
  let cll,chan = hd args,(hd o tl) args in
    "\seq{" ^ (string_of_term chan) ^ "}{" ^ linprop_to_latex cll ^ ")" ;;
  
let string_of_cll_latex x =
  let proc = rand x 
  and cll = (strip_munion o rand o rator) x in
  let sequents = map (string_of_seq_latex o rand) cll in
  let seql l =
    let mk_seq x y = x ^ " \sep " ^ y in
      match l with 
          [] -> ""
	| [h] -> h
	| _ -> itlist mk_seq (butlast l) (last l) in
    "\\tstile \cllproc{" ^ string_of_term proc ^ "} " ^ (seql sequents);;

let string_of_cll_logic_latex x =
  let cll = (List.rev o strip_munion o rand o rator) x in
  let sequents = map (linprop_to_latex o rand o rator o rand) cll in
  let seql l =
    let mk_seq x y = x ^ " \sep " ^ y in
      match l with 
          [] -> ""
	| [h] -> h
	| _ -> itlist mk_seq (butlast l) (last l) in
    "\\tstile " ^ (seql sequents);;


(* map (print_newline o print_string o string_of_cll_logic_latex o Service.get_cll o Service.get) (Service.get_all());; *)
