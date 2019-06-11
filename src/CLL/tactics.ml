(* ========================================================================= *)
(* Advanced tactics for CLL                                                  *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                  2011-2019                                *)
(* ========================================================================= *)

(* Dependencies *)

needs ("tools/lib.ml");;
needs (!serv_dir ^ "CLL/CLL.ml");;
needs (!serv_dir ^ "CLL/CLL_prover.ml");;
needs (!serv_dir ^ "CLL/rules.ml");;
needs (!serv_dir ^ "processes/actions.ml");;


(* ========================================================================= *)
(* TODO: Consider merging this with the Action module. *)

module Clltactics =
  functor (Cll : Cllproc_type) ->
  struct
    
    module Rules = Cllrules(Cll)

    (* ------------------------------------------------------------------------- *)
    (* REFRESH_CHANS_TAC renames all the channels in a process to keep them fresh*)
    (* ------------------------------------------------------------------------- *)

    (*    let REFRESH_CHANS_TAC:string -> astactic =
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
	((nchans @ metas,compose_insts inst insts),goals,just),Actionstate.add_chanmap pairs st'*)
                 
    (* ------------------------------------------------------------------------- *)
    (* BUFFER_TAC tries to automatically prove any arbitrarily complex buffer.   *)
    (* ie. it proves `|-- (' (NEG A <> _) ^ ' (A <> _)) _` where `A` is an       *)
    (* arbitrarily complex output term (ie. only contains positive literals,     *)
    (* times ( ** ) and plus ( ++ )).                                            *)
    (* ------------------------------------------------------------------------- *)
    (* Note that the times case is treated with a special tactic because of      *)
    (* context splitting.                                                        *)
    (* ------------------------------------------------------------------------- *)

    let rec (BUFFER_ETAC:seqtactic) =
      let timestac lh rh s ((_,tm) as gl) =
	    let nlh,nrh = hashf mk_llneg (lh,rh) in
	    let nltm = mk_msing ( find_ll_term ((=) nlh) tm )
	    and nrtm = mk_msing ( find_ll_term ((=) nrh) tm ) in
	    rule_seqtac [(`A:LinProp`,lh);
			         (`B:LinProp`,rh);
			         (`G:(LinTerm)multiset`,nltm);
			         (`D:(LinTerm)multiset`,nrtm)] Cll.ll_times s gl
      in
      fun s ((_,tm) as gl) ->
	  print_string ("BUFFER_TAC: " ^ (string_of_term tm));
	  print_newline();
	  try (
	    let out = find_output tm in
	    if (is_var out) then (
	      Cll.llid out s gl
	    )
	    else
	      let comb,args = strip_comb out in
	      if (comb = `LinTimes`) then
	        let lh,rh = hd args,(hd o tl) args in
	        let tac = EEVERY
		                [ETAC (ONCE_REWRITE_TAC[NEG_CLAUSES]);
		                 ruleseq Cll.ll_par;
		                 timestac lh rh;
		                 BUFFER_ETAC ] in
	        tac s gl
	      else if (comb = `LinPlus`) then
	        let tac =
		      ETHEN (
	              ETHENL (
	                  EEVERY [ETAC (ONCE_REWRITE_TAC[NEG_CLAUSES]);
			                  ruleseq Cll.ll_with])
		            [ ruleseq Cll.ll_plus1 ;
		              ruleseq Cll.ll_plus2 ])
		        BUFFER_ETAC in
	        tac s gl
	      else
	        failwith "BUFFER_TAC"
		  
	  ) with Failure _ -> failwith "BUFFER_TAC"

                        
    let (BUFFER_TAC:astactic) =
      fun s ((_,tm) as gl) ->
	  (* let out = find_output tm in *)
	  Actionstate.CLL_TAC BUFFER_ETAC s gl
	  
	  
    (* ------------------------------------------------------------------------- *)
    (* PARBUF_TAC tries to automatically prove a buffer with                     *)
    (* composite ( ** ) output and atomic inputs.                                *)
    (* Tries to use BUFFER_TAC upon failure, so in fact the last component of    *)
    (* the output (and its corresponding input) can be complex.                  *)
    (* Simply put, this tactic can prove any composition of a complex buffer     *)
    (* (provable by BUFFER_TAC) with atomic buffers using the times rule.        *)
    (* ------------------------------------------------------------------------- *)
    (* This tactic is particularly useful for the construction (proof) of the    *)
    (* appropriate buffer to handle optional inputs in OPT_INPUT_TAC.            *)
    (* ------------------------------------------------------------------------- *)

    let rec (PARBUF_ETAC:seqtactic) =
      let timestac lh s ((_,tm) as gl) =
	    let nlh = mk_llneg lh in
	    let nltm = mk_msing ( find_ll_term ((=) nlh) tm ) in
	    rule_seqtac [(`A:LinProp`,lh);(`G:(LinTerm)multiset`,nltm)] Cll.ll_times s gl
      in
      fun s ((_,tm) as gl) ->
	  print_string ("PARBUF_TAC: " ^ (string_of_term tm));
	  print_newline();
	  try (
	    let out = find_output tm in
	    if (is_var out) then (
	      Cll.llid out s gl
	    )
	    else
	      let comb,args = strip_comb out in
	      if (comb = `LinTimes`) then
	        let lh = hd args in
	        let tac = EORELSE (ETHEN (timestac lh) PARBUF_ETAC) BUFFER_ETAC in
	        tac s gl
	      else
	        BUFFER_ETAC s gl
	  ) with Failure _ -> failwith "PARBUF_TAC"
	                    
    let (PARBUF_TAC:astactic) =
      fun s ((_,tm) as gl) ->
	  (* let out = find_output tm in *)
	  Actionstate.CLL_TAC PARBUF_ETAC s gl
	  

    (* ------------------------------------------------------------------------- *)
    (* CLL_PROVE_TAC is an automated CLL prover for sequents of the form:        *)
    (* |-- (NEG A), B                                                            *)
    (* where A and B only contain positive literals, plus, and times.            *)
    (* We call such lemmas "filters" and they correspond to properties of CLL.   *)
    (* Filters are useful to allow matching of inputs/outputs beyond simple      *)
    (* equality. e.g. an output A ** B can be matched to an input B ** A.        *)
    (* ------------------------------------------------------------------------- *)


    (* ------------------------------------------------------------------------- *)
    (* cllCombSelect prioritizes CLL term by size. We prefer trying to prove     *)
    (* shorter terms first as they may fail faster.                              *)
    (* ------------------------------------------------------------------------- *)

    let cllCombSelect tm =
      if (not (is_comb tm))
      then 0
      else let comb,args = strip_comb tm in
	       let l,r = hd args,(hd o tl) args in
	       if (Pervasives.(||) (is_var l) (is_const l)) then -1
	       else if (Pervasives.(||) (is_var r) (is_const r)) then 1 
	       else (term_size l) - (term_size r)

    (* ------------------------------------------------------------------------- *)
    (* CLL_PROVE_INPUT_ETAC breaks down the input term NEG A using the par and   *)
    (* with rules. There is no branching in this process so we just run          *)
    (* it until NEG A has been broken down to atomic (negative) literals.        *)
    (* ------------------------------------------------------------------------- *)
    (* TODO: The cllCombSelect selection here doesn't make sense as we run the   *)
    (* tactic exchaustively anyway. What would make sense is to reorder the      *)
    (* subgoals so that the smaller subgoal is tested first at the next stage.   *)
    (* ------------------------------------------------------------------------- *)

    let rec (CLL_PROVE_INPUT_ETAC:seqtactic) =
      fun s gl ->
      let rec withProof s ((_,tm) as gl) =
	    let wtm = find_ll_prop (is_binary "LinWith") tm in
	    let comb,args = strip_comb wtm in
	    let lh,rh = hd args,(hd o tl) args in
	    let select = cllCombSelect wtm in
	    if (select <= 0)
	    then (ETHEN
	            (rule_seqtac [(`A:LinProp`,lh);
			                  (`B:LinProp`,rh)] Cll.ll_with)
	            CLL_PROVE_INPUT_ETAC) s gl
	    else (ETHEN
	            (ETHENL
	               (rule_seqtac [(`A:LinProp`,lh);
			                     (`B:LinProp`,rh)] Cll.ll_with)
	               [ALL_ETAC;CLL_PROVE_INPUT_ETAC])
	            CLL_PROVE_INPUT_ETAC) s gl in
      EEVERY [
          ETAC (PURE_REWRITE_TAC[NEG_CLAUSES]) ;
          EREPEAT (ruleseq Cll.ll_par) ;
          EREPEAT withProof ] s gl

	  
    (* ------------------------------------------------------------------------- *)
    (* CLL_PROVE_OUTPUT_ETAC assumes all inputs are atomic and tried to prove    *)
    (* the output using the times and plus rules.                                *)
    (* Both these rules involve branching/searching so we prioritize by term     *)
    (* size. Atomic terms are the fastest to test as they only allow a unique use*)
    (* of the times rule that only carries their negative counterpart in the     *)
    (* context split.                                                            *)
    (* Focusing is automatic here based on the assumptions we have made about    *)
    (* the form of the conjecture (only 1 positive term containing only positive *)
    (* operators).                                                               *)
    (* ------------------------------------------------------------------------- *)
	  
    let rec (CLL_PROVE_OUTPUT_ETAC:seqtactic) =
      fun s ((_,tm) as gl) ->
      try (
        let out = find_output tm in
        if (is_var out) then (
          Cll.llid out s gl
        )
        else let comb,args = strip_comb out in
	         if (comb = `LinTimes`) then
	           let lh,rh = hd args,(hd o tl) args in
	           if (is_var lh) then
	             let nlh = mk_llneg lh in
                 let nltm = mk_msing ( find_ll_term ((=) nlh) tm ) in
	             (ETHEN
                    (rule_seqtac [(`A:LinProp`,lh);
			                      (`B:LinProp`,rh);
			                      (`G:(LinTerm)multiset`,nltm)] Cll.ll_times)
	                CLL_PROVE_OUTPUT_ETAC) s gl
	           else if (is_var rh) then
	             let nrh = mk_llneg rh in
                 let nrtm = mk_msing ( find_ll_term ((=) nrh) tm ) in
	             (ETHEN
	                (ETHENL
	                   (rule_seqtac [(`A:LinProp`,lh);
			                         (`B:LinProp`,rh);
			                         (`D:(LinTerm)multiset`,nrtm)] Cll.ll_times)
	                   [ ALL_ETAC ; CLL_PROVE_OUTPUT_ETAC ])
	                CLL_PROVE_OUTPUT_ETAC) s gl
	           else
	             let iterms = find_input_terms tm in
	             let rec timesProof index s gl =
	               match nextSubsetIndex(index) with
	               | None -> failwith "CLL_PROVE_OUTPUT_ETAC"
	               | Some(i) ->
		              let subset = getIndexedSubset i iterms in
		              let dcontext = list_mk_munion (map mk_msing subset) in
		              let tac = rule_seqtac [(`A:LinProp`,lh);
					                         (`B:LinProp`,rh);
					                         (`D:(LinTerm)multiset`,dcontext)] Cll.ll_times in
		              let select = cllCombSelect out in
		              if (select <= 0)
		              then 		  
		                (EORELSE (ETHEN tac CLL_PROVE_OUTPUT_ETAC) (timesProof i)) s gl
		              else
		                (EORELSE (ETHEN 
			                        (ETHENL tac [ ALL_ETAC ; CLL_PROVE_OUTPUT_ETAC ])
			                        CLL_PROVE_OUTPUT_ETAC)
			               (timesProof i)) s gl in
	             timesProof (createSubsetIndex iterms) s gl
		         
             else if (comb = `LinPlus`) then
	           let select = cllCombSelect out in
	           if (select <= 0)
	           then (EORELSE (ETHEN (ruleseq Cll.ll_plus1) CLL_PROVE_OUTPUT_ETAC)
			           (ETHEN (ruleseq Cll.ll_plus2) CLL_PROVE_OUTPUT_ETAC)) s gl
	           else (EORELSE (ETHEN (ruleseq Cll.ll_plus2) CLL_PROVE_OUTPUT_ETAC)
			           (ETHEN (ruleseq Cll.ll_plus1) CLL_PROVE_OUTPUT_ETAC)) s gl
			   
             else
               failwith "CLL_PROVE_OUTPUT_ETAC"    
      ) with Failure _ -> failwith "CLL_PROVE_OUTPUT_ETAC"



	                    
    let (CLL_PROVE_ETAC:seqtactic) =
      fun s gl ->
	  try (
	    EEVERY [
	        CLL_PROVE_INPUT_ETAC;
	        CLL_PROVE_OUTPUT_ETAC] s gl
      ) with Failure s -> failwith ("CLL_PROVE_TAC: " ^ s)

    let (CLL_PROVE_TAC:astactic) =
      fun s gl ->
      Actionstate.CLL_TAC CLL_PROVE_ETAC s gl


    (* ------------------------------------------------------------------------- *)
    (* FILTER_TAC takes a term cllTerm from assumption lbl and tries to apply a  *)
    (* filter to convert it to target. This fails if CLL_PROVE_TAC fails to      *)
    (* prove the corresponding filter.                                           *)
    (* ------------------------------------------------------------------------- *)
    (* TODO: We can detect if this is an input ourselves! *)
	  
    let (FILTER_TAC:(?glfrees:term list)->string -> term -> term -> bool -> astactic) =
      let PRINT_PROVEN str st gl =
	    (print_string ("-- Proven: " ^ str) ;
	     print_newline();
	     ALL_ETAC st gl) in
      fun ?(glfrees=[]) lbl cllTerm targetProp isInput st gl ->
      (*	print_string ("Trying to match: " ^ (string_of_term cllTerm) ^ " - with : " ^ (string_of_term targetProp));
	print_newline();*)
	  if (isInput) then
	    if ((rand o rand o rator) cllTerm = targetProp) then Actionstate.CLL_TAC ALL_ETAC st gl
	    else 
	      ETHENL (Actionstate.CLL_TAC 
		            (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
			           [`A:LinProp`,(rand o rand o rator) cllTerm; (* rand of NEG *)
			            mk_var("a",Cll.Pcalc.chantp),rand cllTerm;
			            `B:LinProp`,targetProp]
			           (*			  `b:num`,rand cllTerm] (* TODO This needs testing? *)*)
			           Rules.ll_filter_input))
	        [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC) CLL_PROVE_TAC ;
		      PRINT_PROVEN ("|-- NEG (" ^ (string_of_term targetProp) ^ ") , (" ^ ((string_of_term o rand o rand o rator) cllTerm) ^ ")")
	        ] st gl
	  else
	    if ((rand o rator) cllTerm = targetProp) then Actionstate.CLL_TAC ALL_ETAC st gl
	    else
	      ETHENL (Actionstate.CLL_TAC 
		            (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
			           [`A:LinProp`,(rand o rator) cllTerm;
			            mk_var("a",Cll.Pcalc.chantp),rand cllTerm;
			            `B:LinProp`,targetProp]
			           (*`b:num`,rand cllTerm] (* TODO This needs testing? *)*)
			           Rules.ll_filter_output))
	        [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC) CLL_PROVE_TAC ;
		      PRINT_PROVEN ("|-- NEG (" ^ ((string_of_term o rand o rator) cllTerm) ^ ") , (" ^ (string_of_term targetProp) ^ ")")
	        ] st gl
	  


    (* ------------------------------------------------------------------------- *)
    (* ------------------------------------------------------------------------- *)

    let TENSOR_TAC : actiontactic =
      fun act thml thmr s (asl,w as gl) ->
      let outl = try (find_output (concl thml)) with Failure _ -> failwith "TENSOR: Left process has no output"
      and outr = try (find_output (concl thmr)) with Failure _ -> failwith "TENSOR: Right process has no output"
      and inputsr = (list_mk_munion o (map mk_msing) o find_input_terms o concl) thmr in
      (*      
      let llma s gl' =
	let mvs = (subtract (gl_frees gl') (gl_frees gl)) @ (get_ll_channels (concl thml)) @ (get_ll_channels (concl thmr)) in 
	Cll.ll_meta_lbl_asm act.Action.rarg mvs gl',s in*)
      (ETHENL (
           Actionstate.CLL_TAC (frule_seqtac ~lbl:act.Action.larg ~reslbl:act.Action.res
					              [(`A:LinProp`,outl);(`B:LinProp`,outr);
					               (`D:(LinTerm)multiset`,inputsr)] Cll.ll_times))
	     [ Actionstate.CLL_TAC (prove_by_seq act.Action.rarg) ; ALL_ETAC ])
        (Actionstate.set_prov (timesprov act.Action.larg act.Action.rarg act.Action.res s.Actionstate.prov) s) gl	



    (* ------------------------------------------------------------------------- *)
    (* ------------------------------------------------------------------------- *)
	  
    let WITH_TAC : actiontactic =
      fun act thml thmr st (asl,w as gl) ->
      let glfrees = gl_frees gl in
      let conl = concl thml
      and conr = concl thmr in
      let inputsl = find_input_terms conl 
      and inputsr = find_input_terms conr in
      let outl = find_output conl
      and outr = find_output conr in

      let find_sel sel = (* string_matches_term sel ((rand o rator) input) in *)
        try ( 
          let tm = parse_term sel in
          let tm' = if (is_llneg tm) then tm
                    else mk_llneg (try_type `:LinProp` tm) in
          fun input -> tm' = (rand o rator) input
        )
	    with Failure _ -> failwith ("WITH_TAC: Failed to parse term `"^sel^"`") in
	    
      let rh,rinputs = try ( remove (find_sel act.Action.rsel) inputsr ) 
		               with Failure _ -> failwith ("WITH_TAC: Input `"^act.Action.rsel^"` not found in: " 
						                           ^ (string_of_term conr)) 
      and lh,linputs = try ( remove (find_sel act.Action.lsel) inputsl ) 
		               with Failure _ -> failwith ("WITH_TAC: Input `"^act.Action.lsel^"` not found in: " 
						                           ^ (string_of_term conl)) in

      (* Remove common propositions (comparing with propEq) from the 2 lists *)
      let remove_props lins rins = 
      (* Given 2 terms of the form `NEG A <> a` and `NEG B <> b` compare A = B *)
        let propEq l r = 
	      (rand o rand o rator) l = (rand o rand o rator) r in
        let rec remove_props' lins rins lrest removed =
	      match (lins,rins) with
	      | [],_ -> removed,lrest,rins
	      | l::t,_ -> try (
	                    let r,rest = remove (propEq l) rins in
	                    remove_props' t rest lrest ((l,r)::removed)
                      )
	                  with Failure _ ->
	                    remove_props' t rins (l::lrest) removed in
        remove_props' lins rins [] [] in
                
      (* Filter the left input to match the right or vice versa *)
      let matchInputTac inputl inputr originputs =  
        let TAG_MERGED_TAC lbl chans st (asl,_) = 
          let thm = try ( assoc lbl asl )
	                with Failure _ -> failwith ("WITH_TAC: Failed to find filtered assumption: " ^ lbl) in
	      let newinputs = (find_input_terms o concl) thm in
          let merged = remove_list newinputs originputs in
          if (length merged = 1) 
          then ALL_ETAC (Actionstate.add_merged (hd merged) chans st) gl 
          else failwith ("WITH_TAC: Failed to find filtered channel: " ^ lbl) in
	    EORELSE
	      (ETHEN
             (FILTER_TAC ~glfrees:glfrees act.Action.larg inputl ((rand o rand o rator) inputr) true)
             (TAG_MERGED_TAC act.Action.larg (rand inputl, rand inputr)))
	      (ETHEN
             (FILTER_TAC ~glfrees:glfrees act.Action.rarg inputr ((rand o rand o rator) inputl) true)
             (TAG_MERGED_TAC act.Action.rarg (rand inputl, rand inputr)))
      in
      
      (* Match inl with any of the inputsr via filtering *)
      let matchInputWithAnyTac inl inputsr =
        let rchans = map rand inputsr in 
	    let filter_tacs = map (fun i -> matchInputTac inl i rchans) inputsr in 
	    EFIRST filter_tacs in

      (* Add buffers for any extra inputs that were not matched *)
	  let bufferInputsTac lbl provlbl out extras st =
	    if (extras = []) then ALL_ETAC st 
	    else
	      (* I can no longer tell why we are sortin here, but there must be a reason. *)
	      (* Sort by linprop name *)
	      let inputSorter l r =
	        (string_of_term o rand o rand o rator) l < (string_of_term o rand o rand o rator) r in
	      let extras_sorted = sort inputSorter extras in
	      (* Get the linprops of each input *)
          let extras_props = map (rand o rand o rator) extras_sorted in 
          (* Tensor them - This is the output type of PARBUF we want to build *)
	      let extraout = itlist (fun x y -> list_mk_icomb "LinTimes" [x;y]) 
	                       (butlast extras_props) (last extras_props) in
          (* And these are the inputs of the PARBUF *)
	      let ins = list_mk_munion (map mk_msing extras) in
	      
          (* We don't care about output provenance, because it will all come from the merge node! *)
          (* TODO Maybe we still need to store the original provenance. Can this be useful? *)
          (*
	        let inputprov tm = prov_of_tm (lbl ^ ":" ^ (string_of_term (rand tm))) ((rand o rand o rator) tm) in
	        let inprovs = map inputprov extras_sorted in
	        let outprov = itlist provtimes (butlast inprovs) (last inprovs) in
           *)
	      ETHENL (Actionstate.CLL_TAC (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees 
					                     [(`A:LinProp`,out);(`B:LinProp`,extraout);
					                      (`D:(LinTerm)multiset`,ins)] 
					                     Cll.ll_times))
	        [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC) PARBUF_TAC ; ALL_ETAC ]
	        (* (Actionstate.set_prov (timesprov_r provlbl outprov lbl st.Actionstate.prov) st) in *)
            st in
	 
      
      let rec matchInputsTac lins rins extrasl extrasr =  
        (* Remove a channel that was merged *)
        let remove_chan (_,_,chan) ins = 
          let check tm = (string_of_term o rand) tm = chan in
          remove check ins in

	    match (lins,rins) with
	    | [] , [] -> (* No inputs left to match, so just buffer the extras and finish *)
           EEVERY [
	           bufferInputsTac act.Action.larg act.Action.rarg outl extrasr ;
	           bufferInputsTac act.Action.rarg act.Action.larg outr extrasl
	         ]
	    | _ , [] -> (* We matched all the inputs on the right, so add the inputs on the left as extras *)
           matchInputsTac [] [] (extrasl @ lins) extrasr
	    | [] , _ -> (* We matched all the inputs on the left, so add the intputs on the right as extras *)
           matchInputsTac [] [] extrasl (extrasr @ rins)
	    | (hl :: restl) , _ -> (* We have unmatched inputs on both sides *)
	       EORELSE
             (* Try to match the first input on the left with one on the right *)
             (* If that succeeds, keep going without adding any extras *)
             (* In the next iteration, hl will match with another input and will be removed by remove_props *)
	         (ETHEN (matchInputWithAnyTac hl rins) (
                  fun st ->
                  let _,rins' = remove_chan (Actionstate.get_lmerge (rand hl) st) rins in
                  matchInputsTac restl rins' extrasl extrasr st
             ))
             (* If that fails, hl does not have a match, so add it as an extra and keep going *)
             (* This time it will be removed by remove_list *)
	         (matchInputsTac restl rins (hl :: extrasl) extrasr)
	  in
      
      let matchOutputTac st (asl,w as gl) =
	    (* Try to make the outputs match. *)
	    let thml = try ( assoc act.Action.larg asl ) with Failure _ -> failwith ("WITH_TAC") 
	    and thmr = try ( assoc act.Action.rarg asl ) with Failure _ -> failwith ("WITH_TAC") in
	    let conl = concl thml
	    and conr = concl thmr in
	    let outl = find_output conl
	    and outr = find_output_term conr in
        (* Try a filter to convert one output to the other *)
        (* Note that if they already match, FILTER_TAC will not do anything *)
	    ETRY (FILTER_TAC ~glfrees:glfrees act.Action.rarg outr outl false) st gl in 

      
      let withTac st (asl,w as gl) =
	    (* By now inputs must match perfectly, but outputs may be filtered, so detect them again. *)
	    let thml = try ( assoc act.Action.larg asl ) with Failure _ -> failwith ("WITH_TAC") 
	    and thmr = try ( assoc act.Action.rarg asl ) with Failure _ -> failwith ("WITH_TAC") in
	    let conl = concl thml
	    and conr = concl thmr in
	    let outl = find_output conl
	    and outr = find_output conr in

	    let tac =
	      if (outl = outr) then
	        ETHEN (
	            Actionstate.CLL_TAC (
		            drule_seqtac ~lbl:act.Action.larg ~reslbl:act.Action.res ~glfrees:glfrees
		              [(`A:LinProp`,(rand o rand o rator) lh);(mk_var("a",Cll.Pcalc.chantp),rand lh);
		               (`B:LinProp`,outl);
		               (`C:LinProp`,(rand o rand o rator) rh);(mk_var("c",Cll.Pcalc.chantp),rand rh)]
		              Rules.ll_with_serv))
	          (Actionstate.ADD_PROV_TAC act.Action.res (prov_of_tm ("&" ^ act.Action.res) outl))
	      else 
	        (* TODO cases of single input, optional outputs can always match *)
	        ETHEN (
	            Actionstate.CLL_TAC (
		            drule_seqtac ~lbl:act.Action.larg ~reslbl:act.Action.res ~glfrees:glfrees
		              [(`A:LinProp`,(rand o rand o rator) lh);(mk_var("a",Cll.Pcalc.chantp),rand lh);
		               (`B:LinProp`,outl);
		               (`C:LinProp`,(rand o rand o rator) rh);(mk_var("c",Cll.Pcalc.chantp),rand rh);
		               (`D:LinProp`,outr)]
		              Rules.ll_with_outputs))
		      (Actionstate.ADD_PROV_TAC act.Action.res (provplus (prov_of_tm ("&" ^ act.Action.res) outl) (prov_of_tm ("&" ^ act.Action.res) outr))) in
	    ETHENL tac [ Actionstate.CLL_TAC (prove_by_seq act.Action.rarg) ; ETAC (REMOVE_TAC act.Action.rarg) ] st gl in

      (*let _ = (print_string act.Action.res ; print_newline();
	       print_string "A:LinProp > "; print_term ((rand o rand o rator) lh); print_newline();
	       print_string "a > "; print_term (rand lh); print_newline();
	       print_string "B:LinProp > "; print_term outl'; print_newline();
	       print_string "C:LinProp > "; print_term ((rand o rand o rator) rh); print_newline();
	       print_string "c > "; print_term (rand rh); print_newline();
	       print_string "D:LinProp > "; print_term outr'; print_newline()
      ) in *)

      let matched,lins,rins = remove_props linputs rinputs in
      let merge (l,r) s = Actionstate.add_merged  l (rand l, rand r) s in
      let res = (mk_llneg o list_mk_comb) (`LinPlus`,[(rand o rand o rator) lh;(rand o rand o rator) rh]) in
      let st' = itlist merge matched (Actionstate.add_merged res (rand lh, rand rh) st) in

      EEVERY ([
	        (ETAC (COPY_TAC (act.Action.rarg,"_right_")));
	        (ETAC (COPY_TAC (act.Action.larg,"_left_")));
            matchInputsTac lins rins [] [];
	        matchOutputTac;
	        withTac;
	        ETRY (ETAC (REMOVE_TAC act.Action.rarg));
	        ETRY (ETAC (REMOVE_TAC act.Action.larg));
	        (ETAC (RENAME_TAC ("_right_",act.Action.rarg)));
	        (ETAC (RENAME_TAC ("_left_",act.Action.larg)))
        ]) st' gl
	  

    (* ------------------------------------------------------------------------- *)
    (* ------------------------------------------------------------------------- *)




	  
    (* primary = None && priority not None = when we want to use ANY input but at least one! *)
	  
    let rec INPUT_TAC': term list -> term option -> term list -> string list option -> bool -> term -> provtree -> string -> string -> astactic =    
      fun glfrees primary inchans priority or_left target prov lbl joinlbl st (asl,_ as gl) ->
      (* 	print_goal gl;
	print_newline ();
	print_string "INPUT_TAC' ";
	(match primary with
	  | None -> print_string "None"
	  | Some p -> print_string ("Some(" ^ (string_of_term p) ^ ")"));
	print_string " [";
	ignore (print_tml inchans) ;
	print_string "] ";
	(match priority with
	| None -> print_string "None "
	| Some l -> print_string ("(Some \"" ^ (implode l) ^ "\") ")) ;
	print_bool or_left ;
	print_string " " ;
	print_term target ;
	print_string " " ;
	print_string lbl ;
	print_newline () ; *)

      let matchInputTac lbl priority inputs target elsetac st (asl,w as gl) =
        (*	print_string "Inputs: ";
	print_tml inputs;
	print_newline ();
	print_string "Target: ";
	print_term target;
	print_newline ();
	print_string "Priority: ";
	(match priority with
	  | None -> print_string "-NONE-"
	  | Some l -> print_string (String.concat "" l)) ;
	print_newline() ;*)
	    
	    let tryinputs = if (priority = None) then inputs else
	                      match primary with
	                      | None -> inputs
	                      | Some p -> 
	                         let primaryinput = try (fst (remove (fun x -> (rand o rator) x = p) inputs))
		                                        with Failure _ -> failwith ("INPUT_TAC: Failed to find input to match selected term: " ^ (string_of_term p)) in
	                         [primaryinput] in
	    
	    (* Avoid filtering if you can. *)
	    let rec directMatch l = (* if (mem target (map (rand o rand o rator) inputs)) *)
	      match l with
	      | [] -> None
	      | h :: t ->
	         if (target = (rand o rand o rator) h)
	         then Some(rand h)
	         else None in
	    
	    match directMatch tryinputs with
	    | Some c -> Actionstate.ADD_IPROV_TAC target (Provleaf (string_of_term c ^ ":" ^ string_of_int st.Actionstate.ctr)) (Actionstate.inc 1 st) gl
	    (* (prov_of_tm (string_of_term c) target)*)
	    | None -> 
	       (* else find an input that can be filtered to match target. *)
	       let filter_tac i = ETHEN (FILTER_TAC ~glfrees:glfrees lbl i target true)
	                            (* (prov_of_tm (string_of_term (rand i)) target)*)
	                            (Actionstate.ADD_IPROV_TAC target (Provleaf (string_of_term (rand i) ^ ":" ^ string_of_int (st.Actionstate.ctr - 1)))) in
	       let filter_tacs = map filter_tac tryinputs in
	       (* Try them all, else use elsetac. *)
	       EFIRST (filter_tacs @ [elsetac]) (Actionstate.inc 1 st) gl in (* We could buffer missing inputs here, but it will get confusing. *)

      let isOrigInput inchans input = mem (rand input) inchans in 
      
      let thm = try (assoc lbl asl)
	            with Failure _ -> failwith ("INPUT_TAC: Failed to find process: " ^ lbl) in
      let ins = ((filter (isOrigInput inchans)) o find_input_terms o concl) thm 
      and out = find_output (concl thm) in
      
      if (is_var target or is_const target) then
	    let tac st gl = 
     	  match priority with
	      | None ->
	         if or_left then
	           ETHEN (
	               ETHENL (Actionstate.CLL_TAC (
		                       drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
		                         [(`B:LinProp`,target);(`A:LinProp`,out)] Rules.ll_times_buf_left))
		             [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC) BUFFER_TAC ; ALL_ETAC ])
		         (Actionstate.ADD_IPROV_TAC target (Provleaf "#"))
		         (Actionstate.set_prov (timesprov_l prov lbl lbl st.Actionstate.prov) st) gl
	         else
	           ETHEN (
		           ETHENL (Actionstate.CLL_TAC (
		                       drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
		                         [(`B:LinProp`,target);(`A:LinProp`,out)] Rules.ll_times_buf_right))
		             [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC) BUFFER_TAC ; ALL_ETAC ])
		         (Actionstate.ADD_IPROV_TAC target (Provleaf "#"))
		         (Actionstate.set_prov (timesprov_r lbl prov lbl st.Actionstate.prov) st) gl
	      | _ -> failwith ("INPUT_TAC: Failed to find matching input for: " ^ (string_of_term target)) in
	    matchInputTac lbl priority ins target tac st gl
	    
      else
	    let combtac st gl =
	      let comb,args = strip_comb target in
	      let lh,rh = hd args,(hd o tl) args
	      and lprov,rprov = match prov with
	        | Provnode(_,l,r) -> l,r
	        | _ -> failwith ("INPUT_TAC: Invalid provenance for term `" ^ (string_of_term target) ^ "`: " ^ (string_of_prov prov)) in
	      
	      let leftfirst,lp,lor_left,rp,ror_left = match priority with
	        | None -> true,None,or_left,None,or_left
	        | Some [] -> failwith ("INPUT_TAC: Failed to find input: " ^ (string_of_term target)) 
	        | Some ("l"::"r"::t) -> true,Some t,or_left,None,false
	        | Some ("r"::t) -> false,None,true,Some t,or_left
	        | Some (_::t) -> true,None,or_left,None,or_left in
	      
	      let sidePrepTac primary inchans p or_left target prov st (asl,w as gl) =
	        let thm = try (assoc lbl asl)
	                  with Failure _ -> failwith ("INPUT_TAC: Failed to find process: " ^ lbl) in
	        let ins = ((filter (isOrigInput inchans)) o find_input_terms o concl) thm in
	        let tac = INPUT_TAC' glfrees primary inchans p or_left target prov lbl joinlbl in
	        matchInputTac lbl p ins target tac st gl in
	      
	      
	      if comb = `LinTimes` then
	        
	        let preptac =
	          if (leftfirst) then
		        let _,restins = try (remove (fun x -> (rand o rand o rator) x = lh) ins) with Failure _ -> lh,ins in
		        ETHEN (sidePrepTac primary inchans lp lor_left lh lprov) (sidePrepTac None (map rand restins) rp ror_left rh rprov)
	          else
		        let _,restins = try (remove (fun x -> (rand o rand o rator) x = rh) ins) with Failure _ -> rh,ins in
		        ETHEN (sidePrepTac primary inchans rp ror_left rh rprov) (sidePrepTac None (map rand restins) lp lor_left lh lprov) in
	        
	        EEVERY [
	            preptac ;
	            Actionstate.CLL_TAC (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
		                               [(`A:LinProp`,lh);(`B:LinProp`,rh)] Rules.ll_par_input);
	            Actionstate.TIMES_IPROV_TAC lh rh ] st gl
	        
	        
	      else if comb = `LinPlus` then
	        
	        let failtac st gl =
	          if or_left then
	            ETHEN (
		            ETHENL (Actionstate.CLL_TAC
		   	                  (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
			                     [(`B:LinProp`,target);(`A:LinProp`,out)] Rules.ll_times_buf_left))
			          [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC) BUFFER_TAC ; ALL_ETAC ])
		          (Actionstate.ADD_IPROV_TAC target (prov_of_tm "#" target))
		          (Actionstate.set_prov (timesprov_l prov lbl lbl st.Actionstate.prov) st) gl
	          else
	            ETHEN (
		            ETHENL (Actionstate.CLL_TAC
  			                  (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
			                     [(`B:LinProp`,target);(`A:LinProp`,out)] Rules.ll_times_buf_right))
			          [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC) BUFFER_TAC ; ALL_ETAC ])
		          (Actionstate.ADD_IPROV_TAC target (prov_of_tm "#" target))
		          (Actionstate.set_prov (timesprov_r lbl prov lbl st.Actionstate.prov) st) gl in

	        let tac leftfirst st (asl,_ as gl) =
		      (* Need to get inputs/outputs after the recursion of INPUT_TAC *)
	          let thm = try (assoc lbl asl) with Failure _ -> failwith ("INPUT_TAC: Failed to find process: " ^ lbl) in
	          let ins = find_input_terms (concl thm)
	          and outTerm = find_output_term (concl thm) in
	          let out = (rand o rator) outTerm in
	          
	          let _,inputsl = try ( remove (fun x -> (rand o rand o rator) x = lh) ins ) with Failure _ -> lh,ins
	          and _,inputsr = try ( remove (fun x -> (rand o rand o rator) x = rh) ins ) with Failure _ -> rh,ins in

	          let lcase_eq_tac st gl = 
		        EEVERY [ 
		            (ETHENL (Actionstate.CLL_TAC
			                   (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
				                  [(`A:LinProp`,lh);
				                   (`C:LinProp`,rh)] Rules.ll_with_serv))
		               [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC) PARBUF_TAC ; ALL_ETAC ]);
		            (* Special case: Mark as connected even though it is buffered! *)
		            (Actionstate.ADD_IPROV_TAC rh (prov_of_tm ("&" ^ joinlbl) rh)); 
		            (Actionstate.PLUS_IPROV_TAC lh rh)]
		          (Actionstate.set_prov (assoc_add lbl (prov_of_tm ("&" ^ joinlbl) out) st.Actionstate.prov) st) gl
		        
	          and lcase_rheq_tac st gl =
		        if (is_binop `LinPlus` out) then
		          let target = list_mk_comb (`LinPlus`,[(rand o rator) out;rh]) in 
		          EEVERY [
		              (ETHENL (Actionstate.CLL_TAC
			                     (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
				                    [(`C:LinProp`,rh);
				                     (`A:LinProp`,lh)] Rules.ll_with_serv))
			             [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC)
				             (EORELSE (ETHEN (Actionstate.CLL_TAC (ruleseq ~glfrees:glfrees Cll.ll_plus1)) PARBUF_TAC)
					            (ETHEN (Actionstate.CLL_TAC (ruleseq ~glfrees:glfrees Cll.ll_plus2)) PARBUF_TAC) )
			             ; ALL_ETAC ]) ;
		              (* Special case: Mark as connected even though it is buffered! *)
		              (Actionstate.ADD_IPROV_TAC rh (prov_of_tm ("&" ^ joinlbl) rh));
		              (Actionstate.PLUS_IPROV_TAC lh rh)]
		            (Actionstate.set_prov (assoc_add lbl (prov_of_tm ("&" ^ joinlbl) out) st.Actionstate.prov) st) gl
		        else FAIL_ETAC "" st gl 
		        
	          and lcase_lheq_tac st gl =
		        if (is_binop `LinPlus` out) then
		          let target = list_mk_comb (`LinPlus`,[rh;rand out]) in 
		          EEVERY [
		              (ETHENL (Actionstate.CLL_TAC
			                     (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
				                    [(`B:LinProp`,rh);
				                     (`C:LinProp`,rand out);
				                     (`A:LinProp`,lh)] Rules.ll_with_buf_right1))
		                 [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC) BUFFER_TAC ; ALL_ETAC ]) ;
		              (* Special case: Mark as connected even though it is buffered! *)
		              (Actionstate.ADD_IPROV_TAC rh (prov_of_tm ("&" ^ joinlbl) rh));
		              (Actionstate.PLUS_IPROV_TAC lh rh)]
		            (Actionstate.set_prov (assoc_add lbl (prov_of_tm ("&" ^ joinlbl) out) st.Actionstate.prov) st) gl
		        else FAIL_ETAC "" st gl
		        
	          and lelse_tac st gl =
		        let inputprov tm = prov_of_tm (lbl ^ ":" ^ (string_of_term (rand tm))) ((rand o rand o rator) tm) in
		        let outr = itlist (fun x y -> list_mk_icomb "LinTimes" [x;y]) (map (rand o rand o rator) inputsl) rh
		        and outprov = itlist provtimes (map inputprov inputsl) rprov in
		        EEVERY [
		            ETHENL (Actionstate.CLL_TAC
			                  (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
			                     [(`A:LinProp`,lh);
				                  (`B:LinProp`,out);
				                  (`C:LinProp`,rh);
				                  (`D:LinProp`,outr)] Rules.ll_with_outputs))
		              [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC) PARBUF_TAC ; ALL_ETAC ] ;
		            (Actionstate.ADD_IPROV_TAC rh (prov_of_tm "#" rh));
		            (Actionstate.PLUS_IPROV_TAC lh rh)]
		          (Actionstate.set_prov (plusprov_r lbl outprov lbl st.Actionstate.prov) st) gl
		        
		        
		        
	          and rcase_eq_tac st gl =
		        EEVERY [ 
		            (ETHENL (Actionstate.CLL_TAC
			                   (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
				                  [(`A:LinProp`,lh);
				                   (`C:LinProp`,rh)] Rules.ll_with_serv2))
		               [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC) PARBUF_TAC ; ALL_ETAC ]) ;
		            (* Special case: Mark as connected even though it is buffered! *)
		            (Actionstate.ADD_IPROV_TAC lh (prov_of_tm ("&" ^ joinlbl) lh));
		            (Actionstate.PLUS_IPROV_TAC lh rh)]
		          (Actionstate.set_prov (assoc_add lbl (prov_of_tm ("&" ^ joinlbl) out) st.Actionstate.prov) st) gl
		        
	          and rcase_rheq_tac st gl =
		        if (is_binop `LinPlus` out) then
		          let target = list_mk_comb (`LinPlus`,[(rand o rator) out;lh]) in 
		          EEVERY [
		              (ETHENL (Actionstate.CLL_TAC
			                     (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
				                    [(`C:LinProp`,lh);
				                     (`B:LinProp`,(rand o rator) out);
				                     (`A:LinProp`,rh)] Rules.ll_with_buf_left2))
		                 [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC) BUFFER_TAC ; ALL_ETAC ]) ;
		              (* Special case: Mark as connected even though it is buffered! *)
		              (Actionstate.ADD_IPROV_TAC lh (prov_of_tm ("&" ^ joinlbl) lh));
		              (Actionstate.PLUS_IPROV_TAC lh rh)]
		            (Actionstate.set_prov (assoc_add lbl (prov_of_tm ("&" ^ joinlbl) out) st.Actionstate.prov) st) gl
		        else FAIL_ETAC "" st gl 
		        
	          and rcase_lheq_tac st gl =
		        if (is_binop `LinPlus` out) then
		          let target = list_mk_comb (`LinPlus`,[lh;rand out]) in 
		          EEVERY [
		              (ETHENL (Actionstate.CLL_TAC
			                     (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
				                    [(`C:LinProp`,rh); 
				                     (`A:LinProp`,lh)] Rules.ll_with_serv2))
			             [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC)
				             (EORELSE (ETHEN (Actionstate.CLL_TAC (ruleseq ~glfrees:glfrees Cll.ll_plus1)) PARBUF_TAC)
					            (ETHEN (Actionstate.CLL_TAC (ruleseq ~glfrees:glfrees Cll.ll_plus2)) PARBUF_TAC) )
			             ; ALL_ETAC ]) ;
		              (* Special case: Mark as connected even though it is buffered! *)
		              (Actionstate.ADD_IPROV_TAC lh (prov_of_tm ("&" ^ joinlbl) lh));
		              (Actionstate.PLUS_IPROV_TAC lh rh)]
                    (Actionstate.set_prov (assoc_add lbl (prov_of_tm ("&" ^ joinlbl) out) st.Actionstate.prov) st) gl
		        else FAIL_ETAC "" st gl
		        
	          and relse_tac st gl =
		        print_string "relse_tac"; print_newline(); 
		        let inputprov tm = prov_of_tm (lbl ^ ":" ^ (string_of_term (rand tm))) ((rand o rand o rator) tm) in
		        let outl = itlist (fun x y -> list_mk_icomb "LinTimes" [x;y]) (map (rand o rand o rator) inputsr) lh
		        and outprov = itlist provtimes (map inputprov inputsr) lprov in
		        EEVERY [
		            ETHENL (Actionstate.CLL_TAC
			                  (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
			                     [(`C:LinProp`,rh);
				                  (`D:LinProp`,out);
				                  (`A:LinProp`,lh);
				                  (`B:LinProp`,outl)] Rules.ll_with_outputs2))
		              [ ETHEN (ETAC REMOVE_ALL_ASSUMS_TAC) PARBUF_TAC ; ALL_ETAC ];
		            (Actionstate.ADD_IPROV_TAC lh (prov_of_tm "#" lh));
		            (Actionstate.PLUS_IPROV_TAC lh rh)]
		          (Actionstate.set_prov (plusprov_l outprov lbl lbl st.Actionstate.prov) st) gl in 
	          
	          if (leftfirst) then (* left first *)
		        EFIRST [lcase_rheq_tac;lcase_eq_tac;lelse_tac] st gl
	          else
		        EFIRST [rcase_lheq_tac;rcase_eq_tac;relse_tac] st gl
		      
	        in

	        if (priority = None) then
		      EFIRST [
		          (* Set priorities to fail if no inputs match (part of) each side.*)
		          ETHEN (sidePrepTac None inchans (Some ["l";"r"]) lor_left lh lprov) (tac true);
		          ETHEN (sidePrepTac None inchans (Some ["r"]) ror_left rh rprov) (tac false);
		          failtac ] st gl
	        else if (leftfirst) then
		      ETHEN (sidePrepTac primary inchans lp lor_left lh lprov) (tac true) st gl
	        else
		      ETHEN (sidePrepTac primary inchans rp ror_left rh rprov) (tac false) st gl
		    
	      else failwith ("INPUT_TAC: Unable to construct input: " ^ (string_of_term target)) in
	    matchInputTac lbl priority ins target combtac st gl
	    
    let INPUT_TAC: term list -> term -> term list -> term -> provtree -> string -> string -> string -> astactic =
      fun glfrees primary inchans target prov priority lbl joinlbl -> INPUT_TAC' glfrees (Some primary) inchans (Some (explode priority)) true target prov lbl joinlbl 
	  	                                                            


	                                                                
    let JOIN_TAC: actiontactic =
      fun act thml thmr ->
	  let out = find_output (concl thml)
	  and inlist = (find_input_terms o concl) thmr
	  and inputs = (list_mk_munion o (map mk_msing) o find_input_terms o concl) thml in
	  let primary = try ( 
                      let tm = parse_term act.Action.rsel in
                      if (is_llneg tm) then tm 
                      else mk_llneg (try_type `:LinProp` tm)
                    )
	                with Failure _ -> failwith ("JOIN_TAC: Failed to parse term `"^act.Action.rsel^"`") in
	  
	  let cuttac glfrees cut lbl =
	    Actionstate.CLL_TAC (drule_seqtac ~lbl:lbl ~reslbl:act.Action.res ~glfrees:glfrees
					           [`C:LinProp`,out; `G:(LinTerm)multiset`,inputs] cut) in
	  
      (*	let llma glfrees st gl =
	  let mvs = (subtract (gl_frees gl) glfrees) @ (get_ll_channels (concl thml)) @ (get_ll_channels (concl thmr)) in
	  Cll.ll_meta_lbl_asm act.Action.larg mvs gl,st in *)

	  let provtac st =
	    let rprov = try ( assoc act.Action.rarg st.Actionstate.prov ) with Failure _ -> (
	                  warn true ("JOIN_TAC: Failed to find provenance for composed output of: " ^ act.Action.rarg);
	                  prov_of_tm act.Action.rarg (find_output (concl thmr))) in
	    Actionstate.ADD_PROV_TAC act.Action.res rprov st in

      (*
	  let showtac st (asl,w as gl) =
	    let s = act.Action.res in
	    let th = try assoc s asl with Failure _ ->
	               failwith("JOIN_TAC: failed to produce assumption "^s) in
     	let connected = subtract inlist (find_input_terms (concl th)) in
	    ALL_TAC gl,st in
	  *)

	  fun st gl ->
	  let glfrees = gl_frees gl in
	  let lprov = try ( assoc act.Action.larg st.Actionstate.prov ) with Failure _ -> (
	                warn true ("JOIN_TAC: Failed to find provenance for output of: " ^ act.Action.larg);
	                prov_of_tm act.Action.larg out)
	  and rprov = try ( assoc act.Action.rarg st.Actionstate.prov ) with Failure _ -> (
	                warn true ("JOIN_TAC: Failed to find provenance for output of: " ^ act.Action.rarg);
	                prov_of_tm act.Action.rarg (find_output (concl thmr))) in
	  
	  EEVERY [
	      (ETAC (COPY_TAC (act.Action.rarg,"_right_"))); 
	      INPUT_TAC glfrees primary ((map rand o find_input_terms o concl) thmr) out lprov act.Action.lsel act.Action.rarg act.Action.res;
	      (*(cuttac ll_cut' lblr THENL [llma glf ; USE_THEN lblr showtac])
		ORELSE*) (* TODO: Reenable ll_cut' ?? *)
	      ETHENL (cuttac glfrees Cll.ll_cut act.Action.rarg) [Actionstate.CLL_TAC (prove_by_seq act.Action.larg) ; ALL_ETAC] ;
	      provtac ;
	      ETRY (ETAC (REMOVE_TAC act.Action.rarg));
	      (ETAC (RENAME_TAC ("_right_",act.Action.rarg)));
	      Actionstate.ADD_PROV_TAC act.Action.rarg rprov
	      (* ; showtac *)
	    ] st gl

  end;;



