(* ========================================================================= *)
(* Advance inference rules for CLL                                           *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2011-2019                                 *)
(* ========================================================================= *)

(* Dependencies *)

needs "embed/sequent.ml";;
needs (!serv_dir ^ "CLL/CLL_prover.ml");;

(*
(* Version of cut rule for same channels. *)

(* This is pi-calculus specific. Need to move away from here. *)

let ll_cut' =  prove (
  `|-- (' (NEG C <> x)^D) P ===>
|-- (G^' (C <> x)) Q ===>
|-- (G^D) (Res [x] (Comp P Q))`,
  MIMP_TAC THEN REPEAT DISCH_TAC THEN
    subgoal_tac `|-- (G^D) (Res [x] (Comp (SUBN1 P (x,x)) (SUBN1 Q (x,x))))`
	THENL [ llrule_tac [`C`,`C`] (REWRITE_RULE CLL_PROCS ll_cut) ; simp[piSUBN1_I] ]
	THEN llassumption);;
*)

module Cllrules =
  functor (Cll : Cllproc_type) ->
  struct

    let voper = "_OPER_"

    let rprove (tm,tac) = 
      let tm' = instantiate (term_match [] (find_var "_OPER_" tm) Cll.oper) tm in
      constr_prove (tm', tac)
                     
    (* The ll_par_input rule is a simple variation of ll_par applied directly to *)
    (* inputs. A composite input is created as we also use NEG_CLAUSES to        *)
    (* demonstrate that.                                                         *)
      
    let ll_par_input = rprove ( `?Q . 
                                (_OPER_ (G^' (NEG A <> a)^' (NEG B <> b)) P) ===> 
                                  (_OPER_ (G^' (NEG (A ** B) <> z)) Q)`,
                                    (EEVERY [ ETAC (MDISCH_TAC THEN REWRITE_TAC[NEG_CLAUSES]); 
	                                          ruleseq Cll.ll_par; seqassumption]))
                     
      
    (* The ll_times_buf rules compose a service with a buffer using the ll_times *)
    (* rule.                                                                     *)
    (* The buffered output can be either added to the left or the right of the   *)
    (* original service's output.                                                *)
      
    let ll_times_buf_right = rprove ( `?R .
                                      (_OPER_ (G ^ ' (A <> a)) P) ===>
	                                    (_OPER_ (' (NEG B <> buf) ^ ' (B <> b)) Q) ===>
	                                    (_OPER_ (G ^ ' (NEG B <> buf) ^ ' ((A ** B) <> z)) R)`,
                                          (EEVERY [ ETAC (REPEAT MDISCH_TAC) ;
	                                                ruleseq Cll.ll_times;
	                                                seqassumption]))
                           
    let ll_times_buf_left = rprove ( `?R .
                                     (_OPER_ (G ^ ' (A <> a)) P) ===>
	                                   (_OPER_ (' (NEG B <> buf) ^ ' (B <> b)) Q) ===>
	                                   (_OPER_ (' (NEG B <> buf) ^ G ^ ' ((B ** A) <> z)) R)`,
                                         (EEVERY [ ETAC (REPEAT MDISCH_TAC) ;
	                                               ruleseq Cll.ll_times;
	                                               seqassumption]))
                          
                          
    (* A weaker version of the ll_with rule that makes more sense in the web    *)
    (* services domain.                                                         *)
      
    let ll_with_serv = rprove ( `?R .
                                (_OPER_ (G ^ ' (NEG A <> a) ^ ' (B <> b)) P) ===> 
	                              (_OPER_ (G ^ ' (NEG C <> c) ^ ' (B <> b)) Q) ===>
	                              (_OPER_ (G ^ ' (NEG (A ++ C) <> x) ^ ' (B <> b)) R)`,
                                    (EEVERY [ ETAC (REPEAT MDISCH_TAC THEN REWRITE_TAC[NEG_CLAUSES]); 
	                                          ruleseq Cll.ll_with; seqassumption]))
                     
                     
    let ll_with_serv2 = rprove ( `?R . 
                                 (_OPER_ (G ^ ' (NEG C <> c) ^ ' (B <> b)) Q) ===>
	                               (_OPER_ (G ^ ' (NEG A <> a) ^ ' (B <> b)) P) ===>
	                               (_OPER_ (G ^ ' (NEG (A ++ C) <> x) ^ ' (B <> b)) R)`,
                                     (EEVERY [ ETAC (REPEAT MDISCH_TAC THEN REWRITE_TAC[NEG_CLAUSES]); 
	                                           ruleseq Cll.ll_with; seqassumption]))
                      
                      
    let ll_with_buf_left1 = rprove ( `?R .
                                     (_OPER_ (' (NEG A <> na) ^ ' ((B ++ C) <> a)) P) ===>
	                                   (_OPER_ (' (NEG B <> buf) ^ ' (B <> b)) Q) ===>
	                                   (_OPER_ (' (NEG (B ++ A) <> no) ^ ' ((B ++ C) <> a)) R)`,
                                         ( EEVERY [ ETAC (REPEAT MDISCH_TAC THEN REWRITE_TAC[NEG_CLAUSES]); 
	                                                ETHENL (ruleseq Cll.ll_with) [ruleseq Cll.ll_plus1 ; ALL_ETAC] ;
	                                                seqassumption]))
    
    let ll_with_buf_right1 = rprove ( `?R .
                                      (_OPER_ (' (NEG A <> na) ^ ' ((B ++ C) <> a)) P) ===>
	                                    (_OPER_ (' (NEG B <> buf) ^ ' (B <> b)) Q) ===>
	                                    (_OPER_ (' (NEG (A ++ B) <> no) ^ ' ((B ++ C) <> a)) R)`,
                                          (EEVERY [ ETAC (REPEAT MDISCH_TAC THEN REWRITE_TAC[NEG_CLAUSES]); 
	                                                ETHENL (ruleseq Cll.ll_with) [ALL_ETAC ; ruleseq Cll.ll_plus1] ;
	                                                seqassumption]))
    
    let ll_with_buf_left2 = rprove ( `?R .
                                     (_OPER_ (' (NEG A <> na) ^ ' ((B ++ C) <> a)) P) ===>
	                                   (_OPER_ (' (NEG C <> buf) ^ ' (C <> c)) Q) ===>
	                                   (_OPER_ (' (NEG (C ++ A) <> no) ^ ' ((B ++ C) <> a)) R)`,
                                         (EEVERY [ ETAC (REPEAT MDISCH_TAC THEN REWRITE_TAC[NEG_CLAUSES]); 
	                                               ETHENL (ruleseq Cll.ll_with) [ruleseq Cll.ll_plus2 ; ALL_ETAC] ;
	                                               seqassumption]))
    
    
    let ll_with_buf_right2 = rprove ( `?R .
                                      (_OPER_ (' (NEG A <> na) ^ ' ((B ++ C) <> a)) P) ===>
	                                    (_OPER_ (' (NEG C <> buf) ^ ' (C <> c)) Q) ===>
	                                    (_OPER_ (' (NEG (A ++ C) <> no) ^ ' ((B ++ C) <> a)) R)`,
                                          (EEVERY [ ETAC (REPEAT MDISCH_TAC THEN REWRITE_TAC[NEG_CLAUSES]); 
	                                                ETHENL (ruleseq Cll.ll_with) [ALL_ETAC ; ruleseq Cll.ll_plus2] ;
	                                                seqassumption]))
    
    
    (* The ll_with_outputs rule, enables the application of the ll_with rule on  *)
    (* two services with different outputs.                                      *)
    (* In the normal use of ll_with, the services must be identical apart from a *)
    (* single input (which gets combined). In this case, we allow the output to  *)
    (* also differ! Using the ll_plus rules we can make the two outputs match.   *)
    (* ------------------------------------------------------------------------- *)
    (* When using this rule you should at LEAST instantiate B.                   *)
    (* This is because there is no way to force B to be a positive literal and   *)
    (* thus may be matched to a NEG.                                             *)
      
    let ll_with_outputs = rprove ( `?R .
                                   (_OPER_ (G ^ ' (NEG A <> a) ^ ' (B <> b)) P) ===> 
	                                 (_OPER_ (G ^ ' (NEG C <> c) ^ ' (D <> d)) Q) ===>
	                                 (_OPER_ (G ^ ' (NEG (A ++ C) <> x) ^ ' ((B ++ D) <> y)) R)`,
                                       (EEVERY [ ETAC (REPEAT MDISCH_TAC THEN REWRITE_TAC[NEG_CLAUSES]); 
	                                             ETHENL (ruleseq Cll.ll_with) 
                                                   [ruleseq Cll.ll_plus1 ; ruleseq Cll.ll_plus2] ;
	                                             seqassumption]))
    
    (* ------------------------------------------------------------------------- *)
    (* Different version of the previous rule so that the second premise is the  *)
    (* major one, for use with drule.                                            *)
    (* ------------------------------------------------------------------------- *)
      
    let ll_with_outputs2 = rprove ( `?R .
                                    (_OPER_ (G ^ ' (NEG C <> c) ^ ' (D <> d)) Q) ===>
	                                  (_OPER_ (G ^ ' (NEG A <> a) ^ ' (B <> b)) P) ===> 
	                                  (_OPER_ (G ^ ' (NEG (A ++ C) <> x) ^ ' ((B ++ D) <> y)) R)`,
                                        (EEVERY [ ETAC (REPEAT MDISCH_TAC THEN REWRITE_TAC[NEG_CLAUSES]); 
	                                              ETHENL (ruleseq Cll.ll_with) 
                                                    [ruleseq Cll.ll_plus1 ; ruleseq Cll.ll_plus2] ;
	                                              seqassumption]))
    
    
    (* ------------------------------------------------------------------------- *)
    (* The ll_with_self rule enables the application of the ll_with rule on a    *)
    (* service with itself, joining two distinct intputs.                        *)
    (* ------------------------------------------------------------------------- *)
    (* WITH_TAC fails to deal with this particular case (most probably because   *)
    (* of channels clashing but need to debug further).                          *)
    (* The plan is to create a separate tactic using this rule just for this     *)
    (* case.                                                                     *)
    (* ------------------------------------------------------------------------- *)
    
    let ll_with_self = rprove ( `?R .
                                (_OPER_ (G ^ ' (NEG A <> a) ^ ' (NEG B <> b) ^ ' (C <> c)) P) ===>
	                              (_OPER_ (' ((NEG A) <> na) ^ ' (A <> aa)) Pa) ===>
	                              (_OPER_ (' ((NEG B) <> nb) ^ ' (B <> bb)) Pb) ===>
	                              (_OPER_ (G ^ ' (NEG (A ++ B) <> x) ^ ' (NEG A <> a) ^ ' (NEG B <> b) 
	                                        ^ ' (((C ** A) ++ (C ** B)) <> y)) R)`,
                                    (EEVERY [ ETAC (REPEAT MDISCH_TAC THEN REWRITE_TAC[NEG_CLAUSES]); 
	                                          ETHENL (ruleseq Cll.ll_with)
	                                            [ ETHEN (ruleseq Cll.ll_plus1)
	                                                (rule_seqtac 
	                                                   [(`G`,`G ^' (NEG B <> b)^' (NEG A <> a)`);(`B`,`A`)] 
                                                       ll_times_buf_right) ;
	                                              ETHEN (ruleseq Cll.ll_plus2)
	                                                (rule_seqtac 
	                                                   [(`G`,`G ^' (NEG A <> a)^' (NEG B <> b)`);(`B`,`B`)] 
                                                       ll_times_buf_right) ];
	                                          seqassumption]))


      
    (* ------------------------------------------------------------------------- *)
    (* The ll_filter_input/output rule enables a more "focused" application of   *)
    (* the cut rule to apply filters to an input/the output of a process         *)
    (* respectively.                                                             *)
    (* ------------------------------------------------------------------------- *)
			     
    let ll_filter_input = rprove ( `?R .
                                   (_OPER_ (' (NEG A <> a) ^ G) Q) ===>
	                                 (_OPER_ (' (NEG B <> b) ^ ' (A <> a)) P) ===> 
	                                 (_OPER_ (' (NEG B <> b) ^ G) R)`,
                                       (EEVERY [ ETAC (REPEAT MDISCH_TAC THEN REWRITE_TAC[NEG_CLAUSES]); 
	                                             rule_seqtac [`C:LinProp`,`A:LinProp`] Cll.ll_cut;
	                                             seqassumption]))
                                 
    let ll_filter_output = rprove ( `?R .
                                    (_OPER_ (G ^ ' (A <> a)) Q) ===>
	                                  (_OPER_ (' (NEG A <> a) ^ ' (B <> b)) P) ===> 
	                                  (_OPER_ (G ^ ' (B <> b)) R)`,
                                        (EEVERY [ ETAC (REPEAT MDISCH_TAC THEN REWRITE_TAC[NEG_CLAUSES]); 
	                                              rule_seqtac [`C:LinProp`,`A:LinProp`] Cll.ll_cut;
	                                              seqassumption]))
                                  
  end;;

(*

g `|-- (G^' (NEG A <> a)^' (NEG B <> b)) P ===>
  |-- (G^' (NEG (A ** B) <> z)) (In z [a; b] P)`;;
`?R x y .(|-- ( ' (NEG (A ** B) <> ab) ^ ' (NEG C <> c) ^ ' ((A ** D) <> d)) P) ===> 
  (|-- ( ' (NEG E <> e) ^ ' (NEG C <> c) ^ ' ((C ** E) <> f)) Q) ===>
 (|-- (' (NEG ((A ** B) ++ E) <> x) ^ ' (NEG C <> c) ^ ' (((A ** D) ++ (C ** E)) <> y)) R)`;;
e (REPEAT META_EXISTS_TAC);;
e MIMP_TAC;;
e (REPEAT DISCH_TAC);;

g `(|-- (G ^ ' (NEG A <> a) ^ ' (B <> b)) P) ===> 
  (|-- (G ^ ' (NEG C <> c) ^ ' (D <> d)) Q) ===>
 (|-- (G ^ ' (NEG (A ++ C) <> x) ^ ' ((B ++ D) <> y)) (
  Res [u; v]
   (Out x [u; v]
   (Plus (In u [a] (Res [b] (In y [up; vp] (Out up [b] P))))
   (In v [c] (Res [d] (In y [uq; vq] (Out vq [d] Q))))))
))`;;

e MIMP_TAC;;
e (REPEAT DISCH_TAC);;
e (REWRITE_TAC[NEG_CLAUSES]);;


*)
