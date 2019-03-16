(* ========================================================================= *)
(* Useful properties and corresponding processes using the                   *) 
(* proofs-as-processes paradigm.                                             *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2010-2011                                 *)
(* ========================================================================= *)
(* TODO TODO *)

(* Dependency *)

needs (!serv_dir ^ "pap/PaP.ml");;
needs (!serv_dir ^ "CLL/CLL_prover.ml");;
needs (!serv_dir ^ "services.ml");;

let LL_FILTER_CUT_TAC thm =
  MIMP_TAC THEN REPEAT DISCH_TAC 
    THEN llcut thm
    THENL [ llrule thm ; llassumption ] 
    THEN llassumption;;

(* ========================================================================= *)

(* TIMES *)

let TIMES_COMM_PROC = new_definition 
  `Comm (A,B,x,y,na,aa,nb,bb,Pa,Pb) = 
  ParProc (NEG A) (NEG B) x na nb (TimesProc B A y bb aa Pb Pa)`;;


let TIMES_COMM = prove ( 
  `(|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' (NEG (A ** B) <> x) ^ ' ((B ** A) <> y)) 
    (Comm(A,B,x,y,na,aa,nb,bb,Pa,Pb)))`,
  MIMP_TAC THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC[NEG_TIMES;TIMES_COMM_PROC] THEN 
    llrule ll_par THEN 
    llrule_tac [`G`,`' (NEG B <> nb)`] ll_times
    THEN llassumption);;

let lltimes_comm = prove(
  `(|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (G ^ ' ((A ** B) <> x)) P) ===> 
  (|-- (G ^ ' ((B ** A) <> y)) 
      (CutProc (A ** B) z x' x (Comm (A,B,x',y,na,aa,nb,bb,Pa,Pb)) P)
  )`, 
  LL_FILTER_CUT_TAC TIMES_COMM);;


let TIMES_ASSOC_PROC = new_definition 
  `Assoc (A,B,C,x,x',y,y',na,aa,nb,bb,nc,cc,Pa,Pb,Pc) = 
  ParProc (NEG A % NEG B) (NEG C) x x' nc
    (ParProc (NEG A) (NEG B) x' na nb
       (TimesProc A (B ** C) y aa y' Pa (TimesProc B C y' bb cc Pb Pc)))`;;


let TIMES_ASSOC = prove(
  `(|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  (|-- (' ((NEG ((A ** B) ** C)) <> x) ^ ' ((A ** B ** C) <> y)) 
      (Assoc (A,B,C,x,x',y,y',na,aa,nb,bb,nc,cc,Pa,Pb,Pc))
  )`,
  MIMP_TAC THEN REPEAT DISCH_TAC THEN
    PURE_REWRITE_TAC[NEG_TIMES;TIMES_ASSOC_PROC] THEN
    llrule ll_par THEN llrule ll_par THEN
    llrule_tac [`G`,`' (NEG A <> na)`] ll_times THENL
    [ llassumption ; 
      llrule_tac [`G`,`' (NEG B <> nb)`] ll_times ]
    THEN llassumption);;

let lltimes_assoc = prove(
  `(|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  (|-- (G ^ ' (((A ** B) ** C) <> x)) P) ===> 
  (|-- (G ^ ' ((A ** (B ** C)) <> y)) 
(CutProc ((A ** B) ** C) z fin x
   (Assoc (A,B,C,fin,fin',y,y',na,aa,nb,bb,nc,cc,Pa,Pb,Pc))
   P))`,
  LL_FILTER_CUT_TAC TIMES_ASSOC);;
  

(* ========================================================================= *)

(* PAR *)

let ll_par_inv = prove(
  `(|-- (' ((NEG A) <> na) ^ ' (A <> a) ) Pa) ===>
    (|-- (' ((NEG B) <> nb) ^ ' (B <> b) ) Pb) ===>
    (|-- (G ^ ' ((A % B) <> y)) P) ===>
    (|-- (G ^ ' (A <> a) ^ '(B <> b)) 
	(CutProc (NEG A ** NEG B) z y fout P
	   (TimesProc (NEG A) (NEG B) fout na nb Pa Pb))
    )`,
  MIMP_TAC THEN REPEAT DISCH_TAC THEN 
    llrule_tac [(`C`,`NEG A ** NEG B`);
		(`D`,`G`)] ll_cut
    THENL [ REWRITE_TAC[NEG_TIMES;NEG_NEG] ; llrule ll_times ]
    THEN llassumption);;

(* ========================================================================= *)

(* PLUS *)

let PLUS_COMM_PROC = new_definition 
  `PlusComm (A,B,x,y,na,aa,nb,bb,u,v,ua,va,ub,vb,Pa,Pb) =
  WithProc (NEG A) (NEG B) x na nb u v 
    (PlusRProc B A y aa ua va Pa)
    (PlusLProc B A y bb ub vb Pb)`;;

let PLUS_COMM = prove (
  `(|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
    (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
    (|-- (' (NEG (A ++ B) <> x) ^ ' ((B ++ A) <> y)) 
	(PlusComm (A,B,x,y,na,aa,nb,bb,u,v,ua,va,ub,vb,Pa,Pb))
    )`,
  MIMP_TAC THEN REPEAT DISCH_TAC
    THEN PURE_REWRITE_TAC[NEG_PLUS;PLUS_COMM_PROC]
    THEN llrule ll_with 
    THENL [ llrule ll_plus2 ; llrule ll_plus1 ]
    THEN llassumption);;

let llplus_comm = prove(
  `(|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
    (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
    (|-- (G ^ ' ((A ++ B) <> x)) P) ===> 
    (|-- (G ^ ' ((B ++ A) <> y)) 
	(CutProc (A ++ B) z fin x
	   (PlusComm (A,B,fin,y,na,aa,nb,bb,u,v,ua,va,ub,vb,Pa,Pb))
	   P))`,
  LL_FILTER_CUT_TAC PLUS_COMM);;


let PLUS_ASSOC_PROC = new_definition 
  `PlusAssoc (A,B,C,x,y,na,aa,nb,bb,nc,cc,nab,u,v,uab,vab,ua,va,ub,vb,uc,vc,ul,vl,yl,ur,vr,yr,Pa,Pb,Pc) =
  (WithProc (NEG A & NEG B) (NEG C) x nab nc u v
     (WithProc (NEG A) (NEG B) nab na nb uab vab
	(PlusLProc A (B ++ C) y aa ua va Pa)
	(PlusRProc A (B ++ C) y yl ul vl (PlusLProc B C yl bb ub vb Pb)))
     (PlusRProc A (B ++ C) y yr ur vr (PlusRProc B C yr cc uc vc Pc)))`;;


let PLUS_ASSOC = prove(
  `(|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
    (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
    (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
    (|-- (' ((NEG ((A ++ B) ++ C)) <> x) ^ ' ((A ++ B ++ C) <> y))
	(PlusAssoc (A,B,C,x,y,na,aa,nb,bb,nc,cc,nab,u,v,uab,vab,ua,va,ub,vb,uc,vc,ul,vl,yl,ur,vr,yr,Pa,Pb,Pc))
    )`,
  MIMP_TAC THEN REPEAT DISCH_TAC THEN 
    REWRITE_TAC[NEG_PLUS;PLUS_ASSOC_PROC] THEN llrule ll_with 
    THENL [ llrule ll_with ; 
	    llrule ll_plus2 THEN llrule ll_plus2 THEN llassumption ]
    THENL [ llrule ll_plus1 THEN llassumption ; 
	    llrule ll_plus2 THEN llrule ll_plus1 THEN llassumption ]);;

let llplus_assoc = prove(
  `(|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  (|-- (G ^ ' (((A ++ B) ++ C) <> x)) P) ===> 
  (|-- (G ^ ' ((A ++ B ++ C) <> y)) 
      (CutProc ((A ++ B) ++ C) z fin x
	 (PlusAssoc (A,B,C,fin,y,na,aa,nb,bb,nc,cc,nab,u,v,uab,vab,ua,va,ub,vb,uc,vc,ul,vl,yl,ur,vr,yr,Pa,Pb,Pc))
	 P))`,
  LL_FILTER_CUT_TAC PLUS_ASSOC);;


let PLUS_IDEMPOT_PROC = new_definition 
  `PlusIdempot (A,na,aa,u,v,Pa) = WithProc (NEG A) (NEG A) aa na na u v Pa Pa`;;

let PLUS_IDEMPOT = prove (
  `(|-- (' ((NEG A) <> na) ^ ' (A <> a) ) Pa) ===> 
    (|-- (' (NEG (A ++ A) <> aa) ^ ' (A <> a)) 
	(PlusIdempot (A,na,aa,u,v,Pa)))`,
  MIMP_TAC THEN DISCH_TAC THEN REWRITE_TAC[PLUS_IDEMPOT_PROC;NEG_CLAUSES]
    THEN llrule ll_with THEN llassumption);;


let llplus_idempot = prove (
  `(|-- (' ((NEG A) <> na) ^ ' (A <> a) ) Pa) ===> 
    (|-- (' ((A ++ A) <> aa)) P) ===> 
    (|-- (' (A <> a)) 
	(CutProc (A ++ A) z fin aa (PlusIdempot (A,na,fin,u,v,Pa)) P)
    )`,
  LL_FILTER_CUT_TAC PLUS_IDEMPOT);;


(* ========================================================================= *)

(* DISTRIBUTIVITY *)
(* This needs to be redone. *)

(*
let llleft_times_plus_distrib = prove(
  `(|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  (|-- (G ^ ' ((A ** (B ++ C)) <> x)) P) ===> 
  (|-- (G ^ ' (((A ** B) ++ (A ** C)) <> y)) 
    (Res [z] (
     Comp (SUBN1 P (x,z)) (
     SUBN1 (
     In yy [na; yb] (
     Res [uc; vc] (
     Out yb [uc; vc] (
     Plus (
     In uc [nb] ( 
     Res [xd] (
     In y [ud; vd] (
     Out ud [xd] (Res [aa; bb] (Out xd [aa; bb] (Comp Pa Pb))))))) (
     In vc [nc] (
     Res [ye] (
     In y [ue; ve] (
     Out ve [ye] (Res [aa; cc] (Out ye [aa; cc] (Comp Pa Pc)))))))))))
       (yy,z)))
    ))`, 
  MIMP_TAC THEN REPEAT DISCH_TAC THEN llrule_tac [(`C`,`(A ** (B ++ C))`)] ll_cut
    THENL [ REWRITE_TAC[NEG_PLUS;NEG_TIMES] ; llassumption] THEN llrule ll_par
    THEN llrule ll_with THENL [ llrule ll_plus1 ; llrule ll_plus2 ] THEN 
    llrule ll_times THEN llassumption);;


let llright_times_plus_distrib = prove(
  `(|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  (|-- (G ^ ' (((A ++ B) ** C) <> x)) P) ===> 
  (|-- (G ^ ' (((A ** C) ++ (B ** C)) <> y)) 
    (Res [z] (
     Comp (SUBN1 P (x,z)) (
     SUBN1 (
     In yy [xb; nc] (
     Res [uc; vc] (
     Out xb [uc; vc] (
     Plus (
     In uc [na] (
     Res [xd] (
     In y [ud; vd] (
     Out ud [xd] (Res [aa; cc] (Out xd [aa; cc] (Comp Pa Pc))))))) (
     In vc [nb] (
     Res [ye] (
     In y [ue; ve] (
     Out ve [ye] (Res [bb; cc] (Out ye [bb; cc] (Comp Pb Pc)))))))))))
       (yy,z)))
    ))`, MIMP_TAC THEN REPEAT DISCH_TAC THEN llrule_tac [(`C`,`((A ++ B) ** C)`)] ll_cut THENL
    [ REWRITE_TAC[NEG_PLUS;NEG_TIMES] ; llassumption ] THEN llrule ll_par THEN
    llrule ll_with THENL [ llrule ll_plus1 ; llrule ll_plus2 ] THENL 
    [ llrule_tac [`G`,`' ((NEG A) <> na)`] ll_times ;
      llrule_tac [`G`,`' ((NEG B) <> nb)`] ll_times ] THEN llassumption);;


let RIGHT_TIMES_PLUS_DISTRIB_PLUS = prove(
  `(|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  (|-- (' ((NEG D) <> nd) ^ ' (D <> dd) ) Pd) ===>
  (|-- (' ((((B ** A) ++ (C ** A) ++ D) <> x)) ^ ' ((NEG (((B ++ C) ** A) ++ D) <> y))) (
  Res [ua; va]
    (Out y [ua; va] (
     Plus (
     In ua [xa] (
     In xa [xb; na] (
     Res [uc; vc] (
     Out xb [uc; vc] (
     Plus (
     In uc [nb] (
     Res [xd] (
     In x [ud; vd] ( 
     Out ud [xd] (Res [bb; aa] (Out xd [bb; aa] (Comp Pb Pa))))))) (
     In vc [nc] (
     Res [ye] (
     In x [ue; ve] ( 
     Out ve [ye] ( 
     Res [xf] (
     In ye [uf; vf] ( 
     Out uf [xf] (
     Res [cc; aa] (Out xf [cc; aa] (Comp Pc Pa))))))))))))))) (
     In va [nd] (
     Res [yg] (
     In x [ug; vg] (
     Out vg [yg] (Res [dd] (In yg [uh; vh] (Out vh [dd] Pd)))))))))))
    `,
  MIMP_TAC THEN REPEAT DISCH_TAC THEN 
    REWRITE_TAC[NEG_PLUS;NEG_TIMES] THEN
    llrule ll_with 
    THENL [ llrule ll_par THEN llrule ll_with ; 
	    llrule ll_plus2 THEN llrule ll_plus2 THEN llassumption ]
    THENL [ llrule ll_plus1 ; llrule ll_plus2 THEN llrule ll_plus1 ]
    THENL [ llrule_tac [`G`,`' (NEG B <> nb)`] ll_times ;
	    llrule_tac [`G`,`' (NEG C <> nc)`] ll_times ] THEN llassumption);;




let llright_times_plus_distrib_plus = prove(
  `(|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  (|-- (' ((NEG D) <> nd) ^ ' (D <> dd) ) Pd) ===>
  (|-- (G ^ ' ((((B ++ C) ** A) ++ D) <> y)) P) ===> 
  (|-- (G ^ ' (((B ** A) ++ (C ** A) ++ D) <> x)) 
    (Res [z] (
     Comp ( SUBN1 P (y,z) ) (
     SUBN1 ( 
     Res [ua; va] ( 
     Out yy [ua; va] (
     Plus ( 
     In ua [xa] ( 
     In xa [xb; na] ( 
     Res [uc; vc] ( 
     Out xb [uc; vc] (
     Plus (
     In uc [nb] (
     Res [xd] (
     In x [ud; vd] (
     Out ud [xd] (Res [bb; aa] (Out xd [bb; aa] (Comp Pb Pa))))))) (
     In vc [nc] (
     Res [ye] (
     In x [ue; ve] (
     Out ve [ye] (
     Res [xf] (
     In ye [uf; vf] (
     Out uf [xf] (Res [cc; aa] (Out xf [cc; aa] (Comp Pc Pa))))))))))))))) (
     In va [nd] (
     Res [yg] (
     In x [ug; vg] (
     Out vg [yg] (Res [dd] (In yg [uh; vh] (Out vh [dd] Pd))))))))))
       (yy,z)))
    ))`,
  MIMP_TAC THEN REPEAT DISCH_TAC THEN 
    llcut RIGHT_TIMES_PLUS_DISTRIB_PLUS THENL 
    [ llrule RIGHT_TIMES_PLUS_DISTRIB_PLUS ; llassumption ] 
    THEN llassumption);;
*)
