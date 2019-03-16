(* ========================================================================= *)
(* Construction site for useful properties and corresponding processes       *)
(* using the proofs-as-processes paradigm.                                   *)
(* ------------------------------------------------------------------------- *)
(* Processes for various CLL theorems are constructed here. Then these       *)
(* theorems are transfered to procs.ml with their processes instantiated.    *)
(* Proofs with instantiated processes are cleaner (no metavariables, no      *)
(* meta-assumptions and so on) so this helps keep procs.ml nice and clean.   *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                    2011                                   *)
(* ========================================================================= *)

(* Dependency *)

needs (!serv_dir ^ "pap/PaP.ml");;
needs (!serv_dir ^ "CLL/CLL_prover.ml");;

gll `! A B. ?P. (|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' (NEG (A ** B) <> x) ^ ' ((B ** A) <> y)) P)`;;
ell GEN_ALL_TAC;;
ell (META_EXISTS_TAC);;
ell MIMP_TAC;;
ell (REPEAT DISCH_TAC);;
ell (REWRITE_TAC[NEG_TIMES]);;
ell (llrule ll_par);;
ell (llrule_tac [`G`,`' (NEG B <> y0)`] ll_times);;
ellma ();;
ellma ();;

top_thm();;
p();;
hd it;;
fst3 it;;
instantiate (snd it) `P:(num)Agent`;;

gll `! A B. (|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' (NEG (A ** B) <> x) ^ ' ((B ** A) <> y)) (ParProc (NEG A) (NEG B) x na nb (TimesProc B A y bb aa Pb Pa)))`;;

e (llrule_tac [`G`,`' (NEG B <> nb)`] ll_times);;
ellma ();;
ellma ();;


gll `! G A B. ?Q y.
  (|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (G ^ ' ((A ** B) <> x)) P) ===> 
  (|-- (G ^ ' ((B ** A) <> y)) Q)`;;
e GEN_ALL_TAC;;
e (REPEAT META_EXISTS_TAC);;
e MIMP_TAC;;
e (REPEAT DISCH_TAC);;
ell (llcut TIMES_COMM);;
ell (llrule TIMES_COMM);;
ellma ();;
ellma ();;
ellma ();;

top_thm();;
instantiate ((snd o fst3 o hd o p) ()) `Q:(num)Agent`;;



g `! A B C. ?P x y. (|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  (|-- (' ((NEG ((A ** B) ** C)) <> x) ^ ' ((A ** B ** C) <> y)) P)`;;
e GEN_ALL_TAC;;
e (REPEAT META_EXISTS_TAC);;
e (MIMP_TAC THEN REPEAT DISCH_TAC);;
e (PURE_REWRITE_TAC[NEG_TIMES]);;
e (llrule ll_par);;
e (llrule ll_par);;
e (llrule_tac [(`G`,`' (NEG A <> x1)`)] ll_times);;
ellma ();;
e (llrule_tac [(`G`,`' (NEG B <> y1)`)] ll_times);;
ellma();;
ellma();;
top_thm();;
instantiate (top_inst (p())) `P:(num)Agent`;;

g `! A B C. ?Q y. (|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  (|-- (G ^ ' (((A ** B) ** C) <> x)) P) ===> 
  (|-- (G ^ ' ((A ** (B ** C)) <> y)) Q)`;;
e GEN_ALL_TAC;;
e (REPEAT META_EXISTS_TAC);;
e (MIMP_TAC THEN REPEAT DISCH_TAC);;
e (llcut TIMES_ASSOC);;
e (llrule TIMES_ASSOC);;
ellma ();;
ellma ();;
ellma ();;
ellma ();;
top_thm();;
instantiate (top_inst (p())) `Q:(num)Agent`;;


(* PAR ELIMINATION = NEW = *)



g `?P Q xa xb y. (|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (G ^ ' ((A % B) <> y)) P) ===>
  (|-- (G ^ ' (A <> xa) ^ '(B <> xb)) Q)`;;
e (REPEAT META_EXISTS_TAC);;

e MIMP_TAC;;
e (REPEAT DISCH_TAC);;
e (llrule_tac [(`C`,`NEG A ** NEG B`);(`D`,`G`)] ll_cut);;

e (REWRITE_TAC[NEG_TIMES;NEG_NEG]);;
ellma ();;

e (llrule ll_times);;
ellma ();;
ellma ();;

top_thm();;
instantiate (top_inst (p())) `Q:(num)Agent`;;


g `?P Q. 
  (|-- (G ^ ' ((A % B) <> x)) P) ===>
  (|-- (G ^ ' (A <> xa) ^ '(B <> xb)) Q)`;;
e (REPEAT META_EXISTS_TAC);;

e MIMP_TAC;;
e (REPEAT DISCH_TAC);;
e (llrule_tac [(`C`,`NEG A ** NEG B`);(`D`,`G`)] ll_cut);;

e (REWRITE_TAC[NEG_TIMES;NEG_NEG]);;
ellma ();;

e (llrule ll_times);;
e (llrule ll_id);;
e (llrule ll_id);;

top_thm();;


p();;
hd it;;
fst3 it;;
let qqinst = snd it;;
instantiate qqinst `Q:(num)Agent`;;


(* PLUS IDEMPOT *)

g `? P . (|-- (' ((NEG A) <> na) ^ ' (A <> a) ) Pa) ===> 
    (|-- (' (NEG (A ++ A) <> aa) ^ ' (A <> a)) P)`;;
e (REPEAT META_EXISTS_TAC);;
e (MIMP_TAC THEN DISCH_TAC THEN REWRITE_TAC[NEG_CLAUSES]);;
e (llrule ll_with);;
ellma();;
ellma();;
top_thm();;
instantiate (top_inst (p())) `P:NAgent`;;

g `? Q a . (|-- (' ((NEG A) <> na) ^ ' (A <> a) ) Pa) ===> 
    (|-- (' ((A ++ A) <> aa)) P) ===> 
    (|-- (' (A <> a)) Q)`;;
e (REPEAT META_EXISTS_TAC);;
e (MIMP_TAC THEN REPEAT DISCH_TAC);;
e (llcut PLUS_IDEMPOT);;
e (llrule PLUS_IDEMPOT);;
ellma();;
ellma();;
top_thm();;
instantiate (top_inst (p())) `Q:NAgent`;;



(* TIMES ASSOC *)


 g `?P x y. ! A B C. (|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
|-- (' ((NEG ((A ** B) ** C)) <> x) ^ ' ((A ** B ** C) <> y)) P`;;
e (REPEAT META_EXISTS_TAC);;

e GEN_ALL_TAC;;
e MIMP_TAC;;
e (REPEAT DISCH_TAC);;
e (PURE_REWRITE_TAC[NEG_TIMES]);;
e (llrule (number_vars_thm 1 ll_par));;
e (llrule (number_vars_thm 2 ll_par));;
e (llrule_tac [`G3`,`' (NEG A <> x2)`] (number_vars_thm 3 ll_times));;
ellma ();;
(* e (llrule_tac [(`A4`,`A`)] (number_vars_thm 4 ll_id));; *)
e (llrule_tac [`G5`,`' (NEG B <> y2)`] (number_vars_thm 5 ll_times));;
ellma ();;
ellma ();;
(*
e (llrule_tac [(`A7`,`B`)] (number_vars_thm 7 ll_id));;
e (llrule_tac [(`A10`,`C`)] (number_vars_thm 10 ll_id));;
*)

top_thm();;
p();;
hd it;;
fst3 it;;
instantiate (snd it) `P:(num)Agent`;;



g `?Q y. (|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  (|-- (G ^ ' (((A ** B) ** C) <> x)) P) ===> 
  (|-- (G ^ ' ((A ** (B ** C)) <> y)) Q)`;;
e (REPEAT META_EXISTS_TAC);;
e GEN_ALL_TAC;;
e MIMP_TAC;;
e (REPEAT DISCH_TAC);;
e (llcut (number_vars_thm 1 TIMES_ASSOC));;
e (llrule (number_vars_thm 2 TIMES_ASSOC));;
ellma();;
ellma();;
ellma();;
ellma();;
top_thm();;
p();;
hd it;;
fst3 it;;
instantiate (snd it) `Q:(num)Agent`;;


(* 
Is there an altenative proof without the lemma?
We need forward chaining tactics to find out!
 *)


b();;


(* PLUS COMM *)


g `?P x y. (|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' (NEG (A ++ B) <> x) ^ ' ((B ++ A) <> y)) P)`;;
e (REPEAT META_EXISTS_TAC THEN MIMP_TAC THEN REPEAT DISCH_TAC);;
e (PURE_REWRITE_TAC[NEG_PLUS]);;
e (llrule ll_with);;
e (llrule ll_plus2);;
ellma();;
e (llrule ll_plus1);;
ellma();;
top_thm();;

instantiate (top_inst (p())) `P:(num)Agent`;;


(* PLUS ASSOC *)

g  `? P . (|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  ( |-- (' ((NEG ((A ++ B) ++ C)) <> x) ^ ' ((A ++ B ++ C) <> y)) P)`;;
e (REPEAT META_EXISTS_TAC THEN MIMP_TAC THEN REPEAT DISCH_TAC);;
e (PURE_REWRITE_TAC[NEG_PLUS]);;
e (llrule ll_with);;
e (llrule ll_with);;

e (llrule ll_plus1);;
ellma();;

e (llrule ll_plus2);;
e (llrule ll_plus1);;
ellma();;

e (llrule ll_plus2);;
e (llrule ll_plus2);;
ellma();;

top_thm();;

instantiate (top_inst (p())) `P:(num)Agent`;;

(*
  (Res [ua; va]
       (Out x [ua; va]
	  (Plus
	     (In ua [xa]
		(Res [ub; vb]
		   (Out xa [ub; vb]
		      (Plus
			 (In ub [na]
			    (Res [aa]
			       (In y [uc; vc] 
				  (Out uc [aa] Pa))))
			 (In vb [nb]
			    (Res [ye]
			       (In y [ue; ve]
				  (Out ve [ye]
				     (Res [bb]
					(In ye [uf; vf] 
					   (Out uf [bb] Pb
					   )))))))))))
	     (In va [nc]
		(Res [yh]
		   (In y [uh; vh]
		      (Out vh [yh]
			 (Res [cc]
			    (In yh [ui; vi] 
			       (Out vi [cc] Pc
			       ))))))))))`,
*)
g `?P Q x y. (|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  (|-- (' ((A ** (B ++ C)) <> x)) P) ===> 
  (|-- (' (((A ** B) ++ (A ** C)) <> y)) Q)`;;
e (REPEAT META_EXISTS_TAC);;

e (GEN_ALL_TAC);;
e (MIMP_TAC);;

e (REPEAT DISCH_TAC);;
e (llrule_tac [(`C1`,`(A ** (B ++ C))`)] (number_vars_thm 1 ll_cut));;
e (llmeta_assumption [`(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`; `(x:num)`; `(y:num)`]);;
e (REWRITE_TAC[NEG_PLUS;NEG_TIMES]);;
e (llrule (number_vars_thm 2 ll_par));;
e (llrule (number_vars_thm 3 ll_with));;

e (llrule (number_vars_thm 4 ll_plus1));;
e (llrule (number_vars_thm 5 ll_times));;
e (llmeta_assumption [`(x5:num)`; `(P5:(num)Agent)`; `(y5:num)`; `(Q5:(num)Agent)`; `(x4:num)`; `(P4:(num)Agent)`; `(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(y2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`; `(x:num)`; `(y:num)`]);;
e (llmeta_assumption [`(x5:num)`; `(P5:(num)Agent)`; `(y5:num)`; `(Q5:(num)Agent)`; `(x4:num)`; `(P4:(num)Agent)`; `(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(y2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`; `(x:num)`; `(y:num)`]);;

e (llrule (number_vars_thm 8 ll_plus2));;
e (llrule (number_vars_thm 9 ll_times));;

e (llmeta_assumption [`(x9:num)`; `(P9:(num)Agent)`; `(y9:num)`; `(Q9:(num)Agent)`; `(y8:num)`; `(P8:(num)Agent)`; `(x5:num)`; `(P5:(num)Agent)`; `(y5:num)`; `(Q5:(num)Agent)`; `(x4:num)`; `(P4:(num)Agent)`; `(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(y2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`; `(x:num)`; `(y:num)`]);;
e (llmeta_assumption [`(x9:num)`; `(P9:(num)Agent)`; `(y9:num)`; `(Q9:(num)Agent)`; `(y8:num)`; `(P8:(num)Agent)`; `(x5:num)`; `(P5:(num)Agent)`; `(y5:num)`; `(Q5:(num)Agent)`; `(x4:num)`; `(P4:(num)Agent)`; `(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(y2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`; `(x:num)`; `(y:num)`]);;

p();;
hd it;;
fst3 it;;
map (instantiate (snd it)) (fst it);;





g `?P Q x y. (|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  (|-- (' (((A ++ B) ** C) <> x)) P) ===> 
  (|-- (' (((A ** C) ++ (B ** C)) <> y)) Q)`;;
e (REPEAT META_EXISTS_TAC);;

e (GEN_ALL_TAC);;
e (MIMP_TAC);;

e (REPEAT DISCH_TAC);;
e (llrule_tac [(`C1`,`((A ++ B) ** C)`)] (number_vars_thm 1 ll_cut));;
e (llmeta_assumption [`(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`; `(x:num)`; `(y:num)`]);;
e (REWRITE_TAC[NEG_PLUS;NEG_TIMES]);;
e (llrule (number_vars_thm 2 ll_par));;
e (llrule (number_vars_thm 3 ll_with));;

e (llrule (number_vars_thm 4 ll_plus1));;
e (llrule_tac [`G5`,`' ((NEG A) <> x3)`] (number_vars_thm 5 ll_times));;

e (llmeta_assumption [`(x5:num)`; `(P5:(num)Agent)`; `(y5:num)`; `(Q5:(num)Agent)`; `(x4:num)`; `(P4:(num)Agent)`; `(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(y2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`; `(x:num)`; `(y:num)`]);;
e (llmeta_assumption [`(x5:num)`; `(P5:(num)Agent)`; `(y5:num)`; `(Q5:(num)Agent)`; `(x4:num)`; `(P4:(num)Agent)`; `(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(y2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`; `(x:num)`; `(y:num)`]);;

e (llrule (number_vars_thm 8 ll_plus2));;
e (llrule_tac [`G9`,`' ((NEG B) <> y3)`] (number_vars_thm 9 ll_times));;

e (llmeta_assumption [`(x9:num)`; `(P9:(num)Agent)`; `(y9:num)`; `(Q9:(num)Agent)`; `(y8:num)`; `(P8:(num)Agent)`; `(x5:num)`; `(P5:(num)Agent)`; `(y5:num)`; `(Q5:(num)Agent)`; `(x4:num)`; `(P4:(num)Agent)`; `(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(y2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`; `(x:num)`; `(y:num)`]);;
e (llmeta_assumption [`(x9:num)`; `(P9:(num)Agent)`; `(y9:num)`; `(Q9:(num)Agent)`; `(y8:num)`; `(P8:(num)Agent)`; `(x5:num)`; `(P5:(num)Agent)`; `(y5:num)`; `(Q5:(num)Agent)`; `(x4:num)`; `(P4:(num)Agent)`; `(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(y2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`; `(x:num)`; `(y:num)`]);;

p();;
hd it;;
fst3 it;;
map (instantiate (snd it)) (fst it);;



(*
let myres2 = `Res [z1]
    (Comp
     (
      (Res [z2]
      (Comp ((Res [wc; ro] (Out x2 [wc; ro] (Comp W R))))
      (
       (In z2 [xx2; yy2]
       (Res [ab2; ac2]
       (Out yy2 [ab2; ac2]
       (Plus
        (In ab2 [xxx2]
        (Res [ab'2]
        (In z1 [acc2; ign2]
        (Out acc2 [ab'2]
        (Res [a2; b2]
        (Out ab'2 [a2; b2]
        (Comp (In xx2 [bufa2] (Out a2 [bufa2] Zero))
        (In xxx2 [bufb2] (Out b2 [bufb2] Zero)))))))))
       (In ac2 [yyy2]
       (Res [ac'2]
       (In z1 [ign'2; acc'2]
       (Out acc'2 [ac'2]
       (Res [a'2; c2]
       (Out ac'2 [a'2; c2]
       (Comp (In xx2 [bufc2] (Out a'2 [bufc2] Zero))
       (In yyy2 [bufd2] (Out c2 [bufd2] Zero)))))))))))))
      )))
     )
    ((Res [u4; v4]
     (Out z1 [u4; v4]
     (Plus
      (In u4 [x4]
      (Res [sd] (In t [u5; v5] (Out u5 [sd] (In x4 [sc; sa] S)))))
     (In v4 [y4]
     (Res [y7] (In t [u7; v7] (Out v7 [y7] (In y4 [a8] (Out y7 [a8] Zero)))))))))
    )):(num)Agent`;;


let myres4 = `Res [z1]
   (Comp
    (
     (Res [z2]
     (Comp ((Res [wc; ro] (Out z2 [wc; ro] (Comp W R))))
     (
      (In z2 [xx2; yy2]
      (Res [ab2; ac2]
      (Out yy2 [ab2; ac2]
      (Plus
       (In ab2 [xxx2]
       (Res [ab'2]
       (In z1 [acc2; ign2]
       (Out acc2 [ab'2]
       (Res [a2; b2]
       (Out ab'2 [a2; b2]
       (Comp (In xx2 [bufa2] (Out a2 [bufa2] Zero))
       (In xxx2 [bufb2] (Out b2 [bufb2] Zero)))))))))
      (In ac2 [yyy2]
      (Res [ac'2]
      (In z1 [ign'2; acc'2]
      (Out acc'2 [ac'2]
      (Res [a'2; c2]
      (Out ac'2 [a'2; c2]
      (Comp (In xx2 [bufc2] (Out a'2 [bufc2] Zero))
      (In yyy2 [bufd2] (Out c2 [bufd2] Zero)))))))))))))
     )))
    )
   (
    (Res [u4; v4]
    (Out z1 [u4; v4]
    (Plus
     (In u4 [x4] (Res [sd] (In tt [u5; v5] (Out u5 [sd] (In x4 [sc; sa] S)))))
    (In v4 [y4]
    (Res [y7]
    (In tt [u7; v7]
    (Out v7 [y7]
    (In y4 [x8; y8]
    (Res [x9; y9]
    (Out y7 [x9; y9]
    (Comp (In x8 [a10] (Out x9 [a10] Zero))
    (In y8 [a11] (Out y9 [a11] Zero)))))))))))))
   )):(num)Agent`;;



g `?P Q x y. (|-- (' (((A % B) ++ (A % C)) <> x)) P) ==> (|-- ('((A % (B ++ C)) <> y)) Q)`;;
e (REPEAT META_EXISTS_TAC);;
e (REPEAT DISCH_TAC);;
e (llrule_tac [(`C1`,`((A % B) ++ (A % C))`)] (number_vars_thm 1 ll_cut));;
e (llmeta_assumption [`(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`; `(x:num)`; `(y:num)`]);;
e (REWRITE_TAC[NEG_PLUS;NEG_PAR]);;
e (llrule (number_vars_thm 2 ll_with));;
e (llrule (number_vars_thm 3 ll_par));;
e (llrule (number_vars_thm 4 ll_times));;
e (llrule (number_vars_thm 5 ll_id));;
e (llrule (number_vars_thm 6 ll_plus1));;
e (llrule_tac [`A7`,`B`] (number_vars_thm 7 ll_id));;
e (llrule (number_vars_thm 8 ll_par));;
e (llrule (number_vars_thm 9 ll_times));;
e (llrule (number_vars_thm 10 ll_id));;
e (llrule (number_vars_thm 11 ll_plus2));;
e (llrule_tac [`A12`,`C`] (number_vars_thm 12 ll_id));;
top_thm();;
p();;
hd it;;
fst3 it;;
map (instantiate (snd it)) (fst it);;

ll_with;;
ll_cut;;
b();;



   `Res [z1]
    (Comp (SUBN1 P1 (x1,z1))
    (Res [u2; v2]
     (Out z1 [u2; v2]
     (Plus
      (In u2 [x2]
      (In y [x3; y3]
      (Res [x4; y4]
      (Out x2 [x4; y4]
      (Comp (In x4 [a5] (Out x3 [a5] Zero))
      (Res [x6]
      (In y3 [u6; v6] (Out u6 [x6] (In y4 [a7] (Out x6 [a7] Zero))))))))))
     (In v2 [y2]
     (In y [x8; y8]
     (Res [x9; y9]
     (Out y2 [x9; y9]
     (Comp (In x9 [a10] (Out x8 [a10] Zero))
     (Res [y11]
     (In y8 [u11; v11] (Out v11 [y11] (In y9 [a12] (Out y11 [a12] Zero)))))))))))))
    )`

;;

*)

g `?P x y. ! A B C. |-- (' ((NEG ((A ++ B) ++ C)) <> x) ^ ' ((A ++ B ++ C) <> y)) P`;;
e (REPEAT META_EXISTS_TAC);;

e GEN_ALL_TAC;;
e (PURE_REWRITE_TAC[NEG_PLUS]);;
e (llrule (number_vars_thm 1 ll_with));;
e (llrule (number_vars_thm 2 ll_with));;
e (llrule (number_vars_thm 3 ll_plus1));;
e (llrule_tac [(`A4`,`A`)] (number_vars_thm 4 ll_id));;
e (llrule (number_vars_thm 5 ll_plus2));;
e (llrule (number_vars_thm 6 ll_plus1));;
e (llrule_tac [(`A7`,`B`)] (number_vars_thm 7 ll_id));;
e (llrule (number_vars_thm 8 ll_plus2));;
e (llrule (number_vars_thm 9 ll_plus2));;
e (llrule_tac [(`A10`,`C`)] (number_vars_thm 10 ll_id));;

top_thm();;
p();;
hd it;;
fst3 it;;
map (instantiate (snd it)) (fst it);;


g `?P Q . (|-- (G ^ ' (((A ++ B) ++ C) <> x)) P) ===> (|-- (G ^ ' ((A ++ B ++ C) <> y)) Q)`;;
e (REPEAT META_EXISTS_TAC);;

e MIMP_TAC;;
e DISCH_TAC;;
e (llcut (number_vars_thm 1 PLUS_ASSOC));;
e (llmeta_assumption [`(x':num)`; `(P':(num)Agent)`; `(x1:num)`; `(u11:num)`; `(xa1:num)`; `(ub1:num)`; `(vc1:num)`; `(uc1:num)`; `(xb1:num)`; `(xc1:num)`; `(ad1:num)`; `(vb1:num)`; `(ue1:num)`; `(ve1:num)`; `(ye1:num)`; `(vf1:num)`; `(uf1:num)`; `(yb1:num)`; `(xf1:num)`; `(bufb1:num)`; `(v11:num)`; `(uh1:num)`; `(vh1:num)`; `(yh1:num)`; `(ui1:num)`; `(vi1:num)`; `(ya1:num)`; `(yi1:num)`; `(bufc1:num)`; `(P:(num)Agent)`; `(Q:(num)Agent)`]);;
e (llrule PLUS_ASSOC);;

p();;
hd it;;
fst3 it;;
map (instantiate (snd it)) (fst it);;



g `?P. (|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  (|-- (' ((NEG D) <> nd) ^ ' (D <> dd) ) Pd) ===>
  (|-- (' ((((B ** A) ++ (C ** A) ++ D) <> x)) ^ ' ((NEG (((B ++ C) ** A) ++ D) <> y))) P)`;;
e (REPEAT META_EXISTS_TAC);;
e (MIMP_TAC);;
e (REPEAT DISCH_TAC);;

e (REWRITE_TAC[NEG_PLUS;NEG_TIMES]);;
e (llrule (number_vars_thm 1 ll_with));;
e (llrule (number_vars_thm 2 ll_par));;
e (llrule (number_vars_thm 3 ll_with));;

e (llrule (number_vars_thm 4 ll_plus1));;
e (llrule_tac [`G5`,`' (NEG B <> x3)`] (number_vars_thm 5 ll_times));;

e (llmeta_assumption [`(x5:num)`; `(P5:(num)Agent)`; `(y5:num)`; `(Q5:(num)Agent)`; `(x4:num)`; `(P4:(num)Agent)`; `(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(y2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`]);;
e (llmeta_assumption [`(x5:num)`; `(P5:(num)Agent)`; `(y5:num)`; `(Q5:(num)Agent)`; `(x4:num)`; `(P4:(num)Agent)`; `(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(y2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`]);;

e (llrule (number_vars_thm 8 ll_plus2));;
e (llrule (number_vars_thm 9 ll_plus1));;

e (llrule_tac [`G10`,`' (NEG C <> y3)`] (number_vars_thm 10 ll_times));;

e (llmeta_assumption [`(x10:num)`; `(P10:(num)Agent)`; `(y10:num)`; `(Q10:(num)Agent)`; `(x9:num)`; `(P9:(num)Agent)`; `(y8:num)`; `(P8:(num)Agent)`; `(x5:num)`; `(P5:(num)Agent)`; `(y5:num)`; `(Q5:(num)Agent)`; `(x4:num)`; `(P4:(num)Agent)`; `(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(y2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`]);;
e (llmeta_assumption [`(x10:num)`; `(P10:(num)Agent)`; `(y10:num)`; `(Q10:(num)Agent)`; `(x9:num)`; `(P9:(num)Agent)`; `(y8:num)`; `(P8:(num)Agent)`; `(x5:num)`; `(P5:(num)Agent)`; `(y5:num)`; `(Q5:(num)Agent)`; `(x4:num)`; `(P4:(num)Agent)`; `(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(y2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`]);;

e (llrule (number_vars_thm 13 ll_plus2));;
e (llrule (number_vars_thm 14 ll_plus2));;

e (llmeta_assumption [`(y14:num)`; `(P14:(num)Agent)`; `(y1:num)`]);;

p();;
hd it;;
fst3 it;;
map (instantiate (snd it)) (fst it);;



g `?P Q . (|-- (' ((NEG A) <> na) ^ ' (A <> aa) ) Pa) ===>
  (|-- (' ((NEG B) <> nb) ^ ' (B <> bb) ) Pb) ===>
  (|-- (' ((NEG C) <> nc) ^ ' (C <> cc) ) Pc) ===>
  (|-- (' ((NEG D) <> nd) ^ ' (D <> dd) ) Pd) ===>
  (|-- (G ^ ' ((((B ++ C) ** A) ++ D) <> y)) P) ===> 
  (|-- (G ^ ' (((B ** A) ++ (C ** A) ++ D) <> x)) Q)`;;
e (REPEAT META_EXISTS_TAC);;

e MIMP_TAC;;
e (REPEAT DISCH_TAC);;
e (llcut (number_vars_thm 1 RIGHT_TIMES_PLUS_DISTRIB_PLUS));;
e (llmeta_assumption [`(x':num)`; `(P':(num)Agent)`; `(y1:num)`; `(ua1:num)`; `(xa1:num)`; `(na1:num)`; `(xb1:num)`; `(uc1:num)`; `(nb1:num)`; `(vd1:num)`; `(ud1:num)`; `(xd1:num)`; `(bb1:num)`; `(Pb1:(num)Agent)`; `(vc1:num)`; `(nc1:num)`; `(ue1:num)`; `(ve1:num)`; `(ye1:num)`; `(vf1:num)`; `(uf1:num)`; `(xf1:num)`; `(cc1:num)`; `(aa1:num)`; `(Pc1:(num)Agent)`; `(Pa1:(num)Agent)`; `(va1:num)`; `(nd1:num)`; `(ug1:num)`; `(vg1:num)`; `(yg1:num)`; `(uh1:num)`; `(vh1:num)`; `(dd1:num)`; `(Pd1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`]);;
e (llrule  RIGHT_TIMES_PLUS_DISTRIB_PLUS);;
e (llmeta_assumption [`(x':num)`; `(P':(num)Agent)`; `(y1:num)`; `(ua1:num)`; `(xa1:num)`; `(na1:num)`; `(xb1:num)`; `(uc1:num)`; `(nb1:num)`; `(vd1:num)`; `(ud1:num)`; `(xd1:num)`; `(bb1:num)`; `(Pb1:(num)Agent)`; `(vc1:num)`; `(nc1:num)`; `(ue1:num)`; `(ve1:num)`; `(ye1:num)`; `(vf1:num)`; `(uf1:num)`; `(xf1:num)`; `(cc1:num)`; `(aa1:num)`; `(Pc1:(num)Agent)`; `(Pa1:(num)Agent)`; `(va1:num)`; `(nd1:num)`; `(ug1:num)`; `(vg1:num)`; `(yg1:num)`; `(uh1:num)`; `(vh1:num)`; `(dd1:num)`; `(Pd1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`]);;
e (llmeta_assumption [`(x':num)`; `(P':(num)Agent)`; `(y1:num)`; `(ua1:num)`; `(xa1:num)`; `(na1:num)`; `(xb1:num)`; `(uc1:num)`; `(nb1:num)`; `(vd1:num)`; `(ud1:num)`; `(xd1:num)`; `(bb1:num)`; `(Pb1:(num)Agent)`; `(vc1:num)`; `(nc1:num)`; `(ue1:num)`; `(ve1:num)`; `(ye1:num)`; `(vf1:num)`; `(uf1:num)`; `(xf1:num)`; `(cc1:num)`; `(aa1:num)`; `(Pc1:(num)Agent)`; `(Pa1:(num)Agent)`; `(va1:num)`; `(nd1:num)`; `(ug1:num)`; `(vg1:num)`; `(yg1:num)`; `(uh1:num)`; `(vh1:num)`; `(dd1:num)`; `(Pd1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`]);;
e (llmeta_assumption [`(x':num)`; `(P':(num)Agent)`; `(y1:num)`; `(ua1:num)`; `(xa1:num)`; `(na1:num)`; `(xb1:num)`; `(uc1:num)`; `(nb1:num)`; `(vd1:num)`; `(ud1:num)`; `(xd1:num)`; `(bb1:num)`; `(Pb1:(num)Agent)`; `(vc1:num)`; `(nc1:num)`; `(ue1:num)`; `(ve1:num)`; `(ye1:num)`; `(vf1:num)`; `(uf1:num)`; `(xf1:num)`; `(cc1:num)`; `(aa1:num)`; `(Pc1:(num)Agent)`; `(Pa1:(num)Agent)`; `(va1:num)`; `(nd1:num)`; `(ug1:num)`; `(vg1:num)`; `(yg1:num)`; `(uh1:num)`; `(vh1:num)`; `(dd1:num)`; `(Pd1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`]);;
e (llmeta_assumption [`(x':num)`; `(P':(num)Agent)`; `(y1:num)`; `(ua1:num)`; `(xa1:num)`; `(na1:num)`; `(xb1:num)`; `(uc1:num)`; `(nb1:num)`; `(vd1:num)`; `(ud1:num)`; `(xd1:num)`; `(bb1:num)`; `(Pb1:(num)Agent)`; `(vc1:num)`; `(nc1:num)`; `(ue1:num)`; `(ve1:num)`; `(ye1:num)`; `(vf1:num)`; `(uf1:num)`; `(xf1:num)`; `(cc1:num)`; `(aa1:num)`; `(Pc1:(num)Agent)`; `(Pa1:(num)Agent)`; `(va1:num)`; `(nd1:num)`; `(ug1:num)`; `(vg1:num)`; `(yg1:num)`; `(uh1:num)`; `(vh1:num)`; `(dd1:num)`; `(Pd1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`]);;


p();;
hd it;;
fst3 it;;
map (instantiate (snd it)) (fst it);;


g `? P Q x y. (|-- (' (((AA ++ AB) ** (B ++ C)) <> x)) P ) ===> (|-- (' ((((AA ++ AB) ** B) ++ ((AA ++ AB) ** C)) <> y)) Q )`;;
e (REPEAT META_EXISTS_TAC);;


e (MIMP_TAC);;

e (REPEAT DISCH_TAC);;
e (llrule_tac [(`C1`,`((AA ++ AB) ** (B ++ C))`)] (number_vars_thm 1 ll_cut));;
e (llmeta_assumption [`(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(P:(num)Agent)`; `(Q:(num)Agent)`; `(x:num)`; `(y:num)`]);;
e (REWRITE_TAC[NEG_PLUS;NEG_TIMES]);;
e (llrule (number_vars_thm 2 ll_par));;
e (llrule_tac [`A3`,`NEG B`] (number_vars_thm 3 ll_with));;

e (llrule (number_vars_thm 4 ll_plus1));;
e (llrule (number_vars_thm 5 ll_times));;

e (llrule (number_vars_thm 6 ll_with));;
e (llrule (number_vars_thm 7 ll_plus1));;
e (llrule_tac [`A8`,`AA`] (number_vars_thm 8 ll_id));;
e (llrule (number_vars_thm 9 ll_plus2));;
e (llrule_tac [`A10`,`AB`] (number_vars_thm 10 ll_id));;
e (llrule_tac [`A11`,`B`] (number_vars_thm 11 ll_id));;

e (llrule (number_vars_thm 12 ll_plus2));;
e (llrule (number_vars_thm 13 ll_times));;

e (llrule (number_vars_thm 14 ll_with));;
e (llrule (number_vars_thm 15 ll_plus1));;
e (llrule_tac [`A16`,`AA`] (number_vars_thm 16 ll_id));;
e (llrule (number_vars_thm 17 ll_plus2));;
e (llrule_tac [`A18`,`AB`] (number_vars_thm 18 ll_id));;
e (llrule_tac [`A19`,`C`] (number_vars_thm 19 ll_id));;
 top_thm();;
p();;
hd it;;
fst3 it;;
map (instantiate (snd it)) (fst it);;




(* Example of interaction of assoc filter with a process *)

g `?P newout. 
  (|-- (' (((X ** Y) ** Z) <> gg)) MyProc) ===> 
  (|-- (' ((X ** (Y ** Z)) <> newout)) P)`;;
e (REPEAT META_EXISTS_TAC);;
e MIMP_TAC;;
e (REPEAT DISCH_TAC);;
e (llrule (number_vars_thm 1 lltimes_assoc));;
e (llrule (number_vars_thm 2 ll_id));;
e (llrule (number_vars_thm 3 ll_id));;
e (llrule (number_vars_thm 4 ll_id));;
ellma ();;
top_thm();;
p();;
hd it;;
fst3 it;;
instantiate (snd it) `P:(num)Agent`;;

let qqterm = it;;
print_piviz qqterm;;




(* Example of interaction of comm filter with a process *)

g `?P newout. 
  (|-- (' ((X ** Y) <> gg)) MyProc) ===> 
  (|-- (' ((Y ** X) <> newout)) P)`;;
e (REPEAT META_EXISTS_TAC);;
e MIMP_TAC;;
e (REPEAT DISCH_TAC);;
e (llrule (number_vars_thm 1 lltimes_comm));;
e (llrule (number_vars_thm 2 ll_id));;
e (llrule (number_vars_thm 3 ll_id));;
ellma ();;
top_thm();;
p();;
hd it;;
fst3 it;;
instantiate (snd it) `P:(num)Agent`;;

let qqterm = it;;
print_piviz qqterm;;


g `?Q . 
  (|-- (G ^ ' (A <> a)) P) ===> 
  (|-- (G ^ ' (NEG B <> buf) ^ ' ((A ** B) <> z)) Q)`;;
e (REPEAT META_EXISTS_TAC);;
e MIMP_TAC;;
e (REPEAT DISCH_TAC);;
e (llrule (number_vars_thm 1 ll_times));;
ellma();;
e (llrule (number_vars_thm 2 ll_id));;
top_thm();;
p();;
hd it;;
fst3 it;;
instantiate (snd it) `Q:(num)Agent`;;

let qqterm = it;;


(* Example 1 from Bellin and Scott, p. 13 *)

gll `? P . |-- (' (B <> z) ^ '((NEG A ++ NEG B) <> t)) P`;;
ell (META_EXISTS_TAC);;
ell (llrule_tac [(`C`,`(NEG A ++ NEG B)`);(`x`,`w_:num`);(`y`,`w_:num`)] ll_cut);;
ell (REWRITE_TAC[NEG_CLAUSES;NEG_NEG]);;
ell (llrule_tac [(`x`,`x_:num`);(`y`,`y_:num`)] ll_with);;

ell (llrule_tac [(`x`,`p:num`)] ll_plus1);;
ell (llrule_tac [(`C`,`(NEG A ++ NEG A)`);(`x`,`w:num`);(`y`,`w:num`)] ll_cut);;
ell (REWRITE_TAC[NEG_CLAUSES;NEG_NEG]);;
ell (llrule_tac [(`x`,`x:num`);(`y`,`y:num`)] ll_with);;
ell (llrule ll_id);;
ell (llrule ll_id);;

ell (llrule_tac [(`x`,`p_:num`)] ll_plus1);;
ell (llrule ll_id);;

ell (llrule_tac [(`y`,`q_:num`)] ll_plus2);;
ell (llrule ll_id);;

ell (llrule_tac [(`y`,`q__:num`)] ll_plus2);;
ell (llrule ll_id);;


let BS_EX_1 = top_thm();;
let PTZ = instantiate (top_inst()) `P:NAgent`;;

let PTZ' = 
`Res [w_:num]
   (Comp
     (Res [q__]
     (In w_ [u11; v11] (Out v11 [q__] (In q__ [a12] (Out z [a12] Zero)))))
   (Res [u1; v1]
    (Out w_ [u1; v1]
    (Plus
     (In u1 [x_]
     (Res [p]
     (In t [u2; v2]
     (Out u2 [p]
     (Res [z3]
     (Comp
      (Res [p_]
       (In w [u7; v7] (Out u7 [p_] (In p_ [a8] (Out x_ [a8] Zero)))))
     (Res [u4; v4]
      (Out w [u4; v4]
      (Plus (In u4 [x] (In p [a5] (Out x [a5] Zero)))
      (In v4 [y] (In p [a6] (Out y [a6] Zero))))))
     ))))))
    (In v1 [y_]
    (Res [q_]
    (In t [u9; v9] (Out v9 [q_] (In q_ [a10] (Out y_ [a10] Zero)))))))))
   )`;;



gll `? P . |-- (' (B <> z) ^ '((NEG A ++ NEG B) <> t)) P`;;
ell (META_EXISTS_TAC);;
ell (llrule_tac [(`C`,`(NEG A ++ NEG B)`);(`x`,`w':num`);(`y`,`w':num`)] ll_cut);;
ell (REWRITE_TAC[NEG_CLAUSES;NEG_NEG]);;
ell (llrule_tac [(`x`,`x':num`);(`y`,`y':num`)] ll_with);;

ell (llrule_tac [(`x`,`p:num`)] ll_plus1);;
ell (llrule ll_id);;

ell (llrule_tac [(`y`,`q':num`)] ll_plus2);;
ell (llrule ll_id);;

ell (llrule_tac [(`y`,`q'':num`)] ll_plus2);;
ell (llrule ll_id);;


let BS_EX_1 = top_thm();;
let PTZ = instantiate (top_inst()) `P:NAgent`;;
