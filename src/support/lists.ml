(* ========================================================================= *)
(* Useful list theorems, tactics etc extending standard HOL Light list       *)
(* library (list.ml).                                                        *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                    2010                                   *)
(* ========================================================================= *)

needs "IsabelleLight/make.ml";;
needs "tools/Library/lists.ml";;
needs (!serv_dir ^ "support/support.ml");;


(* Misc lemmas used in pi.ml *)


(*
let ALL_ID_LEMMA = prove ( `!l a. ALL (\x. (\z. if MEM z (FILTER (\x. ~MEM x l) s) then a z else z) (x) = x) l `,
	LIST_INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[ALL] THEN CONJ_TAC THEN 
	  simp[MEM;FILTER;DE_MORGAN_THM;MEM_FILTER;COND_ELSE_EQ;GSYM ALL_MEM]);;
*)

let ALL_ID_LEMMA = prove (`!l a. ALL (\x. (\z. if MEM z (s LDIFF l) then a z else z) (x) = x) l `, LIST_INDUCT_TAC THEN 
			    simp[LDIFF_EMPTY;MEM_LDIFF;MEM;ALL;MESON[] `!P b c. (if P then c else b)= b  <=> (b = c) \/ ~P`;DE_MORGAN_THM;GSYM ALL_MEM]);;



let MAP_ID_LEMMA = GEN_ALL (MATCH_MP (SPEC_ALL MAP_EQ_DEGEN) (SPEC_ALL ALL_ID_LEMMA));;


let MAP_ID_LEMMA2 = prove ( `!l s k. MAP s l = l ==> MAP (\x. if MEM x k then x else s x) l = l`, 
			    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP;CONS_11] THEN GEN_ALL_TAC THEN 
			      DISCH_THEN (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC) THEN 
			      RULE_ASSUM_TAC SPEC_ALL THEN drule mp THEN simp[COND_ID]);;


