(* ========================================================================= *)
(* Deep embedding of polyadic pi-calculus.                                   *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                    2010                                   *)
(* ========================================================================= *)

(* Got some theorems off of http://lamp.epfl.ch/~roeckl/Pi/GP/Subst.html *)

needs "IsabelleLight/make.ml";;
needs "tools/make.ml";;
needs "tools/Library/fresh.ml";;
needs "tools/Library/substitution.ml";;
needs (!serv_dir ^ "support/support.ml");;
needs (!serv_dir ^ "support/lists.ml");;

(* Type declaration *)

let piCalc_INDUCT,piCalc_RECURSION = define_type
    " Agent = Zero
            | Out A (A list) Agent
            | In A (A list) Agent
            | Tau Agent
            | Res (A list) Agent
            | Match A A Agent
            | Comp Agent Agent
            | Plus Agent Agent
            | Repl Agent";;


(* Induction tactic *)

let PI_INDUCT_TAC =
  MATCH_MP_TAC piCalc_INDUCT THEN
  REPEAT CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN GEN_TAC THEN DISCH_TAC];;


(* Injectivity theorem *)

let PI_INJ = injectivity "Agent";;


let is_agent tm = try ( (fst o dest_type o type_of) tm = "Agent" ) with Failure _ -> false;;
  

(* ------------------------------------------------------------------------- *)
(* Agent definitions                                                         *)
(* ------------------------------------------------------------------------- *) 
(* Agent definitions are of the form: a (x1,x2,...,xn) = agent               *)
(* where 'a' is the name of the agent, 'xi' its free names, and 'agent' a    *)
(* pi-calculus process.                                                      *)
(* ------------------------------------------------------------------------- *) 

let is_agent_fun chantp tm =
  try (
  let comb,args = strip_comb tm in
  let aargs = dest_tuple (hd args) in
  let tpmatch = type_matches (mk_type ("fun",[`:A`;mk_type ("Agent",[chantp])])) comb
  and chtpmatch = forall (type_matches chantp) aargs in
  (tpmatch & chtpmatch & tl args = [])
  ) with Failure _ -> false;;

let is_agent_def chantp tm =
  try (
    let fs,def = strip_forall tm in
    let eq = (fst o dest_eq) def in
    (forall (C mem fs) o dest_tuple o rand) eq &
      is_eq def &
      is_agent_fun chantp eq
  ) with Failure _ -> false;;


(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Functions about names.                                                    *)
(* ------------------------------------------------------------------------- *)
(* We define two versions of these functions, one returning a set and one    *)
(* returning a list. We found lists to be generally easier to reason about   *)
(* in HOL Light.                                                             *)
(* We prove that the two definitions are equivalent.                         *)
(* ------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
(* Free names.                                                               *)
(* ------------------------------------------------------------------------- *)


let FN = new_recursive_definition piCalc_RECURSION 
 `(FN Zero = {}) /\
  (!x y P. FN (Out x y P) = {x} UNION (set_of_list y) UNION (FN P)) /\
  (!x y P. FN (In x y P) = {x} UNION ((FN P) DIFF (set_of_list y))) /\
  (!P. FN (Tau P) = FN P) /\
  (!x P. FN (Res x P) = (FN P) DIFF (set_of_list x)) /\
  (!x y P. FN (Match x y P) = {x,y} UNION (FN P)) /\
  (!P Q. FN (Comp P Q) = (FN P) UNION (FN Q)) /\
  (!P Q. FN (Plus P Q) = (FN P) UNION (FN Q)) /\
  (!P. FN (Repl P) = FN P)`;;

let FNL = new_recursive_definition piCalc_RECURSION 
 `(FNL Zero = []) /\
  (!x y P. FNL (Out x y P) = CONS x (APPEND y (FNL P))) /\
  (!x y P. FNL (In x y P) = CONS x ((FNL P) LDIFF y)) /\
  (!P. FNL (Tau P) = FNL P) /\
  (!x P. FNL (Res x P) = (FNL P) LDIFF x) /\
  (!x y P. FNL (Match x y P) = CONS x (CONS y (FNL P))) /\
  (!P Q. FNL (Comp P Q) = APPEND (FNL P) (FNL Q)) /\
  (!P Q. FNL (Plus P Q) = APPEND (FNL P) (FNL Q)) /\
  (!P. FNL (Repl P) = FNL P)`;;

let FN_EQ_FNL = prove (`!P. FN P = set_of_list (FNL P)`, 
		      MATCH_MP_TAC piCalc_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN 
			REWRITE_TAC[FN;FNL;SET_OF_LIST_APPEND;SET_OF_LIST_LDIFF;set_of_list;FILTER] 
			THEN TRY (DISCH_THEN SUBST1_TAC) THEN SET_TAC[]);;


let mk_pi_fn tm = mk_icomb (`FN`,tm);;


(* ------------------------------------------------------------------------- *)
(* Bound names.                                                              *)
(* ------------------------------------------------------------------------- *)


let BN = new_recursive_definition piCalc_RECURSION 
 `(BN Zero = {}) /\
  (!x y P. BN (Out x y P) = (BN P)) /\
  (!x y P. BN (In x y P) = (set_of_list y) UNION (BN P)) /\
  (!P. BN (Tau P) = BN P) /\
  (!x P. BN (Res x P) = (set_of_list x) UNION (BN P)) /\
  (!x y P. BN (Match x y P) = (BN P)) /\
  (!P Q. BN (Comp P Q) = (BN P) UNION (BN Q)) /\
  (!P Q. BN (Plus P Q) = (BN P) UNION (BN Q)) /\
  (!P. BN (Repl P) = BN P)`;;

let BNL = new_recursive_definition piCalc_RECURSION 
 `(BNL Zero = []) /\
  (!x y P. BNL (Out x y P) = (BNL P)) /\
  (!x y P. BNL (In x y P) = APPEND y (BNL P)) /\
  (!P. BNL (Tau P) = BNL P) /\
  (!x P. BNL (Res x P) =  APPEND x (BNL P)) /\
  (!x y P. BNL (Match x y P) = (BNL P)) /\
  (!P Q. BNL (Comp P Q) = APPEND (BNL P) (BNL Q)) /\
  (!P Q. BNL (Plus P Q) = APPEND (BNL P) (BNL Q)) /\
  (!P. BNL (Repl P) = BNL P)`;;

let BN_EQ_BNL = prove (`!P. BN P = set_of_list (BNL P)`, 
		      MATCH_MP_TAC piCalc_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN 
			REWRITE_TAC[BN;BNL;SET_OF_LIST_APPEND;SET_OF_LIST_LDIFF;set_of_list;FILTER] 
			THEN TRY (DISCH_THEN SUBST1_TAC) THEN SET_TAC[]);;

let mk_pi_bn tm = mk_icomb (`BN`,tm);;


(* ------------------------------------------------------------------------- *)
(* All names.                                                                *)
(* ------------------------------------------------------------------------- *)

let NAMES = new_recursive_definition piCalc_RECURSION 
 `(NAMES Zero = {}) /\
  (!x y P. NAMES (Out x y P) = {x} UNION (set_of_list y) UNION (NAMES P)) /\
  (!x y P. NAMES (In x y P) = {x} UNION (set_of_list y) UNION (NAMES P)) /\
  (!P. NAMES (Tau P) = NAMES P) /\
  (!x P. NAMES (Res x P) = (set_of_list x) UNION (NAMES P)) /\
  (!x y P. NAMES (Match x y P) = {x,y} UNION (NAMES P)) /\
  (!P Q. NAMES (Comp P Q) = (NAMES P) UNION (NAMES Q)) /\
  (!P Q. NAMES (Plus P Q) = (NAMES P) UNION (NAMES Q)) /\
  (!P. NAMES (Repl P) = NAMES P)`;;

let NAMESL = new_recursive_definition piCalc_RECURSION 
 `(NAMESL Zero = []) /\
  (!x y P. NAMESL (Out x y P) = CONS x (APPEND y (NAMESL P))) /\
  (!x y P. NAMESL (In x y P) = CONS x (APPEND y (NAMESL P))) /\
  (!P. NAMESL (Tau P) = NAMESL P) /\
  (!x P. NAMESL (Res x P) = APPEND x (NAMESL P)) /\
  (!x y P. NAMESL (Match x y P) = CONS x (CONS y (NAMESL P))) /\
  (!P Q. NAMESL (Comp P Q) = APPEND (NAMESL P) (NAMESL Q)) /\
  (!P Q. NAMESL (Plus P Q) = APPEND (NAMESL P) (NAMESL Q)) /\
  (!P. NAMESL (Repl P) = NAMESL P)`;;

let NAMES_EQ_NAMESL = prove (`!P. NAMES P = set_of_list (NAMESL P)`, 
		      MATCH_MP_TAC piCalc_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN 
			REWRITE_TAC[NAMES;NAMESL;SET_OF_LIST_APPEND;SET_OF_LIST_LDIFF;set_of_list;FILTER] 
			THEN TRY (DISCH_THEN SUBST1_TAC) THEN SET_TAC[]);;  

let mk_pi_names tm = mk_icomb (`NAMES`,tm);;


(* ------------------------------------------------------------------------- *)
(* Properties of sets of names.                                              *)
(* ------------------------------------------------------------------------- *)

let NAMES_FN_UNION_BN = prove ( `!P. NAMES P = (FN P) UNION (BN P)`, 
				MATCH_MP_TAC piCalc_INDUCT THEN REWRITE_TAC[NAMES;BN;FN;UNION_EMPTY;UNION_ASSOC]
				  THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN 
				  (DISCH_THEN SUBST1_TAC ORELSE DISCH_THEN (CONJUNCTS_THEN SUBST1_TAC)) 
				  THEN SET_TAC[]);;

let FINITE_FN = prove (`!P . FINITE (FN P)`, 
		       MATCH_MP_TAC piCalc_INDUCT THEN REWRITE_TAC[FN;FINITE_RULES] THEN
			 REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
			 REWRITE_TAC[FINITE_UNION;FINITE_SING;FINITE_DIFF;FINITE_SET_OF_LIST;FINITE_INSERT]);;

let FINITE_BN = prove (`!P . FINITE (BN P)`, 
		       MATCH_MP_TAC piCalc_INDUCT THEN REWRITE_TAC[BN;FINITE_RULES] THEN
			 REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
			 REWRITE_TAC[FINITE_UNION;FINITE_SING;FINITE_DIFF;FINITE_SET_OF_LIST;FINITE_INSERT]);;

let FINITE_NAMES = prove (`!P . FINITE (NAMES P)`, REWRITE_TAC[NAMES_FN_UNION_BN;FINITE_FN;FINITE_BN;FINITE_UNION]);;

(* ------------------------------------------------------------------------- *)
(* Properties of lists of names.                                             *)
(* ------------------------------------------------------------------------- *)

let NAME_BN_OR_FNL = prove (`!P x:A. MEM x (NAMESL P) <=> (MEM x (BNL P)) \/ (MEM x (FNL P))`, 
			   GEN_ALL_TAC THEN EQ_TAC THEN SPEC_TAC (`P:(A)Agent`,`P:(A)Agent`) THEN 
			     MATCH_MP_TAC piCalc_INDUCT THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN 
			     REWRITE_TAC[NAMESL;BNL;FNL;MEM;MEM_APPEND;MEM_LDIFF] THEN MESON_TAC[]);;

let NON_NAME_FNL = prove(`!x P. ~(MEM x (NAMESL P)) ==> ~(MEM x (FNL P))`, GEN_ALL_TAC THEN REWRITE_TAC[NAME_BN_OR_FNL;DE_MORGAN_THM] THEN 
			  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC ACCEPT_TAC));;

let NON_NAME_BNL = prove(`!x P. ~(MEM x (NAMESL P)) ==> ~(MEM x (BNL P))`, GEN_ALL_TAC THEN REWRITE_TAC[NAME_BN_OR_FNL;DE_MORGAN_THM] THEN 
			  DISCH_THEN (CONJUNCTS_THEN2 ACCEPT_TAC ASSUME_TAC));;


(* ------------------------------------------------------------------------- *)
(* Computation of BN, FN, and NAMES.                                         *)
(* ------------------------------------------------------------------------- *)

let rec FNL_CONV eqconv tm =
  if (is_strconst "Zero" (rand tm)) then PURE_REWRITE_CONV[FNL] tm else
  let comb,args = strip_comb (rand tm) in
  let conv =
    if (is_strcomb "Out" comb) then 
    PATH_CONV "rr" (FNL_CONV eqconv) THENC RAND_CONV (REWRITE_CONV[APPEND])
    else if (is_strcomb "In" comb) then 
    PATH_CONV "rlr" (FNL_CONV eqconv) THENC RAND_CONV (LDIFF_CONV eqconv)
    else if (is_strcomb "Tau" comb) then 
    FNL_CONV eqconv
    else if (is_strcomb "Res" comb) then 
    PATH_CONV "lr" (FNL_CONV eqconv) THENC LDIFF_CONV eqconv
    else if (is_strcomb "Match" comb) then 
    PATH_CONV "rr" (FNL_CONV eqconv)
    else if (is_strcomb "Comp" comb) then 
    PATH_CONV "lr" (FNL_CONV eqconv) THENC PATH_CONV "r" (FNL_CONV eqconv) THENC REWRITE_CONV[APPEND]
    else if (is_strcomb "Plus" comb) then 
    PATH_CONV "lr" (FNL_CONV eqconv) THENC PATH_CONV "r" (FNL_CONV eqconv) THENC REWRITE_CONV[APPEND]
    else if (is_strcomb "Repl" comb) then 
    FNL_CONV eqconv
    else failwith ("FN_CONV: Unknown pi-calculus combinator: " ^ (string_of_term comb)) in
  (PURE_ONCE_REWRITE_CONV[FNL] THENC conv) tm;;

let rec BNL_CONV eqconv tm =
  if (is_strconst "Zero" (rand tm)) then PURE_REWRITE_CONV[BNL] tm else
  let comb,args = strip_comb (rand tm) in
  let conv =
    if (is_strcomb "Out" comb) then 
    BNL_CONV eqconv
    else if (is_strcomb "In" comb) then 
    RAND_CONV (BNL_CONV eqconv) THENC REWRITE_CONV[APPEND]
    else if (is_strcomb "Tau" comb) then 
    BNL_CONV eqconv
    else if (is_strcomb "Res" comb) then 
    RAND_CONV (BNL_CONV eqconv) THENC REWRITE_CONV[APPEND]
    else if (is_strcomb "Match" comb) then 
    BNL_CONV eqconv
    else if (is_strcomb "Comp" comb) then 
    PATH_CONV "lr" (BNL_CONV eqconv) THENC PATH_CONV "r" (BNL_CONV eqconv) THENC REWRITE_CONV[APPEND]
    else if (is_strcomb "Plus" comb) then 
    PATH_CONV "lr" (BNL_CONV eqconv) THENC PATH_CONV "r" (BNL_CONV eqconv) THENC REWRITE_CONV[APPEND]
    else if (is_strcomb "Repl" comb) then 
    BNL_CONV eqconv
    else failwith ("BNL_CONV: Unknown pi-calculus combinator: " ^ (string_of_term comb)) in
  (PURE_ONCE_REWRITE_CONV[BNL] THENC conv) tm;;

let rec NAMESL_CONV eqconv tm =
  if (is_strconst "Zero" (rand tm)) then PURE_REWRITE_CONV[NAMESL] tm else
  let comb,args = strip_comb (rand tm) in
  let conv =
    if (is_strcomb "Out" comb) then 
    PATH_CONV "rr" (NAMESL_CONV eqconv) THENC RAND_CONV (REWRITE_CONV[APPEND])
    else if (is_strcomb "In" comb) then
    PATH_CONV "rr" (NAMESL_CONV eqconv) THENC RAND_CONV (REWRITE_CONV[APPEND])
    else if (is_strcomb "Tau" comb) then 
    NAMESL_CONV eqconv
    else if (is_strcomb "Res" comb) then 
    PATH_CONV "r" (NAMESL_CONV eqconv) THENC REWRITE_CONV[APPEND]
    else if (is_strcomb "Match" comb) then 
    PATH_CONV "rr" (NAMESL_CONV eqconv)
    else if (is_strcomb "Comp" comb) then 
    PATH_CONV "lr" (NAMESL_CONV eqconv) THENC PATH_CONV "r" (NAMESL_CONV eqconv) THENC REWRITE_CONV[APPEND]
    else if (is_strcomb "Plus" comb) then 
    PATH_CONV "lr" (NAMESL_CONV eqconv) THENC PATH_CONV "r" (NAMESL_CONV eqconv) THENC REWRITE_CONV[APPEND]
    else if (is_strcomb "Repl" comb) then 
    NAMESL_CONV eqconv
    else failwith ("NAMESL_CONV: Unknown pi-calculus combinator: " ^ (string_of_term comb)) in
  (PURE_ONCE_REWRITE_CONV[NAMESL] THENC conv) tm;;

(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Polyadic pi-calculus substitution.                                        *)
(* ------------------------------------------------------------------------- *)

let piSUB = new_recursive_definition piCalc_RECURSION 
 `(!ch s. piSUB ch Zero s = Zero) /\
  (!ch x y P s. piSUB ch (Out x y P) s = Out (SUB s x) (MAP (SUB s) y) (piSUB ch P s)) /\
  (!ch x y P s. piSUB ch (In x y P) s = 
      let vs = MAP (SUB s) ((FNL P) LDIFF y) in
      let y' = FRESHL ch y vs in
      let s' = FEMPTY |++ (ZIP y y') in
	In (SUB s x) y' (piSUB ch P (FUNION s' s))) /\
  (!ch P s. piSUB ch (Tau P) s = Tau (piSUB ch P s)) /\
  (!ch y P s. piSUB ch (Res y P) s =
      let vs = MAP (SUB s) ((FNL P) LDIFF y) in
      let y' = FRESHL ch y vs in
      let s' = FEMPTY |++ (ZIP y y') in
	Res y' (piSUB ch P (FUNION s' s))) /\
  (!ch x y P s. piSUB ch (Match x y P) s = Match (SUB s x) (SUB s y) (piSUB ch P s)) /\
  (!ch P Q s. piSUB ch (Comp P Q) s = Comp (piSUB ch P s) (piSUB ch Q s)) /\
  (!ch P Q s. piSUB ch (Plus P Q) s = Plus (piSUB ch P s) (piSUB ch Q s)) /\
  (!ch P s. piSUB ch (Repl P) s = Repl(piSUB ch P s))`;;

let is_piSUB tm = 
  try ((is_strcomb "piSUB" o rator o rator o rator) tm)
  with Failure _ -> false;;

(* ------------------------------------------------------------------------- *) 
(* Some properties.                                                          *)
(* ------------------------------------------------------------------------- *) 

let piSUB_EQ_SUB = prove (`!ch P (f:(A,A)fmap) g. (!x. SUB f x = SUB g x) ==> piSUB ch P f = piSUB ch P g`,
  GEN_TAC THEN MATCH_MP_TAC piCalc_INDUCT THEN simp[piSUB;injectivity "Agent";LET_DEF;LET_END_DEF] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_THEN ASSUME_TAC FORALL_SUBST_MAP THEN simp[] THENL [
  meson[] ; ALL_TAC ; ALL_TAC ; meson[] ; meson[] ] THEN
  MATCH_MP_THEN ASSUME_TAC SUBST_EQ_FUNION_FORALL THENL [
  CONTEXT_THEN ABBREV_TAC `fm = FEMPTY |++ ZIP a1 (FRESHL ch a1 (MAP (SUB g) (FNL a2 LDIFF a1)))` ;
  CONTEXT_THEN ABBREV_TAC `fm = FEMPTY |++ ZIP a0 (FRESHL ch a0 (MAP (SUB g) (FNL a1 LDIFF a0)))` ] THEN
  FIRST_X_ASSUM (ASSUME_TAC o (SPEC `fm:(A,A)fmap`)) THEN
  FIRST_X_ASSUM (ASSUME_TAC o (SPEC `FUNION (fm:(A,A)fmap) f`)) THEN
  FIRST_X_ASSUM (MATCH_MP_THEN ACCEPT_TAC));;

let piSUB_ID = prove (`!P ch x t. piSUB ch P (FEMPTY |++ (CONS (x,x) t)) = piSUB ch P (FEMPTY |++ t)`,
   MATCH_MP_TAC piCalc_INDUCT THEN
   simp[piSUB;SUBST_FUPDATE_LIST_ABSORB;MAP_SUBST_FUPDATE_LIST_ABSORB;LET_DEF;LET_END_DEF;injectivity "Agent";FUNION_FEMPTY_FUPDATE_LIST;APPEND]);;

let piSUB_FEMPTY = prove (`!ch P. piSUB ch P FEMPTY = P`,
   GEN_TAC THEN MATCH_MP_TAC piCalc_INDUCT THEN
   simp[piSUB;SUBST;FLOOKUP;FUNION_FEMPTY;MAP_SUBST_FEMPTY;LET_DEF;LET_END_DEF;injectivity "Agent";FRESHL_LDIFF_VAIN] THEN LIST_INDUCT_TAC THEN simp[ZIP;piSUB_ID;FUPDATE_LIST_NIL]);;

let piSUB_FUPDATE_NONFN = prove (`!ch P x y s. ~(x IN FN P) ==> piSUB ch P (s |+ (x,y)) = piSUB ch P s`,
   GEN_TAC THEN MATCH_MP_TAC piCalc_INDUCT THEN
   SIMP_TAC[piSUB;FN;IN_UNION;IN_DIFF;IN_SET_OF_LIST;DE_MORGAN_THM;SUBST_FUPDATE_VAIN;MAP_SUBST_FUPDATE_VAIN] THEN
   REPEAT STRIP_TAC THENL [
   CONTEXT_THEN subgoal_tac `~(MEM x (FNL a2 LDIFF a1))` ;
   CONTEXT_THEN subgoal_tac `~(MEM x (FNL a2 LDIFF a1))` ;
   ALL_TAC ;
   CONTEXT_THEN subgoal_tac `~(MEM x (FNL a1 LDIFF a0))` ] THEN
   simp[LENGTH_FRESHL;LET_DEF;LET_END_DEF;MAP_SUBST_FUPDATE_VAIN;injectivity "Agent";FUNION_FUPDATE;FDOM_FUPDATE_LIST;IN_SET_OF_LIST;MAP_FST_ZIP;FN_EQ_FNL;NOT_MEM_LDIFF;LDIFF_MEM] THEN
   COND_CASES_TAC THEN simp[]);;

let piSUB_DISJOINT = prove (`!s P. DISJOINT (FN P) (FDOM s) ==> piSUB ch P s = P`,
   FMAP_INDUCT_TAC THEN simp[piSUB_FEMPTY;FDOM_FUPDATE;DISJOINT_INSERT;DISJOINT_SYM;piSUB_FUPDATE_NONFN]);;

let piSUB_EQ_SUB_NAMES = prove (
   `!ch P (f:(A,A)fmap) g. (!x. x IN NAMES P ==> SUB f x = SUB g x) ==> piSUB ch P f = piSUB ch P g`,
   GEN_TAC THEN MATCH_MP_TAC piCalc_INDUCT THEN
   simp[piSUB;injectivity "Agent";LET_DEF;LET_END_DEF;NAMES;IN_UNION;IN_DIFF;IN_SET_OF_LIST;NAMES_EQ_NAMESL] THEN
   REPEAT STRIP_TAC THENL [
   meson[FORALL_MEM_SUBST_MAP] ;
   meson[] ;
   CONTEXT_THEN subgoal_tac `MAP (SUB f) (FNL a2 LDIFF a1) = MAP (SUB g) (FNL a2 LDIFF a1)` ;
   CONTEXT_THEN subgoal_tac `MAP (SUB f) (FNL a2 LDIFF a1) = MAP (SUB g) (FNL a2 LDIFF a1)` ;
   CONTEXT_THEN subgoal_tac `MAP (SUB f) (FNL a1 LDIFF a0) = MAP (SUB g) (FNL a1 LDIFF a0)` ;
   CONTEXT_THEN subgoal_tac `MAP (SUB f) (FNL a1 LDIFF a0) = MAP (SUB g) (FNL a1 LDIFF a0)` ;
   meson[] ;
   meson[] ;
   meson[] ] THENL [
   MATCH_MP_TAC FORALL_MEM_SUBST_MAP THEN simp[MEM_LDIFF;NAME_BN_OR_FNL] ;
   simp[] ;
   MATCH_MP_TAC FORALL_MEM_SUBST_MAP THEN simp[MEM_LDIFF;NAME_BN_OR_FNL] ;
   simp[] ;
   MATCH_MP_TAC FORALL_MEM_SUBST_MAP THEN simp[MEM_LDIFF;NAME_BN_OR_FNL] ;
   simp[] ;
   MATCH_MP_TAC FORALL_MEM_SUBST_MAP THEN simp[MEM_LDIFF;NAME_BN_OR_FNL] ;
   simp[] ] THEN meson[SUBST_EQ_FUNION]);;


(* Intuitively this seems like it should be provable, but I'm having trouble proving it. *)
(*
g `!ch P (f:(A,A)fmap) g. (!x. x IN FN P ==> SUB f x = SUB g x) ==> piSUB ch P f = piSUB ch P g`;;
 *)

(* ------------------------------------------------------------------------- *) 
(* Single name substitution.                                                 *)
(* ------------------------------------------------------------------------- *) 
(* This is for convenience.                                                  *)
(* ------------------------------------------------------------------------- *) 

let piSUB1 = new_definition `!ch P x y. piSUB1 ch P (x,y) = piSUB ch P (FEMPTY |+ (x,y))`;;
			  
let piSUB1_ID =
  let thm = ((REWRITE_RULE[FUPDATE_LIST_THM;piSUB_FEMPTY]) o GEN_ALL o (ISPECL [`P:(A)Agent`;`ch:A->(A)list->A`;`x:A`;`[]:(A#A)list`])) piSUB_ID in 
  prove (`!ch P (x:A). piSUB1 ch P (x,x) = P`, REWRITE_TAC[piSUB1;thm]);;

let piSUB1_NONFN = prove (`!ch P x y. ~(x IN FN P) ==> piSUB1 ch P (x,y) = P`, SIMP_TAC[piSUB1;piSUB_FUPDATE_NONFN;piSUB_FEMPTY]);;



(* ------------------------------------------------------------------------- *) 
(* Using numbers as names.                                                   *)
(* ------------------------------------------------------------------------- *) 

new_type_abbrev("NAgent",`:(num)Agent`);;


(* ------------------------------------------------------------------------- *) 
(* Computations (reductions) of (num)Agents with variables.                  *)
(* ------------------------------------------------------------------------- *) 
(* Variables in the term are mapped to natural numbers thus allowing         *)
(* computation with NUM_REDUCE_CONV or NUM_EQ_CONV.                          *)
(* ------------------------------------------------------------------------- *) 


(* ------------------------------------------------------------------------- *) 
(* Number substitution                                                       *)
(* ------------------------------------------------------------------------- *) 

let piSUBN = new_definition `!P s. piSUBN P s = piSUB NCH P s`;;

let piSUBN_RECURSION = prove(
 `(!s. piSUBN Zero s = Zero) /\
  (!x y P s. piSUBN (Out x y P) s = Out (SUB s x) (MAP (SUB s) y) (piSUBN P s)) /\
  (!x y P s. piSUBN (In x y P) s = 
      let vs = MAP (SUB s) ((FNL P) LDIFF y) in
      let y' = FRESHNL y vs in
      let s' = FEMPTY |++ (ZIP y y') in
	In (SUB s x) y' (piSUBN P (FUNION s' s))) /\
  (!P s. piSUBN (Tau P) s = Tau (piSUBN P s)) /\
  (!y P s. piSUBN (Res y P) s =
      let vs = MAP (SUB s) ((FNL P) LDIFF y) in
      let y' = FRESHNL y vs in
      let s' = FEMPTY |++ (ZIP y y') in
	Res y' (piSUBN P (FUNION s' s))) /\
  (!x y P s. piSUBN (Match x y P) s = Match (SUB s x) (SUB s y) (piSUBN P s)) /\
  (!P Q s. piSUBN (Comp P Q) s = Comp (piSUBN P s) (piSUBN Q s)) /\
  (!P Q s. piSUBN (Plus P Q) s = Plus (piSUBN P s) (piSUBN Q s)) /\
(!P s. piSUBN (Repl P) s = Repl(piSUBN P s))`,
  REWRITE_TAC[piSUBN;piSUB;FRESHNL]);;


(* ------------------------------------------------------------------------- *) 
(* Single number substitution.                                               *)
(* ------------------------------------------------------------------------- *) 

let piSUBN1 = new_definition `!P x y. piSUBN1 P (x,y) = piSUBN P (FEMPTY |+ (x,y))`;; 

(* Alternative *)
let piSUBN1_2 = prove (`!P x y. piSUBN1 P (x,y) = piSUB1 NCH P (x,y)`,REWRITE_TAC[piSUBN1;piSUB1;piSUBN]);;

let is_pisubn1 tm = 
  try ((rator o rator) tm = `piSUBN1`)
  with Failure _ -> false;;


(* ------------------------------------------------------------------------- *) 
(* Computation of substitution.                                              *)
(* ------------------------------------------------------------------------- *)
(* This requires a conversion freshconv to calculate the generation of a     *)
(* fresh name and a conversion eqconv to calculate equality between names.   *)
(* ------------------------------------------------------------------------- *) 

let rec PI_SUB_CONV freshconv eqconv tm =
  if not (is_piSUB tm) then failwith "PI_SUB_CONV: Not a pi-calculus substitution."
  else if (is_strconst "Zero" ((rand o rator) tm)) then PURE_REWRITE_CONV[piSUB] tm else
  let comb,args = strip_comb ((rand o rator) tm) in
  let NORM_CONV =
    PURE_REWRITE_CONV[FUNION_FUPDATE_LIST_1;FUNION_FEMPTY] THENC
		     REWRITE_CONV [FUPDATE_LIST_THM] THENC
		     FUPDATE_NORMALISE_CONV THENC
		     ONCE_REWRITE_CONV [GSYM FUPDATE_LIST_NIL] THENC
		     REWRITE_CONV [GSYM FUPDATE_LIST_CONS] in
  let conv =
    if (is_strcomb "Out" comb) then 
    PATH_CONV "llr" (SUBST_CONV eqconv) THENC
    PATH_CONV "lr" (PURE_REWRITE_CONV[MAP] THENC LIST_CONV(SUBST_CONV eqconv))
    else if (is_strcomb "In" comb) then
    PATH_CONV "rrlr" (FNL_CONV eqconv) THENC
    PATH_CONV "rr" (LDIFF_CONV eqconv) THENC
    PATH_CONV "r" (PURE_REWRITE_CONV[MAP] THENC LIST_CONV (SUBST_CONV eqconv)) THENC
    let_CONV THENC
    PATH_CONV "r" freshconv THENC
    let_CONV THENC
    PATH_CONV "r" (PURE_REWRITE_CONV[ZIP]) THENC
    let_CONV THENC
    PATH_CONV "rr" NORM_CONV THENC
    PURE_REWRITE_CONV[piSUB_ID] THENC
    PATH_CONV "llr" (SUBST_CONV eqconv)
    else if (is_strcomb "Tau" comb) then 
    ALL_CONV
    else if (is_strcomb "Res" comb) then
    PATH_CONV "rrlr" (FNL_CONV eqconv) THENC
    PATH_CONV "rr" (LDIFF_CONV eqconv) THENC
    PATH_CONV "r" (PURE_REWRITE_CONV[MAP] THENC LIST_CONV (SUBST_CONV eqconv)) THENC
    let_CONV THENC
    PATH_CONV "r" freshconv THENC
    let_CONV THENC
    PATH_CONV "r" (PURE_REWRITE_CONV[ZIP]) THENC
    let_CONV THENC
    PATH_CONV "rr" NORM_CONV THENC
    PURE_REWRITE_CONV[piSUB_ID]
    else if (is_strcomb "Match" comb) then 
    PATH_CONV "llr" (SUBST_CONV eqconv) THENC
    PATH_CONV "lr" (SUBST_CONV eqconv)
    else if (is_strcomb "Comp" comb) then 
    PATH_CONV "lr" (PI_SUB_CONV freshconv eqconv)
    else if (is_strcomb "Plus" comb) then 
    PATH_CONV "lr" (PI_SUB_CONV freshconv eqconv)
    else if (is_strcomb "Repl" comb) then
    ALL_CONV
    else failwith ("PI_SUB_CONV: Unknown pi-calculus combinator: " ^ (string_of_term comb)) in
  (PURE_ONCE_REWRITE_CONV[piSUB] THENC conv THENC RAND_CONV (PI_SUB_CONV freshconv eqconv)) tm;;

let PI_SUBN_CONV = PURE_REWRITE_CONV[piSUBN1;piSUBN] THENC PI_SUB_CONV FRESHNL_CONV NUM_EQ_CONV;;


(* ------------------------------------------------------------------------- *) 
(* In order to deal with actual pi-calculus terms, we need a mapping of      *)
(* variables to numbers.                                                     *)
(* ------------------------------------------------------------------------- *) 

(* ------------------------------------------------------------------------- *) 
(* PI_INSTVARS_CONV : term -> thm                                            *)
(* ------------------------------------------------------------------------- *)
(* Maps each free variable 'vi' in a (assumed pi-calculus) term 't' to a     *)
(* fresh number 'ni'.                                                        *)
(* It then generates the theorem:                                            *)
(*      v1, v2, ..., vi,... vn, |- t = s                                     *)
(* where 's' is 't' with all the variables substituted by their respective   *)
(* numbers.                                                                  *)
(* ------------------------------------------------------------------------- *) 

let PI_INSTVARS_CONV tm =
  let vars = filter (fun x -> (type_of x) = `:num`) (frees tm) 
  and nums = map (dest_small_numeral) (find_terms is_numeral tm) in
  let freshn = (itlist max nums 0) + 1 in
  let rec zipnums n vs = match vs with
    | [] -> []
    | (h::t) -> (h,mk_small_numeral n)::(zipnums (n+1) t) in
  let varpairs = zipnums freshn vars in
  let insts = map (fun (x,y) -> term_match [] x y) varpairs in
  let inst = itlist compose_insts insts null_inst in
  let hyps = map mk_eq varpairs 
  and conc = mk_eq (tm,instantiate inst tm) in
  let lemma = itlist (curry mk_imp) hyps conc in 
  (UNDISCH_ALL o prove) (lemma, REPEAT (DISCH_THEN SUBST1_TAC) THEN REFL_TAC);;


(* ------------------------------------------------------------------------- *) 
(* Once the computation is complete, we replace all numeral subterms with    *)
(* their corresponding variables.                                            *)
(* There is a chance new variables will be introduced (eg. by the choice     *)
(* function in substitution). These will be new numbers and they will be     *)
(* left as such.                                                             *)
(* ------------------------------------------------------------------------- *) 

let rec PI_UNINST_RULE thm =
  let hyps,conc = dest_thm thm in
  let tm = if is_eq conc then rand conc else conc in
  let hfilter x = if (not o is_eq) x then false else let l,r = dest_eq x in (is_var l) && (is_numeral r) in
  let hyps' = filter hfilter hyps in
  let subs = mapfilter dest_eq hyps' in
  let conc' = mk_eq (tm,subst subs tm) in
  let lemma = itlist (curry mk_imp) hyps' conc' in
  let thm' = (UNDISCH_ALL o prove) (lemma, REPEAT (DISCH_THEN SUBST1_TAC) THEN REFL_TAC) in
  if is_eq conc then TRANS thm thm' else thm';;


let PI_CONV conv tm = PI_UNINST_RULE ((PI_INSTVARS_CONV THENC conv) tm);;

(* ------------------------------------------------------------------------- *)
(* This conversion can be used to apply other conversions over agent         *)
(* definitions.                                                              *)
(* ------------------------------------------------------------------------- *)
(* The problem lies in the fact that applying a conversion to an agent       *)
(* that includes an agent definition, requires unfolding of that definition. *)
(* Once the result is calculated (e.g. of a substitution) then re-folding    *)
(* the definiton is non-trivial. Using reverse rewritting is actually pretty *)
(* slow (at least the way I tried it).                                       *)
(* Here, we rely on a 'reduce' function to do the calculation for us.        *)
(* This can be any arbitrary OCaml function (i.e. not a conversion).         *)
(* Unfolding the definition(s) in the result given by 'reduce' should match  *)
(* the result of the conversion.                                             *)
(* ------------------------------------------------------------------------- *) 
(* We use this to apply substitutions that do not rename bound variables.    *)
(* Can't see much use outside this context at the moment, but this is still  *)
(* general enough.                                                           *)
(* ------------------------------------------------------------------------- *)
(* TODO: Consider embedding FRANGE in finite maps and proving that if the    *)
(* FRANGE of a substitution is disjoint with bound (or all?) variables in    *)
(* an agent, then we can just rename the free variables (i.e. those in the   *)
(* definition.                                                               *)
(* We might need a more formal account of an agent definition in this case.  *)
(* We also might need a tuple_to_list function for this I guess, if we really*)
(* want to stick to tuples.                                                  *)
(* ------------------------------------------------------------------------- *) 


let PI_AGENT_REDUCE_CONV agents reduce conv pi =
  if (not o is_agent) pi
  then failwith ("PI_AGENT_REDUCE_CONV: Not a pi-calculus term: " ^ (string_of_term pi))
  else try (
    let chantp = (hd o snd o dest_type o type_of) pi in
(*    let gen_agent_vars tm =
      if (not o is_agent_def chantp) tm
      then failwith ("PI_AGENT_REDUCE_CONV: Not an agent definition: " ^ (string_of_term tm))
      else 
      let vars = (dest_tuple o rand o lhs) tm in list_mk_forall (vars,tm) in *)
    let rel = mk_eq (pi, reduce pi) in
    let athms = map ASSUME (filter (is_agent_def chantp) agents) in
    let thm1 = (REWRITE_CONV athms THENC PI_INSTVARS_CONV) rel in
    let conv_res = (LAND_CONV conv THENC REWRITE_CONV[injectivity "Agent"] o rhs o concl) thm1 in
    EQT_ELIM (TRANS thm1 conv_res)) with Failure s -> failwith ("PI_AGENT_REDUCE_CONV: " ^ s);;
(*
    let thm2 = 
    let hyps,conc = dest_thm thm2 in
    let lemma = itlist (curry mk_imp) hyps (mk_eq (rhs conc,reduce pi)) in
    let thm3 = UNDISCH_ALL (prove(lemma,REPEAT DISCH_TAC THEN ASM REWRITE_TAC[] THEN REFL_TAC)) in
    TRANS thm2 thm3 ) with Failure s -> failwith ("PI_AGENT_REDUCE_CONV: " ^ s);;
*)





(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Pretty printing function using the Mobility Workbench (MWB) notation.     *)
(* ------------------------------------------------------------------------- *)
(* We're using an unconventional way to print substitutions.                 *)
(* ------------------------------------------------------------------------- *)

let rec print_pi tm =
  if ((fst o dest_type o type_of) tm = "Agent") then
    if tm = `Zero:(num)Agent` then print_string "0" 
    else if (is_var tm) then (print_string o fst o dest_var) tm 
    else 
      let subn_string (tm1,tm2)= (
	"[" ^ (string_of_term tm1) ^ ">" ^ (string_of_term tm2) ^ "]"
      ) in
      let print_ltm ltm =
	let rec print_terms tml =
	  (match tml with 
	     | [] -> ()
	     | [h] -> print_term h ; ()
	     | h::t -> print_term h; print_string ", "; print_terms t) in
	  print_terms (dest_list ltm) in
      let comb,args = strip_comb tm in
	if ( comb = `Out:num->(num)list->(num)Agent->(num)Agent`) then (print_string "'"; print_term (hd args) ; print_string "<"; print_ltm ((hd o tl) args); print_string ">."; print_pi (last args))
	else if ( comb = `In:num->(num)list->(num)Agent->(num)Agent` ) then (print_term (hd args) ; print_string "("; print_ltm ((hd o tl) args); print_string ")."; print_pi (last args))
	else if ( comb = `Res:(num)list->(num)Agent->(num)Agent`) then (print_string "(v "; print_ltm (hd args); print_string ")("; print_pi (last args) ; print_string ")")
	else if ( comb = `Comp:(num)Agent->(num)Agent->(num)Agent`) then (print_string "("; print_pi (hd args); print_string " || "; print_pi (last args) ; print_string ")")
	else if ( comb = `Plus:(num)Agent->(num)Agent->(num)Agent`) then (print_string "("; print_pi (hd args); print_string " + "; print_pi (last args) ; print_string ")")
	else if ( comb = `piSUBN1:(num)Agent->num#num->(num)Agent`) then 
	  (print_string "{" ; (print_pi (hd args)) ; print_string "}" ; 
	     ((print_string o subn_string) (dest_pair (last args))))
	else if ( is_const comb or is_var comb ) then (print_string "(" ; print_term tm ; print_string ")")
	else failwith ("nop!" ^ (string_of_term comb) ^ ":" ^ (string_of_type (type_of comb))) else failwith "noop!";;

(* install_user_printer ("print_pi",print_pi);; *)

let rec print_pi_latex tm =
  if ((fst o dest_type o type_of) tm = "Agent") then
    if tm = `Zero:(num)Agent` then print_string "0" 
    else if (is_var tm) then (print_string o fst o dest_var) tm 
    else 
      let subn_string (tm1,tm2)= (
	"[" ^ (string_of_term tm2) ^ "/" ^ (string_of_term tm1) ^ "]"
      ) in
      let print_ltm ltm =
	let rec print_terms tml =
	  (match tml with 
	     | [] -> ()
	     | [h] -> print_term h ; ()
	     | h::t -> print_term h; print_string ", "; print_terms t) in
	  print_terms (dest_list ltm) in
      let comb,args = strip_comb tm in
	if ( comb = `Out:num->(num)list->(num)Agent->(num)Agent`) then (print_string "\\overline{"; print_term (hd args) ; print_string "}\\langle "; print_ltm ((hd o tl) args); print_string "\\rangle."; print_pi_latex (last args))
	else if ( comb = `In:num->(num)list->(num)Agent->(num)Agent` ) then (print_term (hd args) ; print_string "("; print_ltm ((hd o tl) args); print_string ")."; print_pi_latex (last args))
	else if ( comb = `Res:(num)list->(num)Agent->(num)Agent`) then (print_string "(\\nu\\ "; print_ltm (hd args); print_string ")("; print_pi_latex (last args) ; print_string ")")
	else if ( comb = `Comp:(num)Agent->(num)Agent->(num)Agent`) then (print_string "("; print_pi_latex (hd args); print_string "\\ ||\\ "; print_pi_latex (last args) ; print_string ")")
	else if ( comb = `Plus:(num)Agent->(num)Agent->(num)Agent`) then (print_string "("; print_pi_latex (hd args); print_string "\\ +\\ "; print_pi_latex (last args) ; print_string ")")
	else if ( comb = `piSUBN1:(num)Agent->num#num->(num)Agent`) then 
	  (print_string "(" ; (print_pi_latex (hd args)) ; print_string ")" ; 
	     ((print_string o subn_string) (dest_pair (last args))))
	else if ( is_const comb or is_var comb ) then (print_string "(" ; print_term tm ; print_string ")")
	else failwith ("nop!" ^ (string_of_term comb) ^ ":" ^ (string_of_type (type_of comb))) else failwith "noop!";;

