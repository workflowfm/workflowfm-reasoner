(* ========================================================================= *)
(* pi-calculus congurence relation.                                          *)
(*                                                                           *)
(*                              Petros Papapanagiotou                        *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                    2017                                   *)
(* ========================================================================= *)

needs (!serv_dir ^ "pap/pi.ml");;

let picong_RULES,picong_INDUCT,picong_CASES = new_inductive_definition
  `(!P. PICONG P P) /\
  (!P Q. PICONG P Q ==> PICONG Q P) /\
  (!P Q R. PICONG P Q /\ PICONG Q R ==> PICONG P R) /\

  (!a b P Q. PICONG P Q ==> PICONG (Out a b P) (Out a b Q)) /\
  (!a b P Q. PICONG P Q ==> PICONG (In a b P) (In a b Q)) /\
  (!P Q. PICONG P Q ==> PICONG (Tau P) (Tau Q)) /\
  (!a b P Q. PICONG P Q ==> PICONG (Match a b P) (Match a b Q)) /\
  (!a P Q. PICONG P Q ==> PICONG (Res a P) (Res a Q)) /\
  (!P Q R. PICONG P Q ==> PICONG (Comp P R) (Comp Q R)) /\
  (!P Q R. PICONG P Q ==> PICONG (Plus P R) (Plus Q R)) /\
  (!P Q. PICONG P Q ==> PICONG (Repl P) (Repl Q)) /\

  (!P. PICONG (Comp P Zero) P) /\
  (!P Q. PICONG (Comp P Q) (Comp Q P)) /\
  (!P Q R. PICONG (Comp (Comp P Q) R) (Comp P (Comp Q R))) /\

  (!P. PICONG (Plus P Zero) P) /\
  (!P Q. PICONG (Plus P Q) (Plus Q P)) /\
  (!P Q R. PICONG (Plus (Plus P Q) R) (Plus P (Plus Q R))) /\

  (!l. PICONG (Res l Zero) Zero) /\
  (!k l P. PICONG (Res k (Res l P)) (Res l (Res k P))) /\
  (!k l P. PICONG (Res k (Res l P)) (Res (APPEND k l) P)) /\  
  
  (!P. PICONG (Repl P) (Comp P (Repl P))) /\

  (!l P Q. (!n. MEM n l ==> ~(MEM n (FNL Q))) ==> PICONG (Res l (Comp P Q)) (Comp (Res l P) Q)) /\

  (!a P. PICONG (Match a a P) P) /\
  (!a b P. ~(a = b) ==> PICONG (Match a b P) Zero)`;;

(*
inductive "PiCon"
  intrs
    
inp   "[| fP c .~ fP' c ; rstra fP ; rstra fP' ; fresha c fP ; fresha c fP' |] \
            \ ==> a[x]. fP x .~ a[x]. fP' x"

    ch     "[| P .~ Q ; rstr R |] ==> P .+ R .~ Q .+ R"
    par    "[| P .~ Q ; rstr R |] ==> P .| R .~ Q .| R"
    res    "[| fP c .~ fP' c ; rstra fP ; rstra fP' ; fresha c fP ; fresha c fP' |] \
            \ ==> .#x. fP x .~ .#x. fP' x"

    rep    "[| fP c .~ fP' c ; rstra fP ; rstra fP' ; fresha c fP ; fresha c fP' |] \
            \ ==> .!a[x]. fP x .~ .!a[x]. fP' x"

    (* garbage collection *)
    n_res  "rstr P ==> .#x. (%x. P) x .~ P"
    n_rs1  "[| rstra fP ; rstr P |] ==> .#x. (%x. fP x .| P) x .~ (.#x. fP x) .| P"


  monos
    rstr_mono_res,rstra_mono_res

*)

parse_as_infix("~~",(13,"right"));; 
override_interface("~~",`PICONG`);;

let is_pic = is_binary "PICONG";;
let dest_pic = dest_binary "PICONG";;
let mk_pic = fun (p,q) -> list_mk_icomb "PICONG" [p;q];;



let [pic_refl;
     pic_sym;
     pic_trans;
     pic_out;pic_in;pic_tau;pic_match;pic_res;pic_compR;pic_plusR;pic_repl;
     pic_comp0;pic_comp_comm;pic_comp_assoc;
     pic_plus0;pic_plus_comm;pic_plus_assoc;
     pic_res0;pic_res_comm;pic_res_append;
     pic_repl_expand;
     pic_scope;
     pic_match_eq;
     pic_match_neq] =
  map (REWRITE_RULE[IMP_CONJ]) (CONJUNCTS picong_RULES);;

let [picm_refl;
     picm_sym;
     picm_trans;
     picm_out;picm_in;picm_tau;picm_match;picm_res;picm_compR;picm_plusR;picm_repl;
     picm_comp0;picm_comp_comm;picm_comp_assoc;
     picm_plus0;picm_plus_comm;picm_plus_assoc;
     picm_res0;picm_res_comm;picm_res_append;
     picm_repl_expand;
     picm_scope;
     picm_match_eq;
     picm_match_neq] =
  map (MIMP_RULE o SPEC_ALL)
    [pic_refl;
     pic_sym;
     pic_trans;
     pic_out;pic_in;pic_tau;pic_match;pic_res;pic_compR;pic_plusR;pic_repl;
     pic_comp0;pic_comp_comm;pic_comp_assoc;
     pic_plus0;pic_plus_comm;pic_plus_assoc;
     pic_res0;pic_res_comm;pic_res_append;
     pic_repl_expand;
     pic_scope;
     pic_match_eq;
     pic_match_neq] ;;

let PIC_EQ_TAC l = MESON_TAC ([pic_refl;pic_sym;pic_trans]@l);;

let pic_transL = prove(`!P Q R. P ~~ Q ==> P ~~ R ==> Q ~~ R`, PIC_EQ_TAC[]);; 
let picm_transL = (MIMP_RULE o SPEC_ALL) pic_transL;;

let pic_transR = prove(`!P Q R. Q ~~ P ==> R ~~ P ==> Q ~~ R`, PIC_EQ_TAC[]);; 
let picm_transR = (MIMP_RULE o SPEC_ALL) pic_transR;;

let (PICL_CONV:thm -> conv) =
  fun thm tm ->
    if (not (is_pic tm) or not (is_pic(concl thm))) then failwith "Not a pi-calculus congruence" else
    let thm' = thm_mk_primed_vars (frees tm) thm in
    let l,_ = (dest_pic o concl) thm' 
    and ltm,rtm = (dest_pic) tm in
    let ins = term_match [] l ltm in
    let ithm = INSTANTIATE_ALL ins thm' in
    let lr,rr = (dest_pic o concl) ithm in
    let res = mk_eq (tm,(mk_pic (rr,rtm))) in
    prove (res,
	   EQ_TAC THEN DISCH_TAC THENL [
	     rule_tac [`P`,ltm] picm_transL;
	     rule_tac [`P`,rr] picm_transL ] THENL [
	     ACCEPT_TAC ithm;
	     assumption;
	     rule picm_sym THEN ACCEPT_TAC ithm;
	     assumption]);;

let PICL = CONV_RULE o PICL_CONV;;

let (PICR_CONV:thm -> conv) =
  fun thm tm ->
    if (not (is_pic tm) or not (is_pic(concl thm))) then failwith "Not a pi-calculus congruence" else
    let thm' = thm_mk_primed_vars (frees tm) thm in
    let l,_ = (dest_pic o concl) thm' 
    and ltm,rtm = (dest_pic) tm in
    let ins = term_match [] l rtm in
    let ithm = INSTANTIATE_ALL ins thm' in
    let lr,rr = (dest_pic o concl) ithm in
    let res = mk_eq (tm,(mk_pic (ltm,rr))) in
    prove (res,
	   EQ_TAC THEN DISCH_TAC THENL [
	     rule_tac [`P`,rtm] picm_transR;
	     rule_tac [`P`,rr] picm_transR ] THENL [
	     assumption;
	     rule picm_sym THEN ACCEPT_TAC ithm;
	     assumption;
	     ACCEPT_TAC ithm]);;

let PICR = CONV_RULE o PICR_CONV;;

PICL_CONV picm_comp_comm `(Comp Zero n) ~~ n`;;
PICL picm_comp_comm picm_comp0;;
PICR_CONV picm_comp_comm `n ~~ (Comp Zero n)`;;

ONCE_DEPTH_CONV (PICR_CONV picm_comp_comm) `!n. n ~~ (Comp Zero n)`;;
ONCE_DEPTH_CONV (PICR_CONV picm_comp_comm) `!n. Q ~~ (Comp Zero n)`;;
ONCE_DEPTH_CONV (PICR_CONV picm_comp_comm) `!n. Q ~~ (Comp Zero n)`;;
ONCE_DEPTH_CONV (PICR_CONV picm_comp0) `Comp n (Comp n Zero) ~~ Q`;;
`(p <=> p') ==> (p' ==> (q <=> q')) ==> (p /\ q <=> p' /\ q')`
`(p <=> p') ==> (p' ==> (q <=> q')) ==> (p ==> q <=> p' ==> q')`

let xtm = `(Comp Zero n) ~~ n`;;
SIMP_CONV[pic_comp0] `(Comp Zero n) ~~ n`;;
PIC_SIMP_CONV[pic_comp0;pic_refl;pic_sym;pic_trans] `(Comp n Zero) ~~ Q`;;
SIMP_CONV[pic_comp0;pic_congL] `(Comp n Zero) ~~ Q`;;

let pic_comp0L = prove( `Comp P Zero ~~ Q <=> P ~~ Q`, PIC_EQ_TAC [pic_comp0]);;
SIMP_CONV[pic_comp0L] `(Comp n Zero) ~~ Q`;;
SIMP_CONV[pic_comp0L] `Comp n (Comp n Zero) ~~ Q`;;
PIC_SIMP_CONV[pic_comp0L;pic_out;pic_in;pic_tau;pic_match;pic_res;pic_compR;pic_plusR;pic_repl] `Comp n (Comp n Zero) ~~ Q`;;

let pic_congL = prove( `(p ~~ p') ==> (p ~~ q <=> p' ~~ q)`, PIC_EQ_TAC []);;
let pic_congL = prove( `(p ~~ p') ==> (q ~~ q') ==> (p ~~ q <=> p' ~~ q')`, PIC_EQ_TAC []);;
let pic_congL = prove( `((p ~~ p') ==> (q ~~ q')) ==> (p ~~ q <=> p' ~~ q')`, PIC_EQ_TAC []);;

g `

let PIC_SIMP_CONV thl = SIMPLIFY_CONV ((ss_of_congs [pic_congL] (basic_ss []))) thl;;

SIMP_CONV[] `x = 1 /\ x < 2`;;
let acong = TAUT `(p <=> p') ==> (p' ==> (q <=> q')) ==> (p /\ q <=> p' /\ q')`;;
let acong = TAUT `(p ==> (q <=> q')) ==> (p /\ q <=> p /\ q')`;;
SIMPLIFY_CONV ((ss_of_congs [acong] (basic_ss []))) [] `x = 1 /\ x < 2`;;

									      g `Comp Zero P ~~ P <=> Comp P Zero ~~ P`;;
g `P ~~ Comp Zero P <=> P ~~ Comp P Zero`;;
e (	   EQ_TAC THEN DISCH_TAC THENL [
	     rule_tac [`P`,`Comp Zero P`] picm_transR;
	     rule_tac [`P`,`Comp P Zero` ] picm_transR ]);;
e (	   EQ_TAC THEN DISCH_TAC THENL [
	     rule_tac [`P`,`Comp P Zero`] picm_transL;
	     rule_tac [`P`,`Comp Zero P` ] picm_transL ]);;

e (EQ_TAC THEN DISCH_TAC);;
e (rule_tac [`P`,`Comp Zero P`] pic_rtransL);;
e (rule (SPEC_ALL pic_comp_comm));;
e assumption;;
e (rule_tac [`P`,`Comp P Zero`] pic_rtransL);;
e (rule picm_sym);;
e (rule (SPEC_ALL pic_comp_comm));;
e assumption;;


b();;

g `P ~~ Q ===> P ~~ R ===> Q ~~ R`;;
e MIMP_TAC;;
e (REPEAT DISCH_TAC);;
e (rule_tac [`Q`,`P`] pic_trans THEN simp[pic_sym]);;
e (erule pic_sym);;
e assumption;;
b();;

e (SIMP_TAC[pic_refl;
     pic_sym;
     pic_trans]);;
e (MESON_TAC[pic_refl;
     pic_sym;
     pic_trans]);;
PICL_CONV picm_comp_comm `(Comp Zero n) ~~ n`;;
