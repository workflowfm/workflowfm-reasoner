#cd "/home/kane/HOL_Light";;
#cd "/afs/inf.ed.ac.uk/user/s06/s0681691/HOL_Light";;

needs (!serv_dir ^ "procs.ml");;
needs (!serv_dir ^ "tactics.ml");;
loads "services/make.ml";;
loads "services/dev/make.ml";;

mk_llservice "P" `(' (NEG A <> a) ^ ' ((X ** Y) <> out))`;;
let mk_atomic_service = mk_llservice;;

mk_atomic_service "SelectLength" `(' (NEG HC <> slh) ^ ' (NEG WK <> slw) ^ ' (LC <> sll))`;;
mk_atomic_service "Cm2Inch" `(' (NEG LC <> cic) ^ ' (LI <> cii))`;;
mk_atomic_service "Usd2Nok" `(' (NEG PU <> unu) ^ ' (PN <> unn))`;;
mk_atomic_service "SelectModel" `(' (NEG PL <> smp) ^ ' (NEG SL <> sms) ^ ' ((BR ** MO) <> smo))`;;
mk_atomic_service "SelSki" `(' (NEG BR <> ssb) ^ ' (NEG MO <> ssm) ^ ' (NEG LI <> ssl) ^ ' ((PU ++ EXE) <> sso))`;;


compose "TENSOR" "SelectLength" "" "Cm2Inch" "" "[Step1]";;

compose "JOIN" "SelectLength" "" "Cm2Inch" "" "[Step1]";;
compose "JOIN" "[Step1]" "" "SelSki" "" "[Step2]";;
compose "JOIN" "SelectModel" "" "[Step2]" "" "[Step3]";;
compose "JOIN" "[Step3]" "" "Usd2Nok" "" "[Step4]";;
store_service "Ski" "[Step4]";;

compose "JOIN" "SelectLength" "" "Cm2Inch" "" "[Step5]";;
compose "JOIN" "[Step1]" "" "SelSki" "" "[Step6]";;
compose "JOIN" "SelectModel" "" "[Step2]" "" "[Step7]";;
compose "JOIN" "[Step3]" "" "Usd2Nok" "" "[Step8]";;


Composition.rename "[Step4]" "[Step1821]";;
compose "JOIN" "SelectModel" "" "[Step4]" "" "[Step5]";;


Service.rename "Usd2Nok" "Usd3Nok";;
Composition.get_all();;
Composition.names();;

Service.get "Usd3Nok";;
Service.get "Ski";;
verify_process "Ski";;
Service.get "Ski";;

get_ordered_ancestors "Ski";;


let mytarget = `?P x y z w t. |-- (' (NEG PL <> x) ^ ' (NEG SL <> y) ^ ' (NEG HC <> z) ^ ' (NEG WK <> w) ^ ' ((PN ++ EXE) <> t)) P`;;

clear_available_services();;
map add_available_service ["SelectLength";"Cm2Inch";"Usd2Nok";"SelectModel";"SelSki"];;

gs mytarget;;
e (FIRST_ASSUM (FIRST_JOIN_TAC `LC:LinProp`));;
e (FIRST_ASSUM (FIRST_JOIN_TAC `LI:LinProp`));;
e (FIRST_ASSUM (FIRST_JOIN_TAC `BR:LinProp`));;
e (FIRST_ASSUM (FIRST_JOIN_TAC `PU:LinProp`));;
ellma();;
top_thm();;
instantiate ((snd o fst3 o hd o p) ()) `P:(num)Agent`;;
let qqterm = it;;

gs mytarget;;
e (LABEL_JOIN_TAC "SelectLength" "Cm2Inch" `LC:LinProp`);;
e (LABEL_JOIN_TAC "Cm2Inch" "SelSki" `LI:LinProp`);;
e (LABEL_JOIN_TAC "SelectModel" "SelSki"`BR:LinProp`);;
e (LABEL_JOIN_TAC "SelSki_7" "Usd2Nok_0" `PU:LinProp`);;
ellma();;
top_thm();;
instantiate ((snd o fst3 o hd o p) ()) `P:(num)Agent`;;
let qqterm = it;;

gs `?G . G`;;
gs mytarget;;
ell (LABEL_JOIN_TAC "SelectLength" "Cm2Inch");;
ell (LABEL_JOIN_TAC "Cm2Inch" "SelSki");;
ell (LABEL_JOIN_TAC "SelectModel" "SelSki");;
ell (LABEL_JOIN_TAC "SelSki_7" "Usd2Nok_0");;
ellma();;

let qqthm = top_thm();;
let qqres = inst_concl (top_inst()) (concl qqthm);;
let qqtermski = rand qqres;;

let qqthm = top_thm();;
instantiate (top_inst (p())) `P:(num)Agent`;;
instantiate (top_inst ()) ((snd o strip_exists) mytarget);;
let qqtermski = it;;

PI_SUBN1_RED qqtermski;;


clear_available_services();;
gs `?G . G`;;
map (add_service_assum) ["SelectLength";"Cm2Inch";"Usd2Nok";"SelectModel";"SelSki"];;
ell (LABEL_JOIN_TAC "SelectLength" "Cm2Inch");;
ell (LABEL_JOIN_TAC "Cm2Inch" "SelSki");;
ell (LABEL_JOIN_TAC "SelectModel" "SelSki");;
ell (LABEL_JOIN_TAC "SelSki_7" "Usd2Nok_0");;
ellma();;
let qqthm = top_thm();;
let qqres = inst_concl (top_inst()) (concl qqthm);;
let qqtermski = rand qqres;;


let qqreduce pi = 
  let pi' = vsubst (get_chanmap_inv()) pi in
  let chanmap,ipi = fresh_pichans pi' in
  let agentpaths,piex = INST_AGENTS ipi [] (!defined_agents) in
  let thm = PISUBN1_CONV piex in
  let res = UNINST_AGENTS ((rhs o concl) thm) agentpaths in
    chanmap,res;;

let skichans,qqski = qqreduce qqtermski;;

let qqcll = ((instantiate (top_inst())) o snd o strip_exists o concl o UNDISCH_ALL) qqthm;; 
let qqcll' = (snd o dest_comb o fst o dest_comb) qqcll;;

gs mytarget;;
e (REPEAT DISCH_TAC);;
e (REPEAT META_EXISTS_TAC);;
e (llrule_tac [(`C`,`((BR ** MO) ** LI)`);(`D`,`' ((PN ++ EXE) <> t)`)] ll_cut);;

e (REWRITE_TAC[NEG_TIMES]);;
e (llrule_tac [(`C`,`(PU ++ EXE)`);(`D`,`' ((PN ++ EXE) <> t)`)] ll_cut);;

e (REWRITE_TAC[NEG_PLUS]);;
e (llrule ll_with);;
e (llrule ll_plus1);;
ellma ();;
e (llrule ll_plus2);;
e (llrule_tac [`A`,`EXE`] ll_id);;

e (llrule ll_par);;
e (llrule ll_par);;
ellma ();;

e (llrule_tac [(`D`,`' (NEG HC <> z)^' (NEG WK <> w)`)] ll_times);;
ellma ();;
e (llrule_tac [(`C`,`LC:LinProp`);(`D`,`' (LI <> y8)`)] ll_cut);;
ellma ();;
ellma ();;

top_thm();;
p();;
hd it;;
fst3 it;;
let qqinst = snd it;;
instantiate qqinst `P:(num)Agent`;;
let qqterm = it;;

PI_SUBN1_RED qqterm;;

map (instantiate (snd it)) (fst it);;



`Res [z1]
    (Comp
     (SUBN1
      (Res [smo; cii]
      (Out x1 [smo; cii]
      (Comp SelectModel
      (Res [z3]
      (Comp (SUBN1 SelectLength (sll,z3)) (SUBN1 Cm2Inch (cic,z3)))))))
     (x1,z1))
    (SUBN1
     (Res [z4]

     (Comp (SUBN1 (In y1 [x5; ssl] (In x5 [ssb; ssm] SelSki)) (sso,z4))
     (SUBN1
      (Res [u7; v7]
      (Out y4 [u7; v7]
      (Plus (In u7 [unu] (Res [unn] (In t [u8; v8] (Out u8 [unn] Usd2Nok))))
      (In v7 [y7]
      (Res [y9]
      (In t [u9; v9] (Out v9 [y9] (In y7 [a10] (Out y9 [a10] Zero)))))))))
     (y4,z4))))
    (y1,z1)))`


let qqterm2 = `Res [z1]
   (Comp
    (SUBN1
     (Res [smo; cii]
     (Out x1 [smo; cii]
     (Comp Zero
     (Res [z3] (Comp (SUBN1 Zero (sll,z3)) (SUBN1 Zero (cic,z3)))))))
    (x1,z1))
   (SUBN1
    (Res [z4]
    (Comp (SUBN1 (In y1 [x5; ssl] (In x5 [ssb; ssm] Zero)) (sso,z4))
    (SUBN1
     (Res [u7; v7]
     (Out y4 [u7; v7]
     (Plus (In u7 [unu] (Res [unn] (In t [u8; v8] (Out u8 [unn] Zero))))
     (In v7 [y7]
     (Res [y9]
     (In t [u9; v9] (Out v9 [y9] (In y7 [a10] (Out y9 [a10] Zero)))))))))
    (y4,z4))))
   (y1,z1)))`;;


let qqterm3 = `Res [z1]
  (Comp
    (SUBN1
     (Res [smo; cii]
     (Out x1 [smo; cii]
     (Comp Zero
     (Res [z3] (Comp (SUBN1 Zero (sll,z3)) (SUBN1 Zero (cic,z3)))))))
    (x1,z1))
   (SUBN1
    (Res [z4]
    (Comp (SUBN1 (In y1 [x5; ssl] (In x5 [ssb; ssm] Zero)) (sso,z4))
    (SUBN1
     (Res [u7; v7]
     (Out y4 [u7; v7]
     (Plus (In u7 [unu] (Res [unn] (In t [u8; v8] (Out u8 [unn] Zero))))
     (In v7 [y7]
     (Res [y9]
     (In t [u9; v9] (Out v9 [y9] (In y7 [a10] (Out y9 [a10] (
SelectModel (br,mo,pl,sl,y4,smo_a,smo_b,smp,sms)
))))))))))
    (y4,z4))))
   (y1,z1)))`;;



let qqterm4 =  `Res [z1]
   (Comp
     (Res [smo; cii]
     (Out z1 [smo; cii]
     (Comp (SelectModel (br,mo,pl,sl,smo,smo_a,smo_b,smp,sms))
     (Res [z3]
     (Comp (SelectLength (hc,lc,slh,z3,slw,wk))
     (Cm2Inch (z3,cii,lc,li)) )))))
    (Res [z4]
    (Comp
      (In z1 [x5; ssl]
      (In x5 [ssb; ssm]
      (SelSki (br,li,mo,pu,ssb,ssl,ssm,z4,sso_u,sso_v,sso_x,sso_y))))
     (Res [u7; v7]
     (Out z4 [u7; v7]
     (Plus
      (In u7 [unu]
      (Res [unn] (In t [u8; v8] (Out u8 [unn] (Usd2Nok (pn,pu,unn,unu))))))
     (In v7 [y7]
     (Res [y9]
     (In t [u9; v9] (Out v9 [y9] (In y7 [a10] (Out y9 [a10] Zero)))))))))
    )))`;;

let tm  = `(SUBN1
     (Res [smo; cii]
     (Out x1 [smo; cii]
     (Comp Zero
     (Res [z3] (Comp (SUBN1 Zero (sll,z3)) (SUBN1 Zero (cic,z3)))))))
    (x1,z1))`;;

let myservices = [
`|-- (' (NEG A <> ra) ^ ' ((B ++ E) <> ro)) R`;
`|-- (' (NEG B <> sa) ^ ' (NEG C <> sc) ^ ' (D <> sd)) S`;
`|-- (' (NEG G <> wg) ^ ' (C <> wc)) W`
];;

let mytarget = `?X x y t. |-- (' (NEG A <> x) ^ ' (NEG G <> y) ^ ' ((D ++ (C ** E)) <> t)) X`;;

let mygoal = itlist (fun x y -> mk_imp (x,y)) myservices mytarget;;

g mygoal;;
e (REPEAT DISCH_TAC);;
e (REPEAT META_EXISTS_TAC);;

e (llrule_tac [(`C1`,`((C ** B) ++ (C ** E))`);(`G1`,`' (NEG A <> x) ^ ' (NEG G <> y)`)] (number_vars_thm 1 ll_cut));;
e (llrule (number_vars_thm 2 llleft_times_plus_distrib));;
e (llrule_tac [`G3`,`' ((NEG G) <> y)`] (number_vars_thm 3 ll_times));;
e (llmeta_assumption [`(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(X:(num)Agent)`; `(x:num)`; `(y:num)`; `(t:num)`]);;
e (llmeta_assumption [`(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(X:(num)Agent)`; `(x:num)`; `(y:num)`; `(t:num)`]);;

e (REWRITE_TAC [NEG_PLUS]);;
e (llrule (number_vars_thm 4 ll_with));;

e (llrule (number_vars_thm 5 ll_plus1));;
e (REWRITE_TAC [NEG_TIMES]);;
e (llrule (number_vars_thm 6 ll_par));;
e (llmeta_assumption [`(x6:num)`; `(y6:num)`; `(P6:(num)Agent)`; `(x5:num)`; `(P5:(num)Agent)`; `(x4:num)`; `(P4:(num)Agent)`; `(y4:num)`; `(Q4:(num)Agent)`; `(x3:num)`; `(P3:(num)Agent)`; `(y3:num)`; `(Q3:(num)Agent)`; `(x2:num)`; `(P2:(num)Agent)`; `(x1:num)`; `(P1:(num)Agent)`; `(y1:num)`; `(Q1:(num)Agent)`; `(X:(num)Agent)`; `(x:num)`; `(y:num)`; `(t:num)`]);;

e (llrule (number_vars_thm 7 ll_plus2));;
e (REWRITE_TAC [NEG_TIMES]);;
e (llrule (number_vars_thm 8 ll_par));;
e (llrule (number_vars_thm 9 ll_times));;
e (llrule_tac [`A10`,`C`] (number_vars_thm 10 ll_id));;
e (llrule_tac [`A11`,`E`] (number_vars_thm 11 ll_id));;

e (llrule_tac [`A8`,`C ** E`] (number_vars_thm 8 ll_id));;

top_thm();;
p();;
hd it;;
fst3 it;;
let qqinst = snd it;;
instantiate qqinst `P:(num)Agent`;;
let qqterm = it;;



clear_available_services();;

	 
mk_llservice "HomeDir" `(' (NEG HC <> hdc) ^ ' (HL <> hdl))`;;
mk_llservice "CriminalService" `(' (NEG RE <> csr) ^ ' (CL <> csl))`;;
mk_llservice "HouseAlert" `(' (NEG HL <> hal) ^ ' (NEG CL <> hac) ^ ' (NEG DCL <> had) ^ ' ((HAID ** HDE ** HTID) <> hao))`;;
mk_llservice "EstateAgentOffer" `(' (NEG HAID <> eoi) ^ ' (NEG AC <> eoc) ^ ' (HO <> eoo))`;;
mk_llservice "Client" `(' (NEG HDE <> cld) ^ ' (NEG HO <> clho) ^ ' ((AO ++ RO) <> clo))`;;
mk_llservice "MortgageService" `(' (NEG CI <> mi) ^ ' ((PA ++ EXM) <> mo))`;;
mk_llservice "EstateAgentSeller" `(' (NEG PA <> esa) ^ ' (NEG AO <> eso) ^ ' (CO <> esc))`;;
mk_llservice "TitleSearch" `(' (NEG HTID <> tsi) ^ ' ((HT ** (HI ++ HIID)) <> tso))`;;
mk_llservice "HomeIns" `(' (NEG HIID <> hid) ^ ' (HI <> hii))`;;
mk_llservice "Settlement" `(' (NEG HT <> set) ^ ' (NEG CO <> sec) ^ ' (NEG HI <> sei) ^ ' (S <> ses))`;;



let mytarget = `?P x y z w v t. |-- (' (NEG HC <> x) ^ ' (NEG RE <> y) ^ ' (NEG DCL <> z) ^ ' (NEG AC <> w) ^ ' (NEG CI <> v) ^ ' ((S ++ ((HT ** HI) ** ((EXM ** AO) ++ ((PA ++ EXM) ** RO)))) <> t)) P`;;

let mytarget = `?EXE P x y z w v t. |-- (' (NEG HC <> x) ^ ' (NEG RE <> y) ^ ' (NEG DCL <> z) ^ ' (NEG AC <> w) ^ ' (NEG CI <> v) ^ ' ((S ++ EXE) <> t)) P`;;

let mytarget = `?EXF EXE P x y z w v t. |-- (' (NEG HC <> x) ^ ' (NEG RE <> y) ^ ' (NEG DCL <> z) ^ ' (NEG AC <> w) ^ ' (NEG CI <> v) ^ ' (((S ++ EXE) ++ EXF) <> t)) P`;;


gs mytarget;;
e (LABEL_JOIN_TAC "CriminalService" "HouseAlert");;
e (LABEL_JOIN_TAC "HomeDir" "HouseAlert");;
e (LABEL_JOIN_TAC "MortgageService" "EstateAgentSeller");;
e (LABEL_JOIN_TAC "Client" "EstateAgentSeller");;
e (LABEL_JOIN_TAC "EstateAgentOffer" "EstateAgentSeller");;

e (LABEL_JOIN_TAC "TitleSearch" "HomeIns");;
e (LABEL_JOIN_TAC "HomeIns" "Settlement");;

e (LABEL_JOIN_TAC "EstateAgentSeller" "Settlement");;

e (LABEL_JOIN_TAC "HouseAlert" "Settlement");;

ellma ();;
top_thm();;

store_service "HomeComp";;

instantiate (top_inst ()) `P:NAgent`;;
let qqterm = it;;

gs mytarget;;
e (LABEL_JOIN_TAC "CriminalService" "HouseAlert" `CL:LinProp`);;
e (LABEL_JOIN_TAC "HomeDir" "HouseAlert" `HL:LinProp`);;
e (LABEL_JOIN_TAC "MortgageService" "EstateAgentSeller" `PA:LinProp`);;
e (LABEL_JOIN_TAC "Client" "EstateAgentSeller" `AO:LinProp`);;
e (LABEL_JOIN_TAC "EstateAgentOffer" "EstateAgentSeller" `HO:LinProp`);;

e (LABEL_JOIN_TAC "TitleSearch" "HomeIns" `HIID:LinProp`);;
e (LABEL_JOIN_TAC "HomeIns" "Settlement" `HI:LinProp`);;

e (LABEL_JOIN_TAC "EstateAgentSeller" "Settlement" `CO:LinProp`);;

e (LABEL_JOIN_TAC "HouseAlert" "Settlement" `HTID:LinProp`);;

ellma ();;
top_thm();;

instantiate (top_inst ()) `P:NAgent`;;
b();;

`|--
      ((' (NEG HC <> hdc)^' (NEG RE <> csr)^' (NEG DCL <> had))^
       ' (NEG AC <> eoc)^
       ' (NEG CI <> mi)^
       ' (((S ++ (HTID ** AO ** EXM)) ++ (HTID ** CI ** RO)) <> y50))

|--
 (' (NEG HC <> x)^
  ' (NEG RE <> y)^
  ' (NEG DCL <> z)^
  ' (NEG AC <> w)^
  ' (NEG CI <> v)^
  ' ((S ++ EXE) <> t))
 P`

let mygoal = itlist (fun x y -> mk_imp (x,y)) myservices mytarget;;


g `?P x y . |-- (' ((NEG ((EXM ** AO) ++ ((PA ++ EMX) ** RO))) <> x) ^ ' (((EXM ** AO) ++ ((PA ++ EMX) ** RO)) <> y)) P`;;
e (REPEAT META_EXISTS_TAC);;

gll `|-- (' ((NEG ((EXM ** AO) ++ ((PA ++ EMX) ** RO))) <> x) ^ ' (((EXM ** AO) ++ ((PA ++ EMX) ** RO)) <> y)) (Res [u1; v1]
    (Out x [ua; va]
    (Plus
     (In ua [xa]
     (Res [xb]
     (In y [ub; vb]
     (Out ub [xb]
     (In xa [xc; yc]
     (Res [xd; yd]
     (Out xb [xd; yd]
     (Comp (In xc [ae] (Out xd [ae] Zero)) (In yc [bufa] (Out yd [bufa] Zero))))))))))
    (In va [ya]
    (In ya [xg; yg]
    (Res [yo]
    (In y [uo; vo]
    (Out vo [yo]
    (Res [xh; yh]
    (Out yo [xh; yh]
    (Comp
     (Res [ui; vi]
     (Out xg [ui; vi]
     (Plus
      (In ui [xi]
      (Res [xj]
      (In xh [uj; vj] (Out uj [xj] (In xi [bufb] (Out xj [bufb] Zero))))))
     (In vi [yi]
     (Res [yl]
     (In xh [ul; vl] (Out vl [yl] (In yi [bufc] (Out yl [bufc] Zero)))))))))
    (In yg [an] (Out yh [an] Zero))))))))))))
)`;;


e (REWRITE_TAC[NEG_TIMES;NEG_PLUS]);;
e (llrule (number_vars_thm 1 ll_with));;
e (llrule (number_vars_thm 2 ll_plus1));;
e (llrule (number_vars_thm 3 ll_par));;
e (llrule (number_vars_thm 4 ll_times));;
e (llrule_tac [`A5`,`EXM`] (number_vars_thm 5 ll_id));;
e (llrule_tac [`A6`,`AO`] (number_vars_thm 6 ll_id));;
e (llrule (number_vars_thm 7 ll_par));;
e (llrule (number_vars_thm 15 ll_plus2));;
e (llrule (number_vars_thm 8 ll_times));;
e (llrule (number_vars_thm 9 ll_with));;
e (llrule (number_vars_thm 10 ll_plus1));;
e (llrule_tac [`A11`,`PA`] (number_vars_thm 11 ll_id));;
e (llrule (number_vars_thm 12 ll_plus2));;
e (llrule_tac [`A13`,`EMX`] (number_vars_thm 13 ll_id));;
e (llrule_tac [`A14`,`RO`] (number_vars_thm 14 ll_id));;

let lemma_E = top_thm();;

p();;
hd it;;
fst3 it;;
map (instantiate (snd it)) (fst it);;





gll mygoal;;
e (REPEAT DISCH_TAC);;
e (REPEAT META_EXISTS_TAC);;

e (llrule_tac [(`C16`,`((HT ** HI) ** CO) ++ ((HT ** HI) ** ((EXM ** AO) ++ ((PA ++ EXM) ** RO)))`);(`D16`,`' ((S ++ ((HT ** HI) ** ((EXM ** AO) ++ ((PA ++ EXM) ** RO)))) <> t)`)] (number_vars_thm 16 ll_cut));;

(* D *)
e (llrule (number_vars_thm 17 llleft_times_plus_distrib));;
e (REWRITE_TAC[NEG_TIMES]);;
e (llrule (number_vars_thm 53 ll_par));;
e (llrule (number_vars_thm 54 ll_times));;
e (llrule_tac [`A55`,`HT`] (number_vars_thm 55 ll_id));;
e (llrule_tac [`A56`,`HI`] (number_vars_thm 56 ll_id));;
e (llrule_tac [`A57`,`CO`] (number_vars_thm 57 ll_id));;
e (REWRITE_TAC[NEG_PLUS]);;
e (llrule (number_vars_thm 58 ll_with));;
e (llrule (number_vars_thm 59 ll_plus1));;
e (REWRITE_TAC[NEG_TIMES]);;
e (llrule (number_vars_thm 60 ll_par));;
e (llrule (number_vars_thm 61 ll_times));;
e (llrule_tac [`A62`,`EXM`] (number_vars_thm 62 ll_id));;
e (llrule_tac [`A63`,`AO`] (number_vars_thm 63 ll_id));;
e (llrule (number_vars_thm 64 ll_plus2));;
e (REWRITE_TAC[NEG_TIMES]);;
e (llrule (number_vars_thm 65 ll_par));;
e (llrule (number_vars_thm 66 ll_times));;
e (REWRITE_TAC[NEG_PLUS]);;
e (llrule (number_vars_thm 67 ll_with));;
e (llrule (number_vars_thm 68 ll_plus1));;
e (llrule_tac [`A69`,`PA`] (number_vars_thm 69 ll_id));;
e (llrule (number_vars_thm 70 ll_plus2));;
e (llrule_tac [`A71`,`EXM`] (number_vars_thm 71 ll_id));;
e (llrule_tac [`A72`,`RO`] (number_vars_thm 72 ll_id));;

(* Cut with (1) *)
e (llrule_tac [(`C18`,`(HAID ** HDE ** HTID)`);(`D18`,`' (NEG AC <> w) ^ ' (NEG CI <> v) ^ ' (((HT ** HI) ** (CO ++ (EXM ** AO) ++ ((PA ++ EXM) ** RO))) <> x17)`)] (number_vars_thm 18 ll_cut));;

(* 1 *)
e (llrule_tac [(`C19`,`(HL ** CL)`);(`G19`,`' (NEG HC <> x) ^ ' (NEG RE <> y)`)] (number_vars_thm 19 ll_cut));;
e (llrule (number_vars_thm 20 ll_times));;


(* e (llrule_tac [(`C20`,`(HL ** CL)`);(`G20`,`' (NEG HC <> x) ^ ' (NEG RE <> y)`)] (number_vars_thm 19 ll_cut));; *)
e (llmeta_assumption [`(x20:num)`; `(P20:(num)Agent)`; `(y20:num)`; `(Q20:(num)Agent)`; `(x19:num)`; `(P19:(num)Agent)`; `(y19:num)`; `(Q19:(num)Agent)`; `(x18:num)`; `(P18:(num)Agent)`; `(y18:num)`; `(Q18:(num)Agent)`; `(x17:num)`; `(P17:(num)Agent)`; `(x16:num)`; `(P16:(num)Agent)`; `(y16:num)`; `(Q16:(num)Agent)`; `(P:(num)Agent)`; `(x:num)`; `(y:num)`; `(z:num)`; `(w:num)`; `(v:num)`; `(t:num)`]);;
e (llmeta_assumption [`(x20:num)`; `(P20:(num)Agent)`; `(y20:num)`; `(Q20:(num)Agent)`; `(x19:num)`; `(P19:(num)Agent)`; `(y19:num)`; `(Q19:(num)Agent)`; `(x18:num)`; `(P18:(num)Agent)`; `(y18:num)`; `(Q18:(num)Agent)`; `(x17:num)`; `(P17:(num)Agent)`; `(x16:num)`; `(P16:(num)Agent)`; `(y16:num)`; `(Q16:(num)Agent)`; `(P:(num)Agent)`; `(x:num)`; `(y:num)`; `(z:num)`; `(w:num)`; `(v:num)`; `(t:num)`]);;

e (REWRITE_TAC[NEG_TIMES]);;
e (llrule (number_vars_thm 21 ll_par));;
e (llmeta_assumption [`(x21:num)`; `(y21:num)`; `(P21:(num)Agent)`; `(x20:num)`; `(P20:(num)Agent)`; `(y20:num)`; `(Q20:(num)Agent)`; `(x19:num)`; `(P19:(num)Agent)`; `(y19:num)`; `(Q19:(num)Agent)`; `(x18:num)`; `(P18:(num)Agent)`; `(y18:num)`; `(Q18:(num)Agent)`; `(x17:num)`; `(P17:(num)Agent)`; `(x16:num)`; `(P16:(num)Agent)`; `(y16:num)`; `(Q16:(num)Agent)`; `(P:(num)Agent)`; `(x:num)`; `(y:num)`; `(z:num)`; `(w:num)`; `(v:num)`; `(t:num)`]);;

(* Estate Agent Offer *)
e (REWRITE_TAC[NEG_TIMES]);;
e (llrule (number_vars_thm 22 ll_par));;
e (llrule (number_vars_thm 23 ll_par));;
(* ll_times ==> A *)
e (llrule_tac [`G24`,`' (NEG HTID <> y23)`] (number_vars_thm 24 ll_times));;

(* A *)
e (llrule_tac [(`C25`,`HT ** (HI ++ HIID)`);(`G25`,`' (NEG HTID <> y23)`)] (number_vars_thm 25 ll_cut));;

e (llmeta_assumption [`(x25:num)`; `(P25:(num)Agent)`; `(y25:num)`; `(Q25:(num)Agent)`; `(x24:num)`; `(P24:(num)Agent)`; `(y24:num)`; `(Q24:(num)Agent)`; `(x23:num)`; `(y23:num)`; `(P23:(num)Agent)`; `(x22:num)`; `(y22:num)`; `(P22:(num)Agent)`; `(x21:num)`; `(y21:num)`; `(P21:(num)Agent)`; `(x20:num)`; `(P20:(num)Agent)`; `(y20:num)`; `(Q20:(num)Agent)`; `(x19:num)`; `(P19:(num)Agent)`; `(y19:num)`; `(Q19:(num)Agent)`; `(x18:num)`; `(P18:(num)Agent)`; `(y18:num)`; `(Q18:(num)Agent)`; `(x17:num)`; `(P17:(num)Agent)`; `(x16:num)`; `(P16:(num)Agent)`; `(y16:num)`; `(Q16:(num)Agent)`; `(P:(num)Agent)`; `(x:num)`; `(y:num)`; `(z:num)`; `(w:num)`; `(v:num)`; `(t:num)`]);;

e (REWRITE_TAC[NEG_TIMES]);;
e (llrule (number_vars_thm 26 ll_par));;
e (llrule (number_vars_thm 27 ll_times));;
e (llrule_tac [`A28`,`HT`] (number_vars_thm 28 ll_id));;

e (REWRITE_TAC[NEG_PLUS]);;
e (llrule (number_vars_thm 52 ll_with));;
e (llrule (number_vars_thm 29 ll_id));;
e (llmeta_assumption [`(x52:num)`; `(P52:(num)Agent)`; `(y52:num)`; `(Q52:(num)Agent)`; `(x27:num)`; `(P27:(num)Agent)`; `(y27:num)`; `(Q27:(num)Agent)`; `(x26:num)`; `(y26:num)`; `(P26:(num)Agent)`; `(x25:num)`; `(P25:(num)Agent)`; `(y25:num)`; `(Q25:(num)Agent)`; `(x24:num)`; `(P24:(num)Agent)`; `(y24:num)`; `(Q24:(num)Agent)`; `(x23:num)`; `(y23:num)`; `(P23:(num)Agent)`; `(x22:num)`; `(y22:num)`; `(P22:(num)Agent)`; `(x21:num)`; `(y21:num)`; `(P21:(num)Agent)`; `(x20:num)`; `(P20:(num)Agent)`; `(y20:num)`; `(Q20:(num)Agent)`; `(x19:num)`; `(P19:(num)Agent)`; `(y19:num)`; `(Q19:(num)Agent)`; `(x18:num)`; `(P18:(num)Agent)`; `(y18:num)`; `(Q18:(num)Agent)`; `(x17:num)`; `(P17:(num)Agent)`; `(x16:num)`; `(P16:(num)Agent)`; `(y16:num)`; `(Q16:(num)Agent)`; `(P:(num)Agent)`; `(x:num)`; `(y:num)`; `(z:num)`; `(w:num)`; `(v:num)`; `(t:num)`]);;


(* Back to build C *)
e (llrule_tac [(`C30`,`HO`);(`G30`,`' (NEG AC <> w) ^ ' (NEG HAID <> x22)`)] (number_vars_thm 30 ll_cut));;
e (llmeta_assumption [`(x30:num)`; `(P30:(num)Agent)`; `(y30:num)`; `(Q30:(num)Agent)`; `(x28:num)`; `(P28:(num)Agent)`; `(y28:num)`; `(Q28:(num)Agent)`; `(x27:num)`; `(P27:(num)Agent)`; `(y27:num)`; `(Q27:(num)Agent)`; `(x26:num)`; `(y26:num)`; `(P26:(num)Agent)`; `(x25:num)`; `(P25:(num)Agent)`; `(y25:num)`; `(Q25:(num)Agent)`; `(x24:num)`; `(P24:(num)Agent)`; `(y24:num)`; `(Q24:(num)Agent)`; `(x23:num)`; `(y23:num)`; `(P23:(num)Agent)`; `(x22:num)`; `(y22:num)`; `(P22:(num)Agent)`; `(x21:num)`; `(y21:num)`; `(P21:(num)Agent)`; `(x20:num)`; `(P20:(num)Agent)`; `(y20:num)`; `(Q20:(num)Agent)`; `(x19:num)`; `(P19:(num)Agent)`; `(y19:num)`; `(Q19:(num)Agent)`; `(x18:num)`; `(P18:(num)Agent)`; `(y18:num)`; `(Q18:(num)Agent)`; `(x17:num)`; `(P17:(num)Agent)`; `(x16:num)`; `(P16:(num)Agent)`; `(y16:num)`; `(Q16:(num)Agent)`; `(P:(num)Agent)`; `(x:num)`; `(y:num)`; `(z:num)`; `(w:num)`; `(v:num)`; `(t:num)`]);;

(* C *)
e (llrule_tac [(`C31`,`(PA ** AO) ++ (EXM ** AO) ++ ((PA ++ EXM) ** RO)`);(`G31`,`' (NEG HO <> y30) ^ ' (NEG CI <> v) ^  ' (NEG HDE <> x23)`)] (number_vars_thm 31 ll_cut));;

e (llrule (number_vars_thm 32 llright_times_plus_distrib_plus));;
e (llrule_tac [`A73`,`AO`] (number_vars_thm 73 ll_id));;
e (llrule_tac [`A74`,`PA`] (number_vars_thm 74 ll_id));;
e (llrule_tac [`A75`,`EXM`] (number_vars_thm 75 ll_id));;
e (REWRITE_TAC[NEG_TIMES]);;
e (llrule (number_vars_thm 76 ll_par));;
e (llrule (number_vars_thm 77 ll_times));;
e (REWRITE_TAC[NEG_PLUS]);;
e (llrule (number_vars_thm 82 ll_with));;
e (llrule (number_vars_thm 83 ll_plus1));;
e (llrule_tac [`A78`,`PA`] (number_vars_thm 78 ll_id));;
e (llrule (number_vars_thm 79 ll_plus2));;
e (llrule_tac [`A80`,`EXM`] (number_vars_thm 80 ll_id));;
e (llrule_tac [`A81`,`RO`] (number_vars_thm 81 ll_id));;

e (llrule (number_vars_thm 33 llleft_times_plus_distrib));;
e (REWRITE_TAC[NEG_PLUS]);;
e (llrule (number_vars_thm 84 ll_with));;
e (llrule (number_vars_thm 85 ll_plus1));;
e (llrule_tac [`A86`,`PA`] (number_vars_thm 86 ll_id));;
e (llrule (number_vars_thm 87 ll_plus2));;
e (llrule_tac [`A88`,`EXM`] (number_vars_thm 88 ll_id));;
e (llrule_tac [`A89`,`AO`] (number_vars_thm 89 ll_id));;
e (llrule_tac [`A90`,`RO`] (number_vars_thm 90 ll_id));;


e (llrule_tac [`G34`,`' (NEG CI <> v)`] (number_vars_thm 34 ll_times));;
e (llmeta_assumption [ `(x34:num)`; `(P34:(num)Agent)`; `(y34:num)`; `(Q34:(num)Agent)`; `(x33:num)`; `(P33:(num)Agent)`; `(y32:num)`; `(P32:(num)Agent)`; `(x31:num)`; `(P31:(num)Agent)`; `(y31:num)`; `(Q31:(num)Agent)`; `(x30:num)`; `(P30:(num)Agent)`; `(y30:num)`; `(Q30:(num)Agent)`; `(x28:num)`; `(P28:(num)Agent)`; `(y28:num)`; `(Q28:(num)Agent)`; `(x27:num)`; `(P27:(num)Agent)`; `(y27:num)`; `(Q27:(num)Agent)`; `(x26:num)`; `(y26:num)`; `(P26:(num)Agent)`; `(x25:num)`; `(P25:(num)Agent)`; `(y25:num)`; `(Q25:(num)Agent)`; `(x24:num)`; `(P24:(num)Agent)`; `(y24:num)`; `(Q24:(num)Agent)`; `(x23:num)`; `(y23:num)`; `(P23:(num)Agent)`; `(x22:num)`; `(y22:num)`; `(P22:(num)Agent)`; `(x21:num)`; `(y21:num)`; `(P21:(num)Agent)`; `(x20:num)`; `(P20:(num)Agent)`; `(y20:num)`; `(Q20:(num)Agent)`; `(x19:num)`; `(P19:(num)Agent)`; `(y19:num)`; `(Q19:(num)Agent)`; `(x18:num)`; `(P18:(num)Agent)`; `(y18:num)`; `(Q18:(num)Agent)`; `(x17:num)`; `(P17:(num)Agent)`; `(x16:num)`; `(P16:(num)Agent)`; `(y16:num)`; `(Q16:(num)Agent)`; `(P:(num)Agent)`; `(x:num)`; `(y:num)`; `(z:num)`; `(w:num)`; `(v:num)`; `(t:num)`]);;
e (llmeta_assumption [ `(x34:num)`; `(P34:(num)Agent)`; `(y34:num)`; `(Q34:(num)Agent)`; `(x33:num)`; `(P33:(num)Agent)`; `(y32:num)`; `(P32:(num)Agent)`; `(x31:num)`; `(P31:(num)Agent)`; `(y31:num)`; `(Q31:(num)Agent)`; `(x30:num)`; `(P30:(num)Agent)`; `(y30:num)`; `(Q30:(num)Agent)`; `(x28:num)`; `(P28:(num)Agent)`; `(y28:num)`; `(Q28:(num)Agent)`; `(x27:num)`; `(P27:(num)Agent)`; `(y27:num)`; `(Q27:(num)Agent)`; `(x26:num)`; `(y26:num)`; `(P26:(num)Agent)`; `(x25:num)`; `(P25:(num)Agent)`; `(y25:num)`; `(Q25:(num)Agent)`; `(x24:num)`; `(P24:(num)Agent)`; `(y24:num)`; `(Q24:(num)Agent)`; `(x23:num)`; `(y23:num)`; `(P23:(num)Agent)`; `(x22:num)`; `(y22:num)`; `(P22:(num)Agent)`; `(x21:num)`; `(y21:num)`; `(P21:(num)Agent)`; `(x20:num)`; `(P20:(num)Agent)`; `(y20:num)`; `(Q20:(num)Agent)`; `(x19:num)`; `(P19:(num)Agent)`; `(y19:num)`; `(Q19:(num)Agent)`; `(x18:num)`; `(P18:(num)Agent)`; `(y18:num)`; `(Q18:(num)Agent)`; `(x17:num)`; `(P17:(num)Agent)`; `(x16:num)`; `(P16:(num)Agent)`; `(y16:num)`; `(Q16:(num)Agent)`; `(P:(num)Agent)`; `(x:num)`; `(y:num)`; `(z:num)`; `(w:num)`; `(v:num)`; `(t:num)`]);;

e (ONCE_REWRITE_TAC[NEG_PLUS]);;
e (llrule (number_vars_thm 35 ll_with));;

e (llrule (number_vars_thm 36 ll_plus1));;
e (REWRITE_TAC[NEG_TIMES]);;
e (llrule (number_vars_thm 37 ll_par));;
e (llmeta_assumption [`(x37:num)`; `(y37:num)`; `(P37:(num)Agent)`; `(x36:num)`; `(P36:(num)Agent)`; `(x35:num)`; `(P35:(num)Agent)`; `(y35:num)`; `(Q35:(num)Agent)`; `(x34:num)`; `(P34:(num)Agent)`; `(y34:num)`; `(Q34:(num)Agent)`; `(x33:num)`; `(P33:(num)Agent)`; `(y32:num)`; `(P32:(num)Agent)`; `(x31:num)`; `(P31:(num)Agent)`; `(y31:num)`; `(Q31:(num)Agent)`; `(x30:num)`; `(P30:(num)Agent)`; `(y30:num)`; `(Q30:(num)Agent)`; `(x28:num)`; `(P28:(num)Agent)`; `(y28:num)`; `(Q28:(num)Agent)`; `(x27:num)`; `(P27:(num)Agent)`; `(y27:num)`; `(Q27:(num)Agent)`; `(x26:num)`; `(y26:num)`; `(P26:(num)Agent)`; `(x25:num)`; `(P25:(num)Agent)`; `(y25:num)`; `(Q25:(num)Agent)`; `(x24:num)`; `(P24:(num)Agent)`; `(y24:num)`; `(Q24:(num)Agent)`; `(x23:num)`; `(y23:num)`; `(P23:(num)Agent)`; `(x22:num)`; `(y22:num)`; `(P22:(num)Agent)`; `(x21:num)`; `(y21:num)`; `(P21:(num)Agent)`; `(x20:num)`; `(P20:(num)Agent)`; `(y20:num)`; `(Q20:(num)Agent)`; `(x19:num)`; `(P19:(num)Agent)`; `(y19:num)`; `(Q19:(num)Agent)`; `(x18:num)`; `(P18:(num)Agent)`; `(y18:num)`; `(Q18:(num)Agent)`; `(x17:num)`; `(P17:(num)Agent)`; `(x16:num)`; `(P16:(num)Agent)`; `(y16:num)`; `(Q16:(num)Agent)`; `(P:(num)Agent)`; `(x:num)`; `(y:num)`; `(z:num)`; `(w:num)`; `(v:num)`; `(t:num)`]);;

e (llrule (number_vars_thm 38 ll_plus2));;
e (llrule (number_vars_thm 50 lemma_E));;

(* S + G above Cut with D *)
e (REWRITE_TAC[NEG_PLUS]);;
e (llrule (number_vars_thm 39 ll_with));;

e (llrule (number_vars_thm 40 ll_plus1));;
e (REWRITE_TAC[NEG_TIMES]);;
e (llrule (number_vars_thm 41 ll_par));;
e (llrule (number_vars_thm 42 ll_par));;
e (llmeta_assumption [`(x42:num)`; `(y42:num)`; `(P42:(num)Agent)`; `(x41:num)`; `(y41:num)`; `(P41:(num)Agent)`; `(x40:num)`; `(P40:(num)Agent)`; `(x39:num)`; `(P39:(num)Agent)`; `(y39:num)`; `(Q39:(num)Agent)`; `(y38:num)`; `(P38:(num)Agent)`; `(x37:num)`; `(y37:num)`; `(P37:(num)Agent)`; `(x36:num)`; `(P36:(num)Agent)`; `(x35:num)`; `(P35:(num)Agent)`; `(y35:num)`; `(Q35:(num)Agent)`; `(x34:num)`; `(P34:(num)Agent)`; `(y34:num)`; `(Q34:(num)Agent)`; `(x33:num)`; `(P33:(num)Agent)`; `(y32:num)`; `(P32:(num)Agent)`; `(x31:num)`; `(P31:(num)Agent)`; `(y31:num)`; `(Q31:(num)Agent)`; `(x30:num)`; `(P30:(num)Agent)`; `(y30:num)`; `(Q30:(num)Agent)`; `(x28:num)`; `(P28:(num)Agent)`; `(y28:num)`; `(Q28:(num)Agent)`; `(x27:num)`; `(P27:(num)Agent)`; `(y27:num)`; `(Q27:(num)Agent)`; `(x26:num)`; `(y26:num)`; `(P26:(num)Agent)`; `(x25:num)`; `(P25:(num)Agent)`; `(y25:num)`; `(Q25:(num)Agent)`; `(x24:num)`; `(P24:(num)Agent)`; `(y24:num)`; `(Q24:(num)Agent)`; `(x23:num)`; `(y23:num)`; `(P23:(num)Agent)`; `(x22:num)`; `(y22:num)`; `(P22:(num)Agent)`; `(x21:num)`; `(y21:num)`; `(P21:(num)Agent)`; `(x20:num)`; `(P20:(num)Agent)`; `(y20:num)`; `(Q20:(num)Agent)`; `(x19:num)`; `(P19:(num)Agent)`; `(y19:num)`; `(Q19:(num)Agent)`; `(x18:num)`; `(P18:(num)Agent)`; `(y18:num)`; `(Q18:(num)Agent)`; `(x17:num)`; `(P17:(num)Agent)`; `(x16:num)`; `(P16:(num)Agent)`; `(y16:num)`; `(Q16:(num)Agent)`; `(P:(num)Agent)`; `(x:num)`; `(y:num)`; `(z:num)`; `(w:num)`; `(v:num)`; `(t:num)`]);;


e (llrule (number_vars_thm 43 ll_plus2));;
e (ONCE_REWRITE_TAC[NEG_TIMES]);;
e (llrule (number_vars_thm 44 ll_par));;
e (llrule (number_vars_thm 45 ll_times));;

e (ONCE_REWRITE_TAC[NEG_TIMES]);;
e (llrule (number_vars_thm 46 ll_par));;
e (llrule (number_vars_thm 47 ll_times));;
e (llrule_tac [`A48`,`HT`] (number_vars_thm 48 ll_id));;
e (llrule_tac [`A49`,`HI`] (number_vars_thm 49 ll_id));;
e (llrule (number_vars_thm 51 lemma_E));;

top_thm();;
p();;
hd it;;
fst3 it;;
let qqinst = snd it;;
instantiate qqinst `P:(num)Agent`;;

let qqmou = it;;

map (instantiate qqinst) [`x:num`; `y:num`; `z:num`; `w:num`; `v:num`; `t:num`];;
print_piviz qqmou;;




(^ z16)(((^ z17)(((^ z18)(((^ z19)(((^ hdl, csl)('z19<hdl, csl>.(HomeDir(hdc,hdl,hl) | CriminalService(csr,csl,cl))) | z19(hal, hac).HouseAlert(hal,hac,had,z18))) | z18(eoi, y22).y22(cld, tsi).(^ x24, y24)('z17<x24, y24>.((^ z25)((TitleSearch(tsi,z25,ht,hi,hiid) | z25(x26, y26).(^ x27, hii)('x24<x27, hii>.(x26(a28).'x27<a28>.0 | (^ u52, v52)('y26<u52, v52>.(u52(x52).x52(a29).'hii<a29>.0 + v52(hid).HomeIns(hid,hii,hi))))))) | (^ z30)((EstateAgentOffer(eoi,eoc,z30,ho) | (^ z31)(((^ z32)(((^ z33)(((^ mo, clo)('z33<mo, clo>.(MortgageService(mi,mo,pa,exm) | Client(cld,z30,clo,ao,ro))) | z33(na33, yb33).(^ uc33, vc33)('yb33<uc33, vc33>.(uc33(nb33).(^ xd33)(z32(ud33, vd33).'ud33<xd33>.(^ aa33, bb33)('xd33<aa33, bb33>.((^ u84, v84)('na33<u84, v84>.(u84(x84).(^ x85)(aa33(u85, v85).'u85<x85>.x84(a86).'x85<a86>.0) + v84(y84).(^ y87)(aa33(u87, v87).'v87<y87>.y84(a88).'y87<a88>.0))) | nb33(a89).'bb33<a89>.0))) + vc33(nc33).(^ ye33)(z32(ue33, ve33).'ve33<ye33>.(^ aa331, cc33)('ye33<aa331, cc33>.((^ u841, v841)('na33<u841, v841>.(u841(x84).(^ x851)(aa331(u85, v85).'u85<x851>.x84(a86).'x851<a86>.0) + v841(y84).(^ y871)(aa331(u87, v87).'v87<y87>.y84(a88).'y871<a88>.0))) | nc33(a90).'cc33<a90>.0))))))) | (^ ua32, va32)('z32<ua32, va32>.(ua32(xa32).xa32(xb32, na32).(^ uc32, vc32)('xb32<uc32, vc32>.(uc32(nb32).(^ xd32)(z31(ud32, vd32).'ud32<xd32>.(^ bb32, aa32)('xd32<bb32, aa32>.(nb32(a74).'bb32<a74>.0 | na32(a73).'aa32<a73>.0))) + vc32(nc32).(^ ye32)(z31(ue32, ve32).'ve32<ye32>.(^ xf32)(ye32(uf32, vf32).'uf32<xf32>.(^ cc32, aa321)('xf32<cc32, aa321>.(nc32(a75).'cc32<a75>.0 | na32(a73).'aa321<a73>.0)))))) + va32(nd32).(^ yg32)(z31(ug32, vg32).'vg32<yg32>.(^ dd32)(yg32(uh32, vh32).'vh32<dd32>.nd32(x76, y76).(^ x77, y77)('dd32<x77, y77>.((^ u82, v82)('x76<u82, v82>.(u82(x82).(^ x83)(x77(u83, v83).'u83<x83>.x82(a78).'x83<a78>.0) + v82(y82).(^ y79)(x77(u79, v79).'v79<y79>.y82(a80).'y79<a80>.0))) | y76(a81).'y77<a81>.0)))))))) | (^ u35, v35)('z31<u35, v35>.(u35(x35).(^ esc)(y24(u36, v36).'u36<esc>.x35(esa, eso).EstateAgentSeller(esa,eso,esc,co)) + v35(y35).(^ y38)(y24(u38, v38).'v38<y38>.(^ u150, v150)('y35<u150, v150>.(u150(xa50).(^ xb50)(y38(ub50, vb50).'ub50<xb50>.xa50(xc50, yc50).(^ xd50, yd50)('xb50<xd50, yd50>.(xc50(ae50).'xd50<ae50>.0 | yc50(bufa50).'yd50<bufa50>.0))) + v150(ya50).ya50(xg50, yg50).(^ yo50)(y38(uo50, vo50).'vo50<yo50>.(^ xh50, yh50)('yo50<xh50, yh50>.((^ ui50, vi50)('xg50<ui50, vi50>.(ui50(xi50).(^ xj50)(xh50(uj50, vj50).'uj50<xj50>.xi50(bufb50).'xj50<bufb50>.0) + vi50(yi50).(^ yl50)(xh50(ul50, vl50).'vl50<yl50>.yi50(bufc50).'yl50<bufc50>.0))) | yg50(an50).'yh50<an50>.0)))))))))))))))) | z17(na17, yb17).(^ uc17, vc17)('yb17<uc17, vc17>.(uc17(nb17).(^ xd17)(z16(ud17, vd17).'ud17<xd17>.(^ aa17, bb17)('xd17<aa17, bb17>.(na17(x53, y53).(^ x54, y54)('aa17<x54, y54>.(x53(a55).'x54<a55>.0 | y53(a56).'y54<a56>.0)) | nb17(a57).'bb17<a57>.0))) + vc17(nc17).(^ ye17)(z16(ue17, ve17).'ve17<ye17>.(^ aa171, cc17)('ye17<aa171, cc17>.(na17(x53, y53).(^ x541, y541)('aa171<x541, y541>.(x53(a55).'x541<a55>.0 | y53(a56).'y541<a56>.0)) | (^ u58, v58)('nc17<u58, v58>.(u58(x58).(^ x59)(cc17(u59, v59).'u59<x59>.x58(x60, y60).(^ x61, y61)('x59<x61, y61>.(x60(a62).'x61<a62>.0 | y60(a63).'y61<a63>.0))) + v58(y58).(^ y64)(cc17(u64, v64).'v64<y64>.y58(x65, y65).(^ x66, y66)('y64<x66, y66>.((^ u67, v67)('x65<u67, v67>.(u67(x67).(^ x68)(x66(u68, v68).'u68<x68>.x67(a69).'x68<a69>.0) + v67(y67).(^ y70)(x66(u70, v70).'v70<y70>.y67(a71).'y70<a71>.0))) | y65(a72).'y66<a72>.0)))))))))))) | (^ u39, v39)('z16<u39, v39>.(u39(x39).(^ ses)(tt(u40, v40).'u40<ses>.x39(x41, sec).x41(set, sei).Settlement(set,sec,sei,ses,s)) + v39(y39).(^ y43)(tt(u43, v43).'v43<y43>.y39(x44, y44).(^ x45, y45)('y43<x45, y45>.(x44(x46, y46).(^ x47, y47)('x45<x47, y47>.(x46(a48).'x47<a48>.0 | y46(a49).'y47<a49>.0)) | (^ u151, v151)('y44<u151, v151>.(u151(xa51).(^ xb51)(y45(ub51, vb51).'ub51<xb51>.xa51(xc51, yc51).(^ xd51, yd51)('xb51<xd51, yd51>.(xc51(ae51).'xd51<ae51>.0 | yc51(bufa51).'yd51<bufa51>.0))) + v151(ya51).ya51(xg51, yg51).(^ yo51)(y45(uo51, vo51).'vo51<yo51>.(^ xh51, yh51)('yo51<xh51, yh51>.((^ ui51, vi51)('xg51<ui51, vi51>.(ui51(xi51).(^ xj51)(xh51(uj51, vj51).'uj51<xj51>.xi51(bufb51).'xj51<bufb51>.0) + vi51(yi51).(^ yl51)(xh51(ul51, vl51).'vl51<yl51>.yi51(bufc51).'yl51<bufc51>.0))) | yg51(an51).'yh51<an51>.0))))))))))))


let myservices = [
`|-- (' (NEG A <> aa) ^ ' (B <> bb)) P`;
`|-- (' (NEG B <> nb) ^ ' ((C ++ (E1 ** E2)) <> cc)) Q`
];;



let mytarget = `?x y W E. |-- (' (NEG A <> x) ^ ' ((C ++ E) <> y)) W`;;

let mygoal = itlist (fun x y -> mk_imp (x,y)) myservices mytarget;;

g mygoal;;
e (REPEAT DISCH_TAC);;
e (REPEAT META_EXISTS_TAC);;

e (lldrule (number_vars_thm 1 ll_cut));;
e (llrule_tac [(`C1`,`B`)] (number_vars_thm 1 ll_cut));;
ellma ();;
ellma ();;

top_thm();;

p();;
hd it;;
fst3 it;;

map (fun x -> (x,instantiate (snd it) x)) (fst it);;
