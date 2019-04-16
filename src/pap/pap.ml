(* ========================================================================= *)
(* The Proofs-as-Processes paradigm.                                         *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2009-2019                                 *)
(* ========================================================================= *)

(* Dependencies *)

needs "IsabelleLight/make.ml";;
needs (!serv_dir ^ "support/support.ml");;
needs (!serv_dir ^ "CLL/CLL.ml");;
needs (!serv_dir ^ "processes/process_calculus.ml");;
needs (!serv_dir ^ "pap/pi.ml");;
needs (!serv_dir ^ "CLL/CLL_prover.ml");;

(* Translation from CLL to pi-calculus. *)

(* LinProps *)

let rec linprop_to_pi' chanOf prefix chan tm =
  try 
    let comb,args = strip_comb tm in
      if (is_var comb) then 
	let name = prefix ^ "_a_" ^ (chanOf comb)in
	let v = mk_var(name,`:num`) in
	let vec = list_mk_icomb "CONS" [v;`[]:(num)list`] in
	  list_mk_icomb "Res" [vec; list_mk_icomb "Out" [chan; vec; `Zero:(num)Agent`]], [name,comb]
      else if (comb = `NEG`) then
        let name = prefix ^ "_a_" ^ ((chanOf o hd) args) in
      	let v = mk_var(name,`:num`) in
	let vec = list_mk_icomb "CONS" [v;`[]:(num)list`] in
	  list_mk_icomb "In" [chan; vec; `Zero:(num)Agent`], [name,hd args]
      else if (comb = `LinTimes`) then
	let newchana = mk_var(prefix ^ ((chanOf o hd) args),`:num`)
	and newchanb = mk_var(prefix ^ ((chanOf o hd o tl) args),`:num`) in
        let pil,tyl = linprop_to_pi' chanOf (prefix ^ "l") newchana (hd args)
	and pir,tyr = linprop_to_pi' chanOf (prefix ^ "r") newchanb ((hd o tl) args) in
	let vec = mk_flist [newchana;newchanb] in
	  list_mk_icomb "Res" [vec; list_mk_icomb "Out" [chan; vec; 
							 list_mk_icomb "Comp" [pil;pir]]],
	  tyl @ tyr
      else if (comb = `LinPar`) then
	let newchana = mk_var(prefix ^ ((chanOf o hd) args),`:num`) 
	and newchanb = mk_var(prefix ^ ((chanOf o hd o tl) args),`:num`) in
        let pil,tyl = linprop_to_pi' chanOf (prefix ^ "l") newchana (hd args)
	and pir,tyr = linprop_to_pi' chanOf (prefix ^ "r") newchanb ((hd o tl) args) in
	let vec = mk_flist [newchana;newchanb] in
	  list_mk_icomb "In" [chan; vec; 
			      list_mk_icomb "Comp" [pil;pir]],
	  tyl @ tyr
      else if (comb = `LinPlus`) then
	let chanu = mk_var(prefix ^ "_opt_" ^ ((chanOf o hd) args),`:num`)  
	and chanv = mk_var(prefix ^ "_opt_" ^ ((chanOf o hd o tl) args),`:num`) 
	and chanx = mk_var(prefix ^ ((chanOf o hd) args),`:num`)
	and chany = mk_var(prefix ^ ((chanOf o hd o tl) args),`:num`) in
	let pil,tyl = linprop_to_pi' chanOf (prefix ^ "l") chanx (hd args)
	and pir,tyr = linprop_to_pi' chanOf (prefix ^ "r") chany ((hd o tl) args) in
	let resvec = mk_flist [chanx;chany]
	and vec = mk_flist [chanu;chanv] in
	  list_mk_icomb "Res" [resvec; 
			       list_mk_icomb "In" [chan; vec; 
						   list_mk_icomb "Plus" [
						     list_mk_icomb "Out" [chanu; mk_flist [chanx];pil];
						     list_mk_icomb "Out" [chanv; mk_flist [chany];pir]]]],
	  tyl @ tyr
      else if (comb = `LinWith`) then
	let chanu = mk_var(prefix ^ "_opt_" ^ ((chanOf o hd) args),`:num`) 
	and chanv = mk_var(prefix ^ "_opt_" ^ ((chanOf o hd o tl) args),`:num`)
	and chanx = mk_var(prefix ^ ((chanOf o hd) args),`:num`)
	and chany = mk_var(prefix ^ ((chanOf o hd o tl) args),`:num`) in
	let pil,tyl = linprop_to_pi' chanOf (prefix ^ "l") chanx (hd args)
	and pir,tyr = linprop_to_pi' chanOf (prefix ^ "r") chany ((hd o tl) args) in
	let vec = mk_flist [chanu;chanv] in
	  list_mk_icomb "Res" [vec; 
			       list_mk_icomb "Out" [chan; vec; 
						    list_mk_icomb "Plus" [
						      list_mk_icomb "In" [chanu; mk_flist [chanx];pil];
						      list_mk_icomb "In" [chanv; mk_flist [chany];pir]]]],
	  tyl @ tyr
      else failwith ""
  with Failure s -> failwith ("linprop_to_pi (" ^ string_of_term(tm) ^ ") :" ^ s);;

let linprop_to_pi chanOf prefix chan tm = fst (linprop_to_pi' chanOf prefix chan tm);;
    
(* LinTerms *)
      
let linterm_to_pi' chanOf tm =
  let oper = `(<>):(LinProp->num->(num)LinTerm)` in
    try
      let (linprop,chan) = dest_binop oper tm in
	linprop_to_pi' chanOf (string_of_term chan ^ "_") chan linprop
    with Failure _ -> failwith ("linterm_to_pi: " ^ string_of_term(tm));;

let linterm_to_pi chanOf tm = fst (linterm_to_pi' chanOf tm);;

(* Multiset of sequents. *)

let linseq_to_pi chanOf tm =
  let linmsing_to_pi = linterm_to_pi chanOf o rhs o concl o (PURE_REWRITE_CONV[NEG_NEG;NEG_CLAUSES]) o snd o dest_comb in
  let terms = flat_munion tm in 
    match terms with
	[] -> `Zero:(num)Agent`
      | [h] -> linmsing_to_pi h
      | _ -> 
	  let procs = map linmsing_to_pi terms in
	  let mkPiComp x y = list_mk_icomb "Comp" [x;y] in
	    itlist mkPiComp (butlast procs) (last procs);;


(* Negated LinTerms *)

let linterm_to_pi_inv chanOf tm =
  let oper = `(<>):(LinProp->num->(num)LinTerm)` in
    try
      let (linprop,chan) = dest_binop oper tm in
      let linprop_inv = (rhs o concl o (PURE_REWRITE_CONV[NEG_NEG;NEG_CLAUSES]) o (fun x -> mk_comb(`NEG`,x))) linprop in
	linprop_to_pi chanOf (string_of_term chan ^ "_") chan linprop_inv
    with Failure s -> failwith ("linterm_to_pi_inv (" ^ string_of_term(tm) ^ ") :" ^ s);;



(* Negated multiset of sequents. *)

let linseq_to_pi_inv chanOf tm =
  let linmsing_to_pi = linterm_to_pi_inv chanOf o snd o dest_comb in
  let terms = flat_munion tm in 
    match terms with
	[] -> `Zero:(num)Agent`
      | [h] -> linmsing_to_pi h
      | _ -> 
	  let procs = map linmsing_to_pi terms in
	  let mkPiComp x y = list_mk_icomb "Comp" [x;y] in
	    itlist mkPiComp (butlast procs) (last procs);;


(* ------------------------------------------------------------------------- *) 
(* Reduces pi-calculus substitutions to simple variable substitutions.       *)
(* ------------------------------------------------------------------------- *)
(* This allows substitutions over agent definitions without unfolding.       *)
(* Proof is accomplished through PI_AGENT_REDUCE_CONV.                       *)
(* ------------------------------------------------------------------------- *) 
(* Proofs-as-processes introduces substitutions only when using the cut rule.*)
(* Substitutions there are always using a fresh name z, so there can never   *)
(* be any clashes with other bound variables, so this should always succeed. *)
(* ------------------------------------------------------------------------- *) 

let reduce_pap_subs tm =
  let reduce tm =
    if (is_piSUB tm) 
    then
      let fmap = (rhs o concl o FUPDATE_LIST_NORMALISE_CONV o rand) tm in
      let subs = try ( (map (invpair o dest_pair) o dest_list o rand) fmap )
	with Failure _ -> failwith ("reduce_pap_subs: Failed to normalise substitution: " ^ string_of_term tm) in
      ((subst subs) o rand o rator) tm
    else tm in (* failwith ("reduce_pap_subs: Not a piSUB: " ^ string_of_term tm) in *)

  let rec reduce_rec tm =
    let tm = reduce tm in
    if is_abs tm then
      let l,r = dest_abs tm in mk_abs (l,reduce_rec r)
    else if is_comb tm then
      let comb,args = strip_comb tm in list_mk_comb (comb,map reduce_rec args) 
    else tm in

  (reduce_rec o rhs o concl o REWRITE_CONV[piSUBN1;piSUBN]) tm;;




module Pi_calc : Process_calculus =
struct
  let consequence = "|--"
  let chantp = `:num`
  let tp = `:NAgent`
  let fn = `FNL:NAgent->(num)list`
  let bn = `BNL:NAgent->(num)list`
  let names = `NAMESL:NAgent->(num)list`
  let fn_conv = PI_CONV (FNL_CONV NUM_EQ_CONV)
  let bn_conv = PI_CONV (BNL_CONV NUM_EQ_CONV)
  let names_conv = PI_CONV (NAMESL_CONV NUM_EQ_CONV)
  let sub_conv agents =
    REWRITE_CONV[piSUBN1;piSUBN] THENC
      (PI_AGENT_REDUCE_CONV agents reduce_pap_subs (DEPTH_CONV PI_SUBN_CONV))
  let sub_reduce = reduce_pap_subs

  let llid A x y m =
    let out = list_mk_icomb "Out" [y;mk_flist [m];`Zero:NAgent`] in
      list_mk_icomb "In" [x;mk_flist [m];out]

  let lltimes A B z x y P Q =
    let out = list_mk_icomb "Out" [z;mk_flist [x;y];list_mk_icomb "Comp" [P;Q]] in
      list_mk_icomb "Res" [mk_flist [x;y];out]

  let llpar A B z x y P =
      list_mk_icomb "In" [z;mk_flist [x;y];P]

  let llwith A B z x y u v P Q =
     let l = list_mk_icomb "In" [u;mk_flist [x];P]
    and r = list_mk_icomb "In" [v;mk_flist [y];Q] in
    let out = list_mk_icomb "Out" [z;mk_flist [u;v];list_mk_icomb "Plus" [l;r]] in
      list_mk_icomb "Res" [mk_flist [u;v];out]

  let llplusL A B z x u v P =
    let l = list_mk_icomb "Out" [u;mk_flist [x];P] in
    let out = list_mk_icomb "In" [z;mk_flist [u;v];l] in
      list_mk_icomb "Res" [mk_flist [x];out]

  let llplusR A B z y u v Q =
    let r = list_mk_icomb "Out" [v;mk_flist [y];Q] in
    let out = list_mk_icomb "In" [z;mk_flist [u;v];r] in
      list_mk_icomb "Res" [mk_flist [y];out]

  let llcut C z x y P Q = 
    let l = list_mk_icomb "piSUBN1" [P;mk_pair (x,z)]
    and r = list_mk_icomb "piSUBN1" [Q;mk_pair (y,z)] in
    list_mk_icomb "Res" [mk_flist [z];list_mk_icomb "Comp" [l;r]]

  let cll_to_proc = linseq_to_pi
(*  let fake_subs = fake_pisubn1
  let prove_subs = prove_pisubn1 *)
end;;

module Cllpi = Cllproc(Pi_calc);;
