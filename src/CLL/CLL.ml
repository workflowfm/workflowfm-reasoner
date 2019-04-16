(* ========================================================================= *)
(* Deep embedding of Classical Linear Logic                                  *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2009-2019                                 *)
(* ========================================================================= *)

(* Dependencies *)

needs "IsabelleLight/make.ml";;
needs "tools/make.ml";;
needs "tools/Library/multisets.ml";; (* We need the multiset type in Cll_terms *)

(* ------------------------------------------------------------------------- *)
(* Formalisation of Classical Propositional Linear Logic                     *)
(* ------------------------------------------------------------------------- *)

(* Type definition: Propositional Linear Logic term. *)

let linprop_INDUCT,linprop_RECURSION = define_type
                                         "LinProp = LinOne
                                          | Bottom
	                                      | Top
	                                      | LinZero
                                          | OfCourse LinProp
                                          | WhyNot LinProp
                                          | LinPlus LinProp LinProp
                                          | LinWith LinProp LinProp
                                          | LinTimes LinProp LinProp
                                          | LinPar LinProp LinProp"
;;


(* Type definition: Linear Proposition with a proof term attached to it. *)

let linterm_INDUCT,linterm_RECURSION = define_type "LinTerm = LL LinProp A";;


(* Pretty printing abbreviations *)

parse_as_infix("++",(13,"right"));; 
override_interface("++",`LinPlus`);;
parse_as_infix("**",(13,"right"));;
override_interface("**",`LinTimes`);;
parse_as_infix("&",(13,"right"));;
override_interface("&",`LinWith`);;
parse_as_infix("%",(13,"right"));;
override_interface("%",`LinPar`);;
parse_as_prefix("!!");;
override_interface("!!",`OfCourse`);;
parse_as_prefix("??");;
override_interface("??",`WhyNot`);;
parse_as_infix("<>",(16,"right"));;
override_interface("<>",`LL`);;

let is_tensor = is_binary "LinTimes";;
let is_plus = is_binary "LinPlus";;
let is_par = is_binary "LinPar";;
let is_with = is_binary "LinWith";;

let flat_tensor = flat_binary "LinTimes";;
let flat_plus = flat_binary "LinPlus";;
let flat_par = flat_binary "LinPar";;
let flat_with = flat_binary "LinWith";;


(* Some automatically proven properties *)

let linear_CASES = prove_cases_thm linprop_INDUCT;;
	      
let linear_DISTINCT = distinctness "LinProp";;

let linear_INJ = injectivity "LinProp";;


(* ------------------------------------------------------------------------- *)
(* Linear Negation                                                           *)
(* ------------------------------------------------------------------------- *)

(* Conservative definition of linear negation as a function. *)
 
let NEG_CLAUSES = define
  `(NEG LinOne = Bottom) /\
   (NEG Bottom = LinOne) /\
   (NEG LinZero = Top) /\
   (NEG Top = LinZero) /\
   (NEG (A ** B) = (NEG A) % (NEG B)) /\
   (NEG (A % B) = (NEG A) ** (NEG B)) /\
   (NEG (A ++ B ) = (NEG A) & (NEG B)) /\
   (NEG (A & B) = (NEG A) ++ (NEG B)) /\
   (NEG (!! A) = ?? (NEG A)) /\
   (NEG (?? A) = !! (NEG A))`;;


(* Double negation. *)

let NEG_NEG = prove (`!A . NEG (NEG A) = A`, MATCH_MP_TAC linprop_INDUCT THEN simp[NEG_CLAUSES]);;


(* Negation clauses. *)

let [NEG_ONE; NEG_BOTTOM; 
     NEG_ZERO; NEG_TOP;
     NEG_TIMES; NEG_PAR; 
     NEG_PLUS; NEG_WITH; 
     NEG_OFCOURSE ; NEG_WHYNOT] =
  map GEN_ALL (CONJUNCTS NEG_CLAUSES);;


(* Meta-level handling for negation. *)

let is_llneg tm = 
  try fst(dest_const(rator tm)) = "NEG"
  with Failure _ -> false;;

let mk_llneg tm = 
  try ( mk_icomb (`NEG`,tm) ) 
  with Failure s -> failwith ("mk_llneg `" ^ string_of_term tm ^ "` : " ^ s);;

let invert_ll_term tm = 
  try (
    let (comb,args) = strip_comb tm in
    let cll = hd args in
    let cll' = (rhs o concl o (PURE_REWRITE_CONV[NEG_NEG;NEG_CLAUSES]) o (fun x -> mk_comb(`NEG`,x))) cll in
      list_mk_comb (comb,cll'::(tl args))
  ) with Failure _ -> failwith ("invert_ll_term: Invalid term ["^(string_of_term tm)^"]");;


(* ------------------------------------------------------------------------- *)
(* Creates lists of resources involved in a positive CLL term.               *)
(* Essentially, each list is a solution to the boolean formula corresponding *)
(* to the CLL term, with Plus as exclusive OR and Times as AND.              *)
(* This is useful for context splitting in automated proofs.                 *)
(* Naturally, this function becomes intractable in very large terms.         *)
(* ------------------------------------------------------------------------- *)
(* Examples:                                                                 *)
(* # ll_resources `A ** B`;;                                                 *)
(* val it : term list list = [[`A`; `B`]]                                    *)
(* # ll_resources `A ++ B`;;                                                 *)
(* val it : term list list = [[`A`]; [`B`]]                                  *)
(* # ll_resources `(A ++ B) ** (C ++ D)`;;                                   *)
(* val it : term list list = [[`A`; `C`]; [`A`; `D`]; [`B`; `C`]; [`B`; `D`]]*)
(* # ll_resources `(A ++ B) ++ (C ++ D)`;;                                   *)
(* val it : term list list = [[`A`]; [`B`]; [`C`]; [`D`]]                    *)
(* # ll_resources `(A ** B) ++ (C ++ D)`;;                                   *)
(* val it : term list list = [[`A`; `B`]; [`C`]; [`D`]]                      *)
(* # ll_resources `(A ** B) ++ (C ** D)`;;                                   *)
(* val it : term list list = [[`A`; `B`]; [`C`; `D`]]                        *)
(* # ll_resources `(A ++ B) ** (C ++ D) ** (E ++ F)`;;                       *)
(* val it : term list list =                                                 *)
(*   [[`A`; `C`; `E`]; [`A`; `C`; `F`]; [`A`; `D`; `E`]; [`A`; `D`; `F`];    *)
(*   [`B`; `C`; `E`]; [`B`; `C`; `F`]; [`B`; `D`; `E`]; [`B`; `D`; `F`]]     *)
(* ------------------------------------------------------------------------- *)
(* This is not currently being used, but kept here for future reference.     *)
(* ------------------------------------------------------------------------- *)

let ll_resources tm =
  let times r x = map (fun y -> x @ y) r in
  let distrib l r = flat (map (times r) l) in

  let rec res tm =
    if (is_var tm) then [[tm]]
  else
    let comb,args = strip_comb tm in
    if (comb = `LinPlus`) then
      (res (hd args)) @ (res (hd (tl args)))
    else
      distrib (res (hd args)) (res (hd (tl args))) in
  
  res tm;;



(* ------------------------------------------------------------------------- *)
(* This module provides functions for the construction of the terms          *)
(* involved in the CLL rule definition.                                      *)
(* This includes the assumptions and conclusion of the inference rules, the  *)
(* process calculus translations, and a substitution theorem for each        *)
(* process.                                                                  *)
(* ------------------------------------------------------------------------- *)

module Cll_terms: sig
  val mk_id_proc : hol_type -> hol_type -> (term->term->term->term->term) -> term
  val mk_times_proc : hol_type -> hol_type -> (term->term->term->term->term->term->term->term) -> term
  val mk_par_proc : hol_type -> hol_type -> (term->term->term->term->term->term->term) -> term
  val mk_with_proc : hol_type -> hol_type -> (term->term->term->term->term->term->term->term->term->term) -> term
  val mk_plusL_proc : hol_type -> hol_type -> (term->term->term->term->term->term->term->term) -> term
  val mk_plusR_proc : hol_type -> hol_type -> (term->term->term->term->term->term->term->term) -> term
  val mk_cut_proc : hol_type -> hol_type -> (term->term->term->term->term->term->term) -> term

  val mk_id_rule : string -> hol_type -> hol_type -> thm -> term
  val mk_times_rule : string -> hol_type -> hol_type -> thm -> term
  val mk_par_rule : string -> hol_type -> hol_type -> thm -> term
  val mk_with_rule : string -> hol_type -> hol_type -> thm -> term
  val mk_plusL_rule : string -> hol_type -> hol_type -> thm -> term
  val mk_plusR_rule : string -> hol_type -> hol_type -> thm -> term
  val mk_cut_rule : string -> hol_type -> hol_type -> thm -> term

  val mk_cll_rules : string -> hol_type -> hol_type -> thm->thm->thm->thm->thm->thm->thm -> term

end = struct

  let mk_id_proc tp chantp llid = 
    let name_params = ["A";"x";"y";"m"] 
    and ty_params = [`:LinProp`;chantp;chantp;chantp] in
    let params = map mk_var (zip name_params ty_params) 
    and oper = mk_var ("IdProc",itlist mk_fun_ty ty_params tp) in
    let def_lhs = list_mk_comb (oper,params)
    and def_rhs = llid (el 0 params) (el 1 params) (el 2 params) (el 3 params) in
      mk_eq (def_lhs,def_rhs)

  let mk_times_proc tp chantp lltimes =   
    let name_params = ["A";"B";"z";"x";"y";"P";"Q"] 
    and ty_params = [`:LinProp`;`:LinProp`;chantp;chantp;chantp;tp;tp] in
    let params = map mk_var (zip name_params ty_params) 
    and oper = mk_var ("TimesProc",itlist mk_fun_ty ty_params tp) in
    let def_lhs = list_mk_comb (oper,params)
    and def_rhs = lltimes (el 0 params) (el 1 params) (el 2 params) (el 3 params) (el 4 params) (el 5 params) (el 6 params) in
      mk_eq (def_lhs,def_rhs)

  let mk_par_proc tp chantp llpar =   
    let name_params = ["A";"B";"z";"x";"y";"P"] 
    and ty_params = [`:LinProp`;`:LinProp`;chantp;chantp;chantp;tp] in
    let params = map mk_var (zip name_params ty_params) 
    and oper = mk_var ("ParProc",itlist mk_fun_ty ty_params tp) in
    let def_lhs = list_mk_comb (oper,params)
    and def_rhs = llpar (el 0 params) (el 1 params) (el 2 params) (el 3 params) (el 4 params) (el 5 params) in
      mk_eq (def_lhs,def_rhs)

  let mk_with_proc tp chantp llwith =   
    let name_params = ["A";"B";"z";"x";"y";"u";"v";"P";"Q"] 
    and ty_params = [`:LinProp`;`:LinProp`;chantp;chantp;chantp;chantp;chantp;tp;tp] in
    let params = map mk_var (zip name_params ty_params) 
    and oper = mk_var ("WithProc",itlist mk_fun_ty ty_params tp) in
    let def_lhs = list_mk_comb (oper,params)
    and def_rhs = llwith (el 0 params) (el 1 params) (el 2 params) (el 3 params) (el 4 params) (el 5 params) (el 6 params) (el 7 params) (el 8 params) in
      mk_eq (def_lhs,def_rhs)

  let mk_plusL_proc tp chantp llplusL =   
    let name_params = ["A";"B";"z";"x";"u";"v";"P"] 
    and ty_params = [`:LinProp`;`:LinProp`;chantp;chantp;chantp;chantp;tp] in
    let params = map mk_var (zip name_params ty_params) 
    and oper = mk_var ("PlusLProc",itlist mk_fun_ty ty_params tp) in
    let def_lhs = list_mk_comb (oper,params)
    and def_rhs = llplusL (el 0 params) (el 1 params) (el 2 params) (el 3 params) (el 4 params) (el 5 params) (el 6 params) in
      mk_eq (def_lhs,def_rhs)

  let mk_plusR_proc tp chantp llplusR =   
    let name_params = ["A";"B";"z";"y";"u";"v";"Q"] 
    and ty_params = [`:LinProp`;`:LinProp`;chantp;chantp;chantp;chantp;tp] in
    let params = map mk_var (zip name_params ty_params) 
    and oper = mk_var ("PlusRProc",itlist mk_fun_ty ty_params tp) in
    let def_lhs = list_mk_comb (oper,params)
    and def_rhs = llplusR (el 0 params) (el 1 params) (el 2 params) (el 3 params) (el 4 params) (el 5 params) (el 6 params) in
      mk_eq (def_lhs,def_rhs)

  let mk_cut_proc tp chantp llcut =   
    let name_params = ["C";"z";"x";"y";"P";"Q"] 
    and ty_params = [`:LinProp`;chantp;chantp;chantp;tp;tp] in
    let params = map mk_var (zip name_params ty_params) 
    and oper = mk_var ("CutProc",itlist mk_fun_ty ty_params tp) in
    let def_lhs = list_mk_comb (oper,params)
    and def_rhs = llcut (el 0 params) (el 1 params) (el 2 params) (el 3 params) (el 4 params) (el 5 params) in
      mk_eq (def_lhs,def_rhs)

	    
  let mk_oper st tp chantp = inst [(chantp,`:CHANTP`);(tp,`:TP`)] (mk_var (st,`:((CHANTP)LinTerm)multiset->TP->bool`))
 
  let mk_rule oper tp chantp procdef asms asmprocs conc =
    let oper = mk_oper oper tp chantp 
    and asms' = map (inst [chantp,`:CHANTP`]) asms
    and asmprocs' = map (inst [tp,`:TP`]) asmprocs
    and conc' = inst [chantp,`:CHANTP`] conc
    and proc = (lhs o snd o strip_forall o concl) procdef in

    let mk_lin (x,y) = list_mk_comb (oper,[x;y])
    and mk_ruleimp (asms,concl) =
      match asms with
	  [] -> concl
	| _ -> mk_imp (list_mk_conj asms,concl) in
    let create_rule (asms,concl) =
      let imp = mk_ruleimp (asms,concl) in
      list_mk_forall (filter ((!=) oper) (frees imp),imp) in

    create_rule (map mk_lin (zip asms' asmprocs'),mk_lin (conc',proc))
		
  let mk_id_rule oper tp chantp thm =
    mk_rule oper tp chantp thm
	    []
	    []
	    `(' (NEG A <> x) ^ ' (A <> y)):((CHANTP)LinTerm)multiset`

  let mk_times_rule oper tp chantp thm =
    mk_rule oper tp chantp thm
	    [`(G ^ ' (A <> x)):((CHANTP)LinTerm)multiset`;`(D ^ ' (B <> y)):((CHANTP)LinTerm)multiset`]
	    [`P:TP`;`Q:TP`]
	    `(G ^ D ^ ' ((A ** B) <> z)):((CHANTP)LinTerm)multiset`

  let mk_par_rule oper tp chantp thm =
    mk_rule oper tp chantp thm
	    [`(G ^ ' (A <> x) ^ ' (B <> y)):((CHANTP)LinTerm)multiset`]
	    [`P:TP`]
	    `(G ^ ' ((A % B) <> z)):((CHANTP)LinTerm)multiset`

  let mk_with_rule oper tp chantp thm =
    mk_rule oper tp chantp thm
	    [`(G ^ ' (A <> x)):((CHANTP)LinTerm)multiset`;`(G ^ ' (B <> y)):((CHANTP)LinTerm)multiset`]
	    [`P:TP`;`Q:TP`]
	    `(G ^ ' ((A & B) <> z)):((CHANTP)LinTerm)multiset`

  let mk_plusL_rule oper tp chantp thm =
    mk_rule oper tp chantp thm
	    [`(G ^ ' (A <> x)):((CHANTP)LinTerm)multiset`]
	    [`P:TP`]
	    `(G ^ ' ((A ++ B) <> z)):((CHANTP)LinTerm)multiset`

  let mk_plusR_rule oper tp chantp thm =
    mk_rule oper tp chantp thm
	    [`(G ^ ' (B <> y)):((CHANTP)LinTerm)multiset`]
	    [`Q:TP`]
	    `(G ^ ' ((A ++ B) <> z)):((CHANTP)LinTerm)multiset`

  let mk_cut_rule oper tp chantp thm =
    mk_rule oper tp chantp thm
	    [`(' (NEG C <> x) ^ D):((CHANTP)LinTerm)multiset`;`(G ^ ' (C <> y)):((CHANTP)LinTerm)multiset`] 
	    [`P:TP`;`Q:TP`]
	    `(G ^ D):((CHANTP)LinTerm)multiset`

  let mk_cll_rules oper tp chantp idthm timesthm parthm withthm plusLthm plusRthm cutthm =
    list_mk_conj [
      mk_id_rule oper tp chantp idthm;
      mk_times_rule oper tp chantp timesthm;
      mk_par_rule oper tp chantp parthm;
      mk_with_rule oper tp chantp withthm;
      mk_plusL_rule oper tp chantp plusLthm;
      mk_plusR_rule oper tp chantp plusRthm;
      mk_cut_rule oper tp chantp cutthm ]
end;;



