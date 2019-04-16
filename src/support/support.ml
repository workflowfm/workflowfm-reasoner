(* ========================================================================= *)
(* Useful general functions, theorems, tactics, conversions, etc.            *)
(*                                                                           *)
(*                           Petros Papapanagiotou                           *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                 2010-2019                                 *)
(* ========================================================================= *)

needs "IsabelleLight/make.ml";;
needs "tools/lib.ml";; (* doesn't really "need" it, but we move some stuff from here to there *) 
needs "tools/terms.ml";;

let string_matches_term key tm =
  try (
    match (term_match [] (parse_term key) tm) with
      | [],[],_ -> true
      | _ -> false
  ) with Failure _ -> false;;


(* ------------------------------------------------------------------------- *)
(* A function used in the justification of our rule tactics.                 *)
(* Discharges a list of terms dischl from theorem thm after instantiating    *)
(* both with i.                                                              *)
(* ------------------------------------------------------------------------- *)

let dischi_pair = 
  fun i (dischl,thm) -> 
    DISCHL (map (instantiate i) dischl) (INSTANTIATE_ALL i thm);;


(* ------------------------------------------------------------------------- *)
(* Same as find_path but with an ignore function that allows skipping some   *)
(* combinators. This is used in INST_AGENTS.                                 *)
(* The ignore function should fail if the term should NOT be ignored,        *)
(* otherwise provide a term->term function to skip through the combinator    *) 
(* (eg. rand, rator).                                                        *)
(* ------------------------------------------------------------------------- *)

let find_path_ign =
  let rec find_path_ign ign p tm =
    if p tm then [] else
    if is_abs tm then "b"::(find_path_ign ign p (body tm)) else
    try( let op = ign tm in find_path_ign ign p (op tm)) with Failure _ ->
      try "r"::(find_path_ign ign p (rand tm))
      with Failure _ -> "l"::(find_path_ign ign p (rator tm)) in
  fun ign p tm -> implode(find_path_ign ign p tm);;


