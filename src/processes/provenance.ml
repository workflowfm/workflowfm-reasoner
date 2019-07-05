(* ========================================================================= *)
(* Tracking provenance of each resource in an output.                        *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                    2016                                   *)
(* ========================================================================= *)

(* Dependencies *)

needs (!serv_dir ^ "CLL/CLL.ml");;

type provtree =
  Provnode of string * provtree * provtree
  | Provleaf of string;;

let provtimes pl pr = Provnode("times",pl,pr);;
let provplus pl pr = Provnode("plus",pl,pr);;


let rec prov_of_tm s tm =
  if (is_var tm) then Provleaf(s) 
  else
    let comb,args = strip_comb tm
    and prov = prov_of_tm s in
    if (comb = `LinTimes`) then provtimes ((prov o hd) args) ((prov o hd o tl) args)
    else if (comb = `LinPlus`) then provplus ((prov o hd) args) ((prov o hd o tl) args)
    else if (length args > 1) then Provnode(string_of_term comb,(prov o hd) args,(prov o hd o tl) args)
    else if (length args = 1) then (prov o hd) args
    else Provleaf(s);;

let timesprov nl nr n pm =
  try (
    let pl = assoc nl pm
    and pr = assoc nr pm in
    assoc_add n (provtimes pl pr) pm )
  with Failure _ -> pm;;

let plusprov nl nr n pm =
  try (
    let pl = assoc nl pm
    and pr = assoc nr pm in
    assoc_add n (provplus pl pr) pm )
  with Failure _ -> pm;;

let timesprov_r nl pr n pm =
  try (
    let pl = assoc nl pm in
    assoc_add n (provtimes pl pr) pm )
  with Failure _ -> pm;;

let timesprov_l pl nr n pm =
  try (
    let pr = assoc nr pm in
    assoc_add n (provtimes pl pr) pm )
  with Failure _ -> pm;;

let plusprov_r nl pr n pm =
  try (
    let pl = assoc nl pm in
    assoc_add n (provplus pl pr) pm )
  with Failure _ -> pm;;

let plusprov_l pl nr n pm =
  try (
    let pr = assoc nr pm in
    assoc_add n (provplus pl pr) pm )
  with Failure _ -> pm;;


let prov_follow_path path pt =
  let rec pfp pathlist pt =
    match pathlist with
      | [] -> (
	match pt with
	  | Provleaf s -> Some s
	  | _ -> None)
      | "r" :: tl -> (
	match pt with
	  | Provnode(_,_,r) -> pfp tl r
	  | _ -> None)
      | "l" :: "r" :: tl -> (
	match pt with
	  | Provnode(_,l,_) -> pfp tl l
	  | _ -> None)
      | _ -> None in
  pfp (explode path) pt;;

let rec string_of_prov pt =
  match pt with
    | Provleaf s -> s
    | Provnode(c,l,r) -> c ^ "(" ^ (string_of_prov l) ^ "," ^ (string_of_prov r) ^ ")";;
