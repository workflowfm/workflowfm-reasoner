(* ========================================================================= *)
(* JSON interface for external tools such as the composer GUI.               *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                2012 - 2016                                *)
(* ========================================================================= *)

needs (!serv_dir ^ "CLL/CLL.ml");;
needs (!serv_dir ^ "processes/actions.ml");;
needs (!serv_dir ^ "processes/processes.ml");;
needs (!serv_dir ^ "json/lib.ml");;

module Cll_json = 
  struct
  open Json_type.Browse
				          
  let rec from_linprop tm =
    let rec mysplitlist dest x =
      try let l,r = dest x in
	  let res = mysplitlist dest r in
      (l::res)
      with Failure _ -> [x] in

    if (is_var tm or is_const tm) then 
    (Object[
     ("type", String "var");
     ("name", String (string_of_term tm))])
    else
    
    let op,args = strip_comb tm in
    let op_string =
      if (op = `NEG`) then "neg"
      else if (op = `LinTimes`) then "times"
      else if (op = `LinPlus`) then "plus"
      else failwith ("Cll_json.from_linprop: Unexpected operator - " ^ (string_of_term op))
    in
    let args' = 
      if (op = `NEG`) then args
      else if (op = `LinTimes`) then mysplitlist (dest_binop op) tm
      else if (op = `LinPlus`) then mysplitlist (dest_binop op) tm
      else failwith ("Cll_json.from_linprop: Unexpected operator - " ^ (string_of_term op))
    in
    
    let jargs = "args",Array (map from_linprop args') in
    Object [ ("type", String op_string) ; jargs ]

  let rec to_linprop j =
    let tbl = make_table (objekt j) in
    let op_string = String.lowercase (string (field tbl "type")) in
    if (op_string = "var") then mk_var (string (field tbl "name"),`:LinProp`)
    else
    let args = list to_linprop (field tbl "args") in
    match op_string with
	"neg" -> mk_comb (`NEG`,hd args)
      | "times" -> list_mk_binop `LinTimes` args
      | "plus" -> list_mk_binop `LinPlus` args
      | _ -> failwith ("Cll_json.to_linprop: Unexpected operator - " ^ op_string)
   
		
  let from_linterm tm =
    let cll,chan = (rand o rator) tm,rand tm in
    Object [("channel", String (string_of_term chan));
	    ("cll", from_linprop cll)]

  let to_linterm to_chan j =
    let tbl = make_table (objekt j) in
    let cll = to_linprop (field tbl "cll")
    and channel = (to_chan o string) (field tbl "channel") in
    mk_icomb (mk_comb (`LL`,cll),channel)
(* TODO this assumes LL is already defined when this file is loaded. *)

	     
  let from_iopair prop,chan =
    Object [("channel", String (string_of_term chan));
	    ("cll", from_linprop prop)]

  let to_iopair to_chan j =
    let tbl = make_table (objekt j) in
    let cll = to_linprop (field tbl "cll")
    and channel:term = (to_chan o string) (field tbl "channel") in
    cll,channel

	
  let from_action (act:Action.t) =
    Object [
      ("act", String act.Action.act);
      ("larg", String act.Action.larg);
      ("lsel", String act.Action.lsel);
      ("rarg", String act.Action.rarg);
      ("rsel", String act.Action.rsel);
      ("res", String act.Action.res)]

  let to_action j =
    let tbl = make_table (objekt j) in
    let act = string (field tbl "act")
    and larg = string (field tbl "larg")
    and lsel = string (field tbl "lsel")
    and rarg = string (field tbl "rarg")
    and rsel = string (field tbl "rsel")
    and res = string (field tbl "res") in
    Action.create act larg lsel rarg rsel res


  let rec from_prov pt =
    let dest tp pt =
      match pt with
	| Provleaf s -> failwith ""
	| Provnode(op,l,r) -> if (op = tp) then l,r else failwith "" in
    let rec mysplitlist tp x =
      try let l,r = dest tp x in
	  let res = mysplitlist tp r in
      (l::res)
      with Failure _ -> [x] in
 
    match pt with
      | Provleaf s ->
	(Object[
	  ("type", String "source");
	  ("name", String s)])
      | Provnode(op,l,r) ->
	  let args = mysplitlist op pt in
	(Object[
	  ("type", String op);
	  ("args", Array (map from_prov args))])   
	
  let rec to_prov j =
    let rec list_mk_prov tp h args =
      match args with
	| [] -> h
	| ha::t -> Provnode(tp,h,list_mk_prov tp ha t) in
    
    let tbl = make_table (objekt j) in
    let op_string = String.lowercase (string (field tbl "type")) in
    if (op_string = "source") then Provleaf (string (field tbl "name"))
    else
      let args = list to_prov (field tbl "args") in
      list_mk_prov op_string (hd args) (tl args)

  let from_prov_entry (n,p) =
    Object [
      ("name", String n);
      ("prov", from_prov p)]

  let to_prov_entry j =
    let tbl = make_table (objekt j) in
    string (field tbl "name"), to_prov (field tbl "prov")

  let from_iprov_entry (n,p) =
    Object [
      ("term", from_linprop n);
      ("prov", from_prov p)]

  let to_iprov_entry j =
    let tbl = make_table (objekt j) in
    to_linprop (field tbl "term"), to_prov (field tbl "prov")

  let from_actionstate (st:Actionstate.t) =
    Object [
    ("ctr", Int st.Actionstate.ctr);
    ("buffered", Array (map from_linprop st.Actionstate.buffered));
    ("joined", Array (map from_linterm st.Actionstate.joined));
    ("iprov", Array (map from_iprov_entry st.Actionstate.iprov));
    ("prov", Array (map from_prov_entry st.Actionstate.prov))]
	   
  let to_actionstate to_chan j =
    let tbl = make_table (objekt j) in
    let ctr = int (field tbl "ctr")
    and buffered = list to_linprop (field tbl "buffered") 
    and joined = list (to_linterm to_chan) (field tbl "joined")
    and iprov = list to_iprov_entry (field tbl "iprov")
    and prov = list to_prov_entry (field tbl "prov") in
    ({ Actionstate.ctr = ctr ;
       Actionstate.metas = [] ;
       Actionstate.buffered = buffered ;
       Actionstate.joined = joined ;
       Actionstate.iprov = iprov ;
       Actionstate.prov = prov}:Actionstate.t)
  end;;




module Json_composer (Process:Process_type) =
  struct
  include Cll_json
  open Json_type.Browse

  let to_linterm j = Cll_json.to_linterm Process.mk_chan j
  let to_iopair j = Cll_json.to_iopair Process.mk_chan j
  let to_actionstate j = Cll_json.to_actionstate Process.mk_chan j
						 
  let from_agent a = String (string_of_term a) (* TODO: Is that good enough? *)

  let to_agent j = try (
    let op,arg = (dest_comb o parse_term o string) j in
    let tm = mk_icomb (op,Proc.try_proc_type arg) in
    let tinst = (map (fun x -> Proc.chantp,x) o filter is_vartype o map type_of o frees) tm in
    inst tinst tm
  ) with Failure _ -> failwith "Json_composer.to_agent: failed to parse agent definition" 
						 
  let from_process (p:Process.t) =
    Object [
      ("name", String p.Process.name);
      ("inputs", Array (map from_iopair p.Process.inputs));
      ("output", from_iopair p.Process.output);
      ("proc", from_agent p.Process.proc);
      ("actions", Array (map from_action p.Process.actions));
      ("copier", Bool p.Process.copier);
      ("intermediate", Bool p.Process.intermediate)]

  let to_process j =
    let tbl = make_table (objekt j) in
    let name = string (field tbl "name")
    and inputs = list to_iopair (field tbl "inputs")
    and output = to_iopair (field tbl "output")
    and proc = to_agent (field tbl "proc")
    and actions = list to_action (field tbl "actions")
    and copier = bool (field tbl "copier")
    and intermediate = bool (field tbl "intermediate") in
    ({Process.name = name; 
      Process.inputs = inputs ;
      Process.output = output ;
      Process.proc = proc ;
      Process.actions = actions ;
      Process.copier = copier ;
      Process.intermediate = intermediate ;
     }:Process.t)


    
  let create_process j =
    let tbl = make_table (objekt j) in
    let name = string (field tbl "name")
    and inputs = list to_linprop (field tbl "inputs")
    and output = to_linprop (field tbl "output") in

    let p = Process.create name inputs output in
    [Object [
    ("response", String "CreateProcess");
    ("process", from_process p);
    ]]

				    

  let composition_result (act:Action.t) (p:Process.t) (st:Actionstate.t) =
 (*   let tp = match  act.Action.act with
	"JOIN" -> "Join"
      | "WITH" -> "With"
      | "TENSOR" -> "Tensor"
      | _ -> act.Action.act in*)
    Object [
    ("response", String "Compose");
    ("action", from_action act);
    ("process", from_process p);
    ("state", from_actionstate st);
    ]

  let compose1 j =
    let tbl = make_table (objekt j) in
    let act = to_action (field tbl "action")
    and lhs = to_process (field tbl "lhs")
    and rhs = to_process (field tbl "rhs")
    and state = to_actionstate (field tbl "state") in
    
    let p,s = Process.compose1 act state lhs rhs in
    [composition_result act p s]


  let verify j =
    let tbl = make_table (objekt j) in
    let name = string (field tbl "name")
    and deps = list to_process (field tbl "components")
    and acts = list to_action (field tbl "actions")
    (* and res = string (field tbl "result") *)
    and state = to_actionstate (field tbl "state") in

    let p,_,s = Process.compose state name deps acts in
    [Object [
      ("response", String "Verify");
      ("process", from_process p);
      ("state", from_actionstate s)]]
      (* ("composition", String res)]] *)

  let compose j =
    let tbl = make_table (objekt j) in
    let name = string (field tbl "name")
    and deps = list to_process (field tbl "components")
    and acts = list to_action (field tbl "actions")
    (* and res = string (field tbl "result") *)
    and state = to_actionstate (field tbl "state") in

    if (acts = []) then [] else
      let p,inters,s = Process.compose state name deps acts in
      let comp_res (a,(s,p)) = composition_result a p s in
      map comp_res (zip acts inters)
      (* let res = (composition_result (last acts) p s) :: (map comp_res (zip acts inters)) in
      rev res (* This sends 2 results for the last action, but that's ok. *) *)
		       
  let deploy tp f j =
    let tbl = make_table (objekt j) in
    let proc = to_process (field tbl "process")
    and deps = list to_process (field tbl "components") in
    let res = f proc deps in
    let mk_res l,r = l, String r in
    [Object [
     ("response", String (tp ^ "Deploy"));
     ("deployment", Object (map mk_res res))]]
		       
end;;

(*  
(**** scala deployment output ****)  
  
let json_of_deploymentfile overwrite (path,content) =
  (Object [
    ("path", String path);
    ("content", String content);
    ("overwrite", Bool overwrite)]);;
    
let scala_deploy_json separator path package project name main java =
  let overwrite,optional = scala_deploy separator path package project name main java in
  let files = (map (json_of_deploymentfile true) overwrite) @ (map (json_of_deploymentfile false) optional) in
  print_json
    (Object [
     ("response", String "DeployAction");
     ("files", Array files)]);;

 *)

