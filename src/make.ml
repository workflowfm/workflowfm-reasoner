(* ========================================================================= *)
(* Basic loader for all the CLL/pi-calculus/processes stuff.                 *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*                          University of Edinburgh                          *)
(*                                 2009-2018                                 *)
(* ========================================================================= *)

let serv_dir = ref (!hol_dir ^ "/workflowfm/src/");;

(* = Core = *)

loads (!serv_dir ^ "processes/processes.ml");;
loads (!serv_dir ^ "CLL/tactics.ml");;


(* = Proofs-as-processes = *)

loads (!serv_dir ^ "pap/pap.ml");;

Cllpi.hide_procs();;

module Clltac = Clltactics(Cllpi);;
module Proc = Process(Cllpi);;


(* = Scala code extraction = *)

loads (!serv_dir ^ "pap/pilib/pilib.ml");;
loads (!serv_dir ^ "pap/pew.ml");;


(* = Initialisation = *)

Action.add "JOIN" Clltac.JOIN_TAC;;
Action.add "TENSOR" Clltac.TENSOR_TAC;;
Action.add "WITH" Clltac.WITH_TAC;;

type_invention_warning := false;;

hide_constant "F";;
hide_constant "I";;
hide_constant "T";;


(* = PiViz/MWB output = *)

loads (!serv_dir ^ "pap/piviz.ml");;

module Piviz = Piviz_make(Proc);;



(* = JSON interface = *)

loads (!serv_dir ^ "json/make.ml");;

module Json_comp = Json_composer(Proc);;

loads (!serv_dir ^ "pap/pilib/json.ml");;

Json_command.add "create" Json_comp.create_process;;
Json_command.add "compose1" Json_comp.compose1;;
Json_command.add "compose" Json_comp.compose;;
Json_command.add "verify" Json_comp.verify;;

let piviz_deploy p ds = ["result",Piviz.deploy p ds] in
    Json_command.add "piviz" (Json_comp.deploy "PiViz" piviz_deploy);;

Json_command.add "pilib" Json_pilib.scaldeploy;;
Json_command.add "pilibstateful" Json_pilib.scaldeploystateful;;








