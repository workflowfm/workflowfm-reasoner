(* ========================================================================= *)
(* WorkflowFM server loader for JSON output.                                 *)
(*                                                                           *)
(*                           Petros Papapanagiotou                           *)
(*                          University of Edinburgh                          *)
(*                                 2009-2016                                 *)
(* ========================================================================= *)

let serv_dir = ref (!hol_dir ^ "/services/dev/");;

needs (!serv_dir ^ "make.ml");;


(* = JSON interface = *)

loads (!serv_dir ^ "json/make.ml");;

module Cmpsr = Json_composer(Proc);;

Command.add "create" Cmpsr.create_process;;
Command.add "compose1" Cmpsr.compose1;;
Command.add "compose" Cmpsr.compose;;

let piviz_deploy p ds = ["result",Piviz.deploy p ds] in
    Command.add "piviz" (Cmpsr.deploy "PiViz" piviz_deploy);;
