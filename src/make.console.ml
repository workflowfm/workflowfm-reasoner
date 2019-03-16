(* ========================================================================= *)
(* WorkflowFM server basic loader for HOL Light console usage.               *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                          University of Edinburgh                          *)
(*                                 2009-2015                                 *)
(* ========================================================================= *)

let serv_dir = ref (!hol_dir ^ "/services/dev/");;

needs (!serv_dir ^ "make.ml");;

module Clltac = Clltactics(Cllpi);;

Action.add "JOIN" Clltac.JOIN_TAC;;
Action.add "TENSOR" Clltac.TENSOR_TAC;;
Action.add "WITH" Clltac.WITH_TAC;;

module Cmpsr = Composer(Cllpi);;
module Cenv = Compose_environment(Cmpsr);;

module Piviz = Piviz_make(Cmpsr);;
let piviz_deploy id name = Piviz.deploy (Cenv.get id) name;;


