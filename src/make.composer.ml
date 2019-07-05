(* ========================================================================= 
   Basic loader for the core composer stuff: CLL/pi-calculus/processes
        
   Petros Papapanagiotou                  
   Center of Intelligent Systems and their Applications         
   School of Informatics, The University of Edinburgh                         
   2009 - 2019                                
 ========================================================================= *)

(* = Core = *)

loads (!serv_dir ^ "processes/processes.ml");;
loads (!serv_dir ^ "CLL/tactics.ml");;


(* = Proofs-as-processes = *)

loads (!serv_dir ^ "pap/pap.ml");;

Cllpi.hide_procs();;

module Proc = Process(Cllpi);;


(* = Load Actions = *)

module Clltac = Clltactics(Cllpi);;
Action.add "JOIN" Clltac.JOIN_TAC;;
Action.add "TENSOR" Clltac.TENSOR_TAC;;
Action.add "WITH" Clltac.WITH_TAC;;


(* = Initialisation = *)

type_invention_warning := false;;

hide_constant "F";;
hide_constant "I";;
hide_constant "T";;


(* = Startup Composer = *)

loads (!serv_dir ^ "api/composer.ml");;

module Composer = Composer_make(Proc);;


(* = Deployment: PiViz, PiLib, PEW = *)

loads (!serv_dir ^ "pap/deploy/piviz.ml");;
loads (!serv_dir ^ "pap/deploy/pilib.ml");;
loads (!serv_dir ^ "pap/deploy/pew.ml");;
