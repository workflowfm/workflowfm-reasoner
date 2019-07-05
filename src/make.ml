(* ========================================================================= 
   Loader for the Reasoner with the JSON API                                 
        
   Petros Papapanagiotou                  
   Center of Intelligent Systems and their Applications         
   School of Informatics, The University of Edinburgh                         
   2009 - 2019                                
 ========================================================================= *)

let serv_dir = ref (!hol_dir ^ "/workflowfm/src/");;

(* = Core = *)

loads (!serv_dir ^ "make.composer.ml");;


(* = JSON API = *)

loads (!serv_dir ^ "api/json/make.ml");;

module Json_api = Json_api_make(Composer);;


(* = JSON Commands = *)

module Json_comms = Json_commands(Json_api);;
Json_comms.load();;


(* = JSON Deployment Commands = *)

loads (!serv_dir ^ "pap/deploy/json.ml");;

module Json_deploy_comms = Json_deploy_commands(Json_api);;
Json_deploy_comms.load();;


(* = JSON I/O = *)

module Json_composer_io = Json_composer_io_make(Json_api);;
