(* ========================================================================= 
   Loader for a console Composer                                
        
   Petros Papapanagiotou                  
   Center of Intelligent Systems and their Applications         
   School of Informatics, The University of Edinburgh                         
   2009 - 2019                                
 ========================================================================= *)

let serv_dir = ref (!hol_dir ^ "/workflowfm/src/");;

(* = Core = *)

loads (!serv_dir ^ "make.composer.ml");;


(* = Load console = *)

loads (!serv_dir ^ "api/console.ml");;

module Console = Composer_console_make(Composer);;

open Console;;


(* = JSON output (optional) = *)

loads (!serv_dir ^ "api/json/console.ml");;

module Json_console = Json_console_make(Console);;

open Json_console;;
