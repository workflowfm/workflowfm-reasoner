(* ========================================================================= 
   JSON Export of Console responses
  
   Petros Papapanagiotou
   Center of Intelligent Systems and their Applications         
   School of Informatics, University of Edinburgh                         
   2019
 ========================================================================= *)

needs (!serv_dir ^ "api/json/api.ml");;
loads (!serv_dir ^ "api/console.ml");;

module Json_console_make (Console : Composer_console_type ) : sig
  val json_responses : unit -> Json_type.json_type
  val store_responses : string -> unit
  val run_file : string -> unit
end = 
  struct
    
    module Json_api : Composer_json_api with module Composer = Console.Composer
      = Json_api_make(Console.Composer) 
    open Json_type.Browse
 
    let json_responses () = Array (map Json_api.response (Console.responses ()))
    
    let store_responses file = Json_io.save_json file (json_responses ())
    
    let run_file file = 
      Console.full_reset () ; 
      use_file file ;
      store_responses ((Filename.remove_extension file) ^ ".json")
end;;
