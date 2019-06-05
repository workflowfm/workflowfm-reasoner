(* ========================================================================= 
   JSON Composer Console 
   - This is designed to accept commands from the console/toplevel and 
   export a list of JSON responses to a file.
  
   Petros Papapanagiotou
   Center of Intelligent Systems and their Applications         
   School of Informatics, University of Edinburgh                         
   2019
 ========================================================================= *)

(* TODO TODO *)

module Json_console_make (Api : Composer_json_api) = 
  struct
  open Json_type.Browse 
  open Api

  let print j =
    print_string "\nJSON_START\n";
    print_string (Json_io.string_of_json j);
    print_string "\nJSON_END\n" 

  let print_file s j = Json_io.save_json s j

  let execute_json j =
      let res = Api.execute j in
      ignore (map print res) ; res

  let execute_file s = execute_json (Json_io.load_json s)
  let execute s = execute_json (Json_io.json_of_string s)
		
end;;
