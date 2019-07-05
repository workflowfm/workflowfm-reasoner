(* ========================================================================= *)
(* JSON Input/Output                                                         *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                2015 - 2019                                *)
(* ========================================================================= *)

needs (!serv_dir ^ "processes/actions.ml");;
needs (!serv_dir ^ "processes/processes.ml");;
needs (!serv_dir ^ "api/json/lib.ml");;
needs (!serv_dir ^ "api/json/api.ml");;

module Json_composer_io_make (Api : Composer_json_api) = 
  struct
  open Json_type.Browse 
  module Api = Api

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


