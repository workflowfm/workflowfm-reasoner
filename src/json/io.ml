(* ========================================================================= *)
(* JSON interface for external tools such as the composer GUI.               *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                2015 - 2016                                *)
(* ========================================================================= *)

needs (!serv_dir ^ "processes/actions.ml");;
needs (!serv_dir ^ "processes/processes.ml");;
needs (!serv_dir ^ "json/lib.ml");;
needs (!serv_dir ^ "json/commands.ml");;

module Json_composer_io = 
  struct
  open Json_type.Browse
       
  let print j =
    print_string "\nJSON_START\n";
    print_string (Json_io.string_of_json j);
    print_string "\nJSON_END\n"
	       
  let string_result s = (Object [("result", String s)])

  let except e =
    let a,s = match e with
      | Failure f -> "CommandFailed",f
      | _ -> "Exception",Printexc.to_string e in
    (print
     (Object [
      ("response", String a);
      ("content", String s)]))
  
  let exec_fun f = try f () with e -> (except e ; raise e)

  let input j =
    let tbl = make_table (objekt j) in
    let name = string (field tbl "command") in
    (Json_command.get name) j

  let execute_json j =
    try (
      let res = input j in
      ignore (map print res)
    ) with e -> (except e ; raise e)

  let execute_file s = execute_json (Json_io.load_json s)
  let execute s = execute_json (Json_io.json_of_string s)
		
end;;
