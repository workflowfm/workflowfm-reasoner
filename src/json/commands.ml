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

module Json_command = struct

  module Commandmap = Map.Make(String)


  type t =  Json_type.json_type -> Json_type.json_type list

  let commands = ref Commandmap.empty;;
				  
  let get_all () = Commandmap.fold (fun k v l -> (v::l)) (!commands) []
  
  let names () = Commandmap.fold (fun k v l -> (k::l)) (!commands) []
  
  let get name = try ( Commandmap.find (String.lowercase name) (!commands) )
		 with Not_found -> failwith ("No such command '" ^ name ^ "'")

  let delete name = commands := Commandmap.remove name (!commands)
  
  let (add:Commandmap.key->t->unit) =
    fun name cmd ->
    let name = String.lowercase name in 
    warn (try (let _ = get name in true) with Failure _ -> false)
	 ("Command.add: Overwriting command '" ^ name ^ "'.") ;
    commands := Commandmap.add name cmd (!commands)

end;;


