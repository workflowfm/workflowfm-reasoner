(* ========================================================================= 
   A modular API for the Composer 
   - This describes a codec that encodes/decodes data for the composer in a
   specified type (encodet). 
   - Commands can be added in a modular way.
   - The API module handles commands and encodes responses.
   
   Petros Papapanagiotou
   Center of Intelligent Systems and their Applications         
   School of Informatics, University of Edinburgh                         
   2019
 ========================================================================= *)

needs (!serv_dir ^ "api/composer.ml");;

module type Codec_type =
  sig
    type encodet 
    type proc
    module Encode :
    sig
      val prop : term -> encodet
      val term : term -> encodet
      val act : Action.t -> encodet
      val prov : provtree -> encodet
      val prov_entry : string * provtree -> encodet
      val iprov_entry : term * provtree -> encodet
      val actionstate : Actionstate.t -> encodet
      val agent : term -> encodet
      val iopair : term * term -> encodet
      val process : proc -> encodet
    end
    module Decode :
    sig
      val prop : encodet -> term
      val act : encodet -> Action.t
      val prov : encodet -> provtree
      val prov_entry : encodet -> string * provtree
      val iprov_entry : encodet -> term * provtree
      val term : encodet -> term
      val actionstate : encodet -> Actionstate.t
      val agent : encodet -> term
      val iopair : encodet -> term * term
      val process : encodet -> proc
    end
  end;;

module type Command_store_type =
  sig
    type encodet
    val get_all : unit -> (encodet -> encodet list) list
    val names : unit -> string list
    val get : string -> encodet -> encodet list
    val delete : string -> unit
    val add : string -> (encodet -> encodet list) -> unit
  end;;

module Command_store ( Codec : Codec_type ) : Command_store_type with type encodet = Codec.encodet = 
  struct
    type encodet = Codec.encodet
    module Commandmap = Map.Make(String)

    let commands = ref Commandmap.empty;;
	
    let get_all () = Commandmap.fold (fun k v l -> (v::l)) (!commands) []
                   
    let names () = Commandmap.fold (fun k v l -> (k::l)) (!commands) []
                 
    let get name = try ( Commandmap.find (String.lowercase name) (!commands) )
		           with Not_found -> failwith ("No such command '" ^ name ^ "'")

    let delete name = commands := Commandmap.remove name (!commands)
                    
    let (add:Commandmap.key->(Codec.encodet -> Codec.encodet list)->unit) =
      fun name cmd ->
      let name = String.lowercase name in 
      warn (try (let _ = get name in true) with Failure _ -> false)
	    ("Command.add: Overwriting command '" ^ name ^ "'.") ;
      commands := Commandmap.add name cmd (!commands)

end;;

module type Composer_api =
  sig
    include Composer_type
    include Codec_type with type proc = Process.t
    module Commands : Command_store_type with type encodet = encodet

    val response : Response.t -> encodet 
    val execute : encodet -> encodet list
  end;;
					 			    
