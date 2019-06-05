(* ========================================================================= 
   JSON Composer API         
   
   Petros Papapanagiotou
   Center of Intelligent Systems and their Applications         
   School of Informatics, University of Edinburgh                         
   2019
 ========================================================================= *)

needs (!serv_dir ^ "api/api.ml");;
needs (!serv_dir ^ "api/json/lib.ml");;
needs (!serv_dir ^ "api/json/codecs.ml");;

module type Composer_json_api = Composer_api with type encodet = Json_type.json_type;; 

module Json_api_make (Composer:Composer_type) : Composer_json_api =
  struct
    open Json_type.Browse
    include Composer
    module Codec = Json_codec(Process) 
    include Codec
    module Commands = Command_store_make(Codec)

    let response (r:Response.t) : encodet = match r with
          | Ping t -> 
             Object [
                 ("response", String "Pong");
                 ("ping", Float t);
               ]

          | Create p ->             
             Object [
                 ("response", String "CreateProcess");
                 ("process", Encode.process p);
               ]

          | Compose (p,act,state) ->   
             Object [
                 ("response", String "Compose");
                 ("action", Encode.act act);
                 ("process", Encode.process p);
                 ("state", Encode.actionstate state);
               ]          

          | Verify p -> 
             Object [
                 ("response", String "Verify");
                 ("process", Encode.process p)
               ]

          | Deploy (s,l) -> 
             let file (path,content,overwrite) = 
               Object [
                   ("path", String path);
                   ("content", String content);
                   ("overwrite", Bool overwrite)
                 ] in
             
             Object [
                 ("response", String (s ^ "Deploy"));
                 ("deployment", Array (map file l))
               ]
             
          | Failed s -> 
             Object [
                 ("response", String "CommandFailed");
                 ("content", String s)
               ]

          | Exception s -> 
             Object [
                 ("response", String "Exception");
                 ("content", String s)
               ]
       
    let execute (j:encodet) : encodet list = 
      let tbl = make_table (objekt j) in
      try (
        let f = Commands.get (string (field tbl "command")) in
        f j
      ) with e -> [ response (except e) ]

  end;;



module Json_commands (Composer : Composer_json_api) =
  struct
    open Json_type.Browse
    open Composer

    let ping j =
      let tbl = make_table (objekt j) in
      let time = float (field tbl "ping") in
      [ response (ping time) ]

    let create j =
      let tbl = make_table (objekt j) in
      let name = string (field tbl "name")
      and inputs = list Decode.prop (field tbl "inputs")
      and output = Decode.prop (field tbl "output") in
      [ response (create name inputs output) ]

    let compose1 j =
      let tbl = make_table (objekt j) in
      let act = Decode.act (field tbl "action")
      and lhs = Decode.process (field tbl "lhs")
      and rhs = Decode.process (field tbl "rhs")
      and state = Decode.actionstate (field tbl "state") in
      [ response (compose1 lhs rhs act state) ]

    let compose j =
      let tbl = make_table (objekt j) in
      let name = string (field tbl "name")
      and deps = list Decode.process (field tbl "components")
      and acts = list Decode.act (field tbl "actions")
      and state = Decode.actionstate (field tbl "state") in
      map response (compose name deps acts state)

    let verify j =
      let tbl = make_table (objekt j) in
      let name = string (field tbl "name")
      and deps = list Decode.process (field tbl "components")
      and acts = list Decode.act (field tbl "actions")
      and state = Decode.actionstate (field tbl "state") in
      [ response (verify name deps acts state) ]
        
    let load () = 
      (ignore o map (uncurry Commands.add)) [
          ("ping",ping);
          ("create",create);
          ("compose1",compose1);
          ("compose",compose);
          ("verify",verify)
        ]
  end ;;

