(* ========================================================================= 
   Composer API                                      
        
   Petros Papapanagiotou                  
   Center of Intelligent Systems and their Applications         
   School of Informatics, The University of Edinburgh                         
   2019                                
 ========================================================================= *)

needs (!serv_dir ^ "CLL/CLL.ml");;
needs (!serv_dir ^ "processes/actions.ml");;
needs (!serv_dir ^ "processes/processes.ml");;

module Composer (Process:Process_type) =
  struct
    module Command =
      struct
        (* TODO deployment commands: 
let piviz_deploy p ds = ["result",Piviz.deploy p ds] in
    Json_command.add "piviz" (Json_comp.deploy "PiViz" piviz_deploy);;

Json_command.add "pilib" Json_pilib.scaldeploy;;
Json_command.add "pilibstateful" Json_pilib.scaldeploystateful;;

         *)
        type t =
          | Ping of float
          | Create of string * term list * term
          | Compose1 of Process.t * Process.t * Action.t * Actionstate.t
          | Compose of string * Process.t list * Action.t list * Actionstate.t
          | Verify of string * Process.t list * Action.t list * Actionstate.t

        let name c = match c with
          | Ping _ -> "Ping"
          | Create _ -> "CreateProcess"
          | Compose1 _ -> "Compose1"
          | Compose _ -> "Compose"
          | Verify _ -> "Verify"
      end

    module Response =
      struct
        type t = (* TODO: Deployment responses *)
          | Ping of float
          | Create of Process.t
          | Compose of Process.t * Action.t * Actionstate.t
          | Verify of Process.t
          | Failed of string
          | Exception of string 

        let name r = match r with
          | Ping _ -> "Ping"
          | Compose _ -> "Compose"
          | Create _ -> "CreateProcess"
          | Verify _ -> "Verify"
          | Failed _ -> "CommandFailed"
          | Exception _ -> "Exception" 
      end

    let except : exn -> Response.t = 
      fun e -> match e with
               | Failure f -> Failed f
               | _ -> Exception (Printexc.to_string e)
      
    let execute : Command.t -> Response.t list =
      fun c -> try ( match c with
               | Ping t -> [ Ping t ]

               | Create (name,inputs,output) -> 
                  let p = Process.create name inputs output in
                  [ Create p ]

               | Compose1 (lhs,rhs,action,state) -> 
                  let p,s = Process.compose1 action state lhs rhs in
                  [ Compose (p,action,s) ]

               | Compose (name,procs,actions,state) ->
                  if (actions = []) then [] else
                    let p,inters,s = Process.compose state name procs actions in
                    let res (a,(s,p)) = Response.Compose (p,a,s) in
                    map res (zip actions inters)                 

               | Verify (name,procs,actions,state) ->
                  let p,_,_ = Process.compose state name procs actions in
                  [ Verify p ]
                   ) with e -> [ except e ]
end ;;

(* (* Testing:*)
module Comp = Composer(Proc);;
let myst = Actionstate.create "TEST" 0;;
let rec add_provs procs st =
    match procs with
      | [] -> st
      | p :: t ->
	let n,prov = Proc.get_atomic_prov p in
	add_provs t (Actionstate.add_prov n prov st);;

Comp.execute (Ping 0.1);;
let [Comp.Response.Create p1] = Comp.execute (Create ("Hi1",[`A`;`B`],`C`));;
let [Comp.Response.Create p2] = Comp.execute (Create ("Hi2",[`C`;`D`],`E`));;
let [Comp.Response.Create p3] = Comp.execute (Create ("Hi3",[`E`;`F`],`G`));;
let myact1 = Action.create "JOIN" "Hi1" "" "Hi2" "(NEG C)" "R1";;
let myact2 = Action.create "JOIN" "R1" "" "Hi3" "(NEG E)" "R2";;
let myactEX = Action.create "JOIN" "Hi1" "" "Hi2" "(NEG E)" "R";;
Comp.execute (Compose1 (p1,p2,myact1,add_provs[p1;p2] myst));;
Comp.execute (Compose ("R2",[p1;p2;p3],[myact1;myact2],add_provs[p1;p2;p3] myst));;
Comp.execute (Verify ("R2",[p1;p2;p3],[myact1;myact2],add_provs[p1;p2;p3] myst));;
Comp.execute (Compose1 (p1,p2,myactEX,add_provs[p1;p2] myst));;
*)
