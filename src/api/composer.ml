(* ========================================================================= 
   Composer Interface
   - Streamlines the core functionality of the Reasoner
        
   Petros Papapanagiotou                  
   Center of Intelligent Systems and their Applications         
   School of Informatics, The University of Edinburgh                         
   2019                                
 ========================================================================= *)

needs (!serv_dir ^ "CLL/CLL.ml");;
needs (!serv_dir ^ "processes/actions.ml");;
needs (!serv_dir ^ "processes/processes.ml");;

module type Composer_type = 
  sig
    module Process : Process_type

    module Response :
      sig
        type t = 
          | Ping of float
          | Create of Process.t
          | Compose of Process.t * Action.t * Actionstate.t
          | Verify of Process.t
          | Deploy of string * (string * string * bool) list (* Path, Content, Overwrite *)
          | Failed of string
          | Exception of string 
        val name : t -> string
        val failed : t -> bool
      end

    val ping : float -> Response.t
    val create : string -> term list -> term -> Response.t
    val compose1 : Process.t -> Process.t -> Action.t -> Actionstate.t -> Response.t
    val compose : string -> Process.t list -> Action.t list -> Actionstate.t -> Response.t list
    val verify : string -> Process.t list -> Action.t list -> Actionstate.t -> Response.t 
    val except : exn -> Response.t
   end;;

module Composer_make (Proc:Process_type): Composer_type with module Process = Proc =
  struct
    module Process = Proc

    module Response =
      struct
        type t = 
          | Ping of float
          | Create of Process.t
          | Compose of Process.t * Action.t * Actionstate.t
          | Verify of Process.t
          | Deploy of string * (string * string * bool) list
          | Failed of string
          | Exception of string 

        let name r = match r with
          | Ping _ -> "Ping"
          | Compose _ -> "Compose"
          | Create _ -> "CreateProcess"
          | Verify _ -> "Verify"
          | Deploy (n,_) -> n ^ "Deploy"
          | Failed _ -> "CommandFailed"
          | Exception _ -> "Exception" 

        let failed r = match r with
          | Ping _ -> false
          | Compose _ -> false
          | Create _ -> false
          | Verify _ -> false
          | Deploy _ -> false
          | Failed _ -> true
          | Exception _ -> true

      end

    let except : exn -> Response.t = 
      fun e -> match e with
               | Failure f -> Failed f
               | _ -> Exception (Printexc.to_string e)

    let ping : float -> Response.t =
      fun t -> Ping t

    let create : string -> term list -> term -> Response.t =
      fun name inputs output -> 
      try (
        let p = Process.create name inputs output in
        Create p 
      ) with e -> except e

    let compose1 : Process.t -> Process.t -> Action.t -> Actionstate.t -> Response.t = 
      fun lhs rhs action state ->
      try (
      let p,s = Process.compose1 action state lhs rhs in
      Compose (p,action,s)
      ) with e -> except e

    let compose : string -> Process.t list -> Action.t list -> Actionstate.t -> Response.t list =
      fun name procs actions state -> 
      try (
        if (actions = []) then [] else
          let p,inters,s = Process.compose state name procs actions in
          let res (a,(s,p)) = Response.Compose (p,a,s) in
          map res (zip actions inters)                 
      ) with e -> [ except e ]

    let verify : string -> Process.t list -> Action.t list -> Actionstate.t -> Response.t =
      fun name procs actions state -> 
      try (
        let p,_,_ = Process.compose state name procs actions in
        Verify p        
      ) with e -> except e

end ;;

(*(* Testing:*)
module Comp = Composer_make(Proc);;
let myst = Actionstate.create "TEST" 0;;
let rec add_provs procs st =
    match procs with
      | [] -> st
      | p :: t ->
	let n,prov = Proc.get_atomic_prov p in
	add_provs t (Actionstate.add_prov n prov st);;

Comp.ping 0.1;;
let Comp.Response.Create p1 = Comp.create "Hi1" [`A`;`B`] `C` ;;
let Comp.Response.Create p2 = Comp.create "Hi2" [`C`;`D`] `E` ;;
let Comp.Response.Create p3 = Comp.create "Hi3" [`E`;`F`] `G` ;;
let myact1 = Action.create "JOIN" "Hi1" "" "Hi2" "(NEG C)" "R1";;
let myact2 = Action.create "JOIN" "R1" "" "Hi3" "(NEG E)" "R2";;
let myactEX = Action.create "JOIN" "Hi1" "" "Hi2" "(NEG E)" "R";;
Comp.compose1 p1 p2 myact1 (add_provs[p1;p2] myst);;
Comp.compose "R2" [p1;p2;p3] [myact1;myact2] (add_provs[p1;p2;p3] myst);;
Comp.verify "R2" [p1;p2;p3] [myact1;myact2] (add_provs[p1;p2;p3] myst);;
Comp.compose1 p1 p2 myactEX (add_provs[p1;p2] myst);;
*)

