(* ========================================================================= 
   An environment to use the Composer at the toplevel.
   
   Petros Papapanagiotou
   Center of Intelligent Systems and their Applications         
   School of Informatics, University of Edinburgh                         
   2019
 ========================================================================= *)

needs (!serv_dir ^ "processes/processes.ml");;
needs (!serv_dir ^ "api/composer.ml");;

module type Composer_console_type =
    sig
      module Composer : Composer_type

      val responses : unit -> Composer.Response.t list

      val add_process : Composer.Process.t -> Composer.Process.t
      val get_process : string -> Composer.Process.t
      val exists_process : string -> bool
      val del_process : string -> unit
      val reset_processes : unit -> unit
      val list : unit -> string list

      val add_intermediate : Composer.Process.t -> Composer.Process.t
      val get_intermediate : string -> Composer.Process.t
      val exists_intermediate : string -> bool
      val del_intermediate : string -> unit
      val reset_intermediates : unit -> unit
      val ilist : unit -> string list

      val get : string -> Composer.Process.t

      val resetstep : unit -> unit
      val reset : unit -> unit
      val full_reset : unit -> unit

      val create : string -> term list -> term -> Composer.Response.t
      val compose1 : Action.t -> Composer.Process.t
      val tensor : string -> string -> Composer.Process.t
      val cwith : string -> string -> string -> string -> Composer.Process.t
      val join : string -> string -> string -> string -> Composer.Process.t

      val store : string -> string -> Composer.Response.t
      val load : string -> unit
    end ;;

module Composer_console_make (Composer : Composer_type) : Composer_console_type =
  struct
    module Composer = Composer

    (* We use a history based on a list in addition to the hash table below so that we 
       can preserve the order in which processes were introduced. This way we don't 
       have to order processes based on dependencies. *)
    let history = ref ([]:Composer.Response.t list)

    let logr r = 
      let hist = !history in
      history := r :: hist

    let logrl = map logr

    let reset_history () = history := []

    let responses () = rev !history


    let processes = Hashtbl.create 50

    let add_process (p:Composer.Process.t) = Hashtbl.add processes p.Composer.Process.name p ; p
    let get_process (s:string) = Hashtbl.find processes s
    let exists_process (s:string) = Hashtbl.mem processes s
    let del_process (s:string) = Hashtbl.remove processes s
    let reset_processes () = Hashtbl.reset processes ; reset_history () 
    let list () = List.of_seq (Hashtbl.to_seq_keys processes)

    let intermediates = Hashtbl.create 50

    let add_intermediate (p:Composer.Process.t) = Hashtbl.add intermediates p.Composer.Process.name p ; p
    let get_intermediate (s:string) = Hashtbl.find intermediates s
    let exists_intermediate (s:string) = Hashtbl.mem intermediates s
    let del_intermediate (s:string) = Hashtbl.remove intermediates s
    let reset_intermediates () = Hashtbl.reset intermediates
    let ilist () = List.of_seq (Hashtbl.to_seq_keys intermediates)

    let get (s:string) = 
      try ( get_process s )
      with _ -> get_intermediate s

    let stepctr = ref 0

    let incstep () =
      let count = !stepctr in
      (stepctr := count + 1;
       count)

    let decstep () =
      let count = !stepctr in
      (stepctr := count - 1;
       count)

    let resetstep () = stepctr := 0

    let getstep () =
      "_Step" ^ (string_of_int (incstep()))



    let reset () =
      resetstep ();
      reset_intermediates()

    let full_reset () =
      resetstep ();
      reset_intermediates();
      reset_processes()

    let create name ins out =
      if (exists_process name) then warn true ("Process " ^ name ^ " already exists.") ;
      let r = Composer.create name ins out in
      match r with
      | Composer.Response.Create p -> ( logr r ; add_process p ; r )
      | _ -> r

    let compose1 act =
      let lp = get act.Action.larg
      and rp = get act.Action.rarg in
      let (p,_) = Composer.Process.compose1 act lp rp in
      add_intermediate p

    let tensor lhs rhs =
      let act = Action.create "TENSOR" lhs "" rhs "" (getstep())
      and lp = get lhs
      and rp = get rhs in
      let (p,_) = Composer.Process.compose1 act lp rp in
      add_intermediate p

    let cwith lhs lsel rhs rsel =
      let act = Action.create "WITH" lhs lsel rhs rsel (getstep())
      and lp = get lhs
      and rp = get rhs in
      let (p,_) = Composer.Process.compose1 act lp rp in
      add_intermediate p

    let join lhs lsel rhs rsel =
      let act = Action.create "JOIN" lhs lsel rhs rsel (getstep())
      and lp = get lhs
      and rp = get rhs in
      let (p,_) = Composer.Process.compose1 act lp rp in
      add_intermediate p

    let components p = (map get o Action.root_deps) p.Composer.Process.actions

    let rename_act old name act = 
      if (act.Action.res = old) 
      then ({ act with Action.res = name }:Action.t)
      else act

    let rec all_actions rename p = 
      let icomps = filter (fun p -> p.Composer.Process.intermediate) (components p) in
      let acts = flat (map (all_actions None) icomps) in
      match rename with
      | None -> acts @ p.Composer.Process.actions
      | Some(name) -> acts @ (map (rename_act p.Composer.Process.name name) p.Composer.Process.actions)

    let store iname name =
      let p = get iname in
      let acts = all_actions (Some name) p in
      let deps = (map get o Action.root_deps) acts in
      let results = Composer.compose name deps acts in
      let final r =
        match r with
        | Composer.Response.Compose(_,a,_) when a.Action.res = name -> true
        | _ -> false in
      if (results = []) 
      then failwith "Compose.compose returned no responses"
      else 
        try (
          let fail = find Composer.Response.failed results in
          fail 
        ) with Failure "find" ->
                try ( 
                  let Composer.Response.Compose(p,_,_) as r = find final results in
                  ( logrl results ; add_process p ; r )
                ) with Failure _ -> last results

    let load name = 
      reset ();
      (ignore o map compose1) (get name).Composer.Process.actions
  end;;


 
