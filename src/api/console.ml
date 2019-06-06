(* ========================================================================= 
   An environment to use the Composer at the toplevel.
   
   Petros Papapanagiotou
   Center of Intelligent Systems and their Applications         
   School of Informatics, University of Edinburgh                         
   2019
 ========================================================================= *)

needs (!serv_dir ^ "api/api.ml");;

module type Composer_console_type =
    sig
      module Cprocess : Process_type

      val add_process : Cprocess.t -> Cprocess.t
      val get_process : string -> Cprocess.t
      val exists_process : string -> bool
      val del_process : string -> unit
      val reset_processes : unit -> unit
      val list : unit -> string list

      val add_intermediate : Cprocess.t -> Cprocess.t
      val get_intermediate : string -> Cprocess.t
      val exists_intermediate : string -> bool
      val del_intermediate : string -> unit
      val reset_intermediates : unit -> unit
      val ilist : unit -> string list

      val get : string -> Cprocess.t

      val resetstep : unit -> unit
      val reset : unit -> unit
      val full_reset : unit -> unit

      val create : string -> term list -> term -> Cprocess.t
      val compose1 : Action.t -> Cprocess.t
      val tensor : string -> string -> Cprocess.t
      val cwith : string -> string -> string -> string -> Cprocess.t
      val join : string -> string -> string -> string -> Cprocess.t

      val store : string -> string -> Cprocess.t
      val load : string -> unit
    end ;;

module Composer_console_make (Composer : Composer_type) : Composer_console_type =
  struct
    module Cprocess = Composer.Process

    let processes = Hashtbl.create 50

    let add_process (p:Cprocess.t) = Hashtbl.add processes p.Cprocess.name p ; p
    let get_process (s:string) = Hashtbl.find processes s
    let exists_process (s:string) = Hashtbl.mem processes s
    let del_process (s:string) = Hashtbl.remove processes s
    let reset_processes () = Hashtbl.reset processes
    let list () = List.of_seq (Hashtbl.to_seq_keys processes)

    let intermediates = Hashtbl.create 50

    let add_intermediate (p:Cprocess.t) = Hashtbl.add intermediates p.Cprocess.name p ; p
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
      let p = Cprocess.create name ins out in
      add_process p 

    let compose1 act =
      let lp = get act.Action.larg
      and rp = get act.Action.rarg in
      let (p,_) = Cprocess.compose1 act lp rp in
      add_intermediate p

    let tensor lhs rhs =
      let act = Action.create "TENSOR" lhs "" rhs "" (getstep())
      and lp = get lhs
      and rp = get rhs in
      let (p,_) = Cprocess.compose1 act lp rp in
      add_intermediate p

    let cwith lhs lsel rhs rsel =
      let act = Action.create "WITH" lhs lsel rhs rsel (getstep())
      and lp = get lhs
      and rp = get rhs in
      let (p,_) = Cprocess.compose1 act lp rp in
      add_intermediate p

    let join lhs lsel rhs rsel =
      let act = Action.create "JOIN" lhs lsel rhs rsel (getstep())
      and lp = get lhs
      and rp = get rhs in
      let (p,_) = Cprocess.compose1 act lp rp in
      add_intermediate p

    let components p = (map get o Action.root_deps) p.Cprocess.actions

    let rename_act old name act = 
      if (act.Action.res = old) 
      then ({ act with Action.res = name }:Action.t)
      else act

    let rec all_actions rename p = 
      let icomps = filter (fun p -> p.Cprocess.intermediate) (components p) in
      let acts = flat (map (all_actions None) icomps) in
      match rename with
      | None -> acts @ p.Cprocess.actions
      | Some(name) -> acts @ (map (rename_act p.Cprocess.name name) p.Cprocess.actions)

    let store iname name =
      let p = get iname in
      let acts = all_actions (Some name) p in
      let deps = (map get o Action.root_deps) acts in
      let (result,_,_) = Cprocess.compose name deps acts in
      add_process result
     
    let load name = 
      reset ();
      (ignore o map compose1) (get name).Cprocess.actions
  end;;


 
