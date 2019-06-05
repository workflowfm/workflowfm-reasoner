(* ========================================================================= 
   An environment to use the Composer at the toplevel.
   
   Petros Papapanagiotou
   Center of Intelligent Systems and their Applications         
   School of Informatics, University of Edinburgh                         
   2019
 ========================================================================= *)

needs (!serv_dir ^ "api/api.ml");;

module Composer_console_make (Composer : Composer_type) =
  struct
    module Proc = Composer.Process

    let processes = Hashtbl.create 50

    let add_process (p:Proc.t) = Hashtbl.add processes p.Proc.name p ; p
    let get_process (s:string) = Hashtbl.find processes s
    let exists_process (s:string) = Hashtbl.mem processes s
    let del_process (s:string) = Hashtbl.remove processes s
    let reset_processes () = Hashtbl.reset processes
    let list () = List.of_seq (Hashtbl.to_seq_keys processes)

    let intermediates = Hashtbl.create 50

    let add_intermediate (p:Proc.t) = Hashtbl.add intermediates p.Proc.name p ; p
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
      let p = Proc.create name ins out in
      add_process p ; p

    let compose1 act =
      let lp = get act.Action.larg
      and rp = get act.Action.rarg in
      let (p,_) = Proc.compose1 act lp rp in
      add_intermediate p

    let tensor lhs rhs =
      let act = Action.create "TENSOR" lhs "" rhs "" (getstep())
      and lp = get lhs
      and rp = get rhs in
      let (p,_) = Proc.compose1 act lp rp in
      add_intermediate p

    let cwith lhs lsel rhs rsel =
      let act = Action.create "WITH" lhs lsel rhs rsel (getstep())
      and lp = get lhs
      and rp = get rhs in
      let (p,_) = Proc.compose1 act lp rp in
      add_intermediate p

    let join lhs lsel rhs rsel =
      let act = Action.create "JOIN" lhs lsel rhs rsel (getstep())
      and lp = get lhs
      and rp = get rhs in
      let (p,_) = Proc.compose1 act lp rp in
      add_intermediate p

    let components p = (map get o Action.root_deps) p.Proc.actions

    let rename_act old name act = 
      if (act.Action.res = old) 
      then ({ act with Action.res = name }:Action.t)
      else act

    let rec all_actions rename p = 
      let icomps = filter (fun p -> p.Proc.intermediate) (components p) in
      let acts = flat (map (all_actions None) icomps) in
      match rename with
      | None -> acts @ p.Proc.actions
      | Some(name) -> acts @ (map (rename_act p.Proc.name name) p.Proc.actions)

    let store iname name =
      let p = get iname in
      let acts = all_actions (Some name) p in
      let deps = (map get o Action.root_deps) acts in
      let (result,_,_) = Proc.compose name deps acts in
      add_process result
     
    let load name = 
      reset ();
      (ignore o map compose1) (get name).Proc.actions
  end;;


 
