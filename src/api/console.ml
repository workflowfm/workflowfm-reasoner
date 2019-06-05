(* ========================================================================= 
   An environment to use the Composer at the toplevel.
   
   Petros Papapanagiotou
   Center of Intelligent Systems and their Applications         
   School of Informatics, University of Edinburgh                         
   2019
 ========================================================================= *)

needs (!serv_dir ^ "api/api.ml");;

(* TODO TODO *)
module Composer_console_make (module Composer : Composer_type) =
  struct
    type t = { name : string; phone : string }
           
  end;;


let current_state = ref (Actionstate.create 0);;

let reset_state () = current_state := Actionstate.create 0;;


let state_stack = ref ([]:Actionstate.t list);;

let reset_state_stack () = state_stack := [];;

let push_state x = 
  let l = !state_stack in
    state_stack := x :: l;;

let pop_state () = 
  let l = !state_stack in
    if length l = 0 then failwith "pop_state: Can't back up any more" else
      state_stack := tl l;
    hd l;;


let set_state (s:Actionstate.t) =
  push_state (!current_state);
  current_state := s;
  s;;


let processes = Hashtbl.create 50;;

let add_process (p:Proc.t) = Hashtbl.add processes p.Proc.name p ; p;;

let get_process (s:string) = Hashtbl.find processes s;;

let exists_process (s:string) = Hashtbl.mem processes s;;

let del_process (s:string) = Hashtbl.remove processes s;;

let reset_processes () = Hashtbl.reset processes;;


let intermediates = Hashtbl.create 50;;

let add_intermediate (p:Proc.t) = Hashtbl.add intermediates p.Proc.name p ; p;;

let get_intermediate (s:string) = Hashtbl.find intermediates s;;

let exists_intermediate (s:string) = Hashtbl.mem intermediates s;;

let del_intermediate (s:string) = Hashtbl.remove intermediates s;;

let reset_intermediatees () = Hashtbl.reset intermediates;;


let stepctr = ref 0;;

let incstep () =
  let count = !stepctr in
  (stepctr := count + 1;
   count);;

let resetstep () = stepctr := 0;;

let getstep () =
  "_Step" ^ (string_of_int (incstep()));;


let create name ins out =
  if (exists_process name) then warn true ("Process " ^ name ^ " already exists.") ;
  let p = Proc.create name ins out in
  add_process p ; p;;


let compose1 action lhs lsel rhs rsel =
  let act = Action.create action lhs lsel rhs rsel (getstep()) in
  let (p,s) = Proc.compose1 act (!current_state) (get_process lhs) (get_process rhs) in
  ignore(set_state s);
  add_intermediate p;;
  
