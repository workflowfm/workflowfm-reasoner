(* ========================================================================= *)
(* Tools to export pi-calculus terms to PiVizTool, MWB, and other external   *)
(* programs.                                                                 *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                2012 - 2015                                *)
(* ========================================================================= *)

needs ("tools/terms.ml");;
needs (!serv_dir ^ "pap/pi.ml");;
needs (!serv_dir ^ "pap/pap.ml");;
needs (!serv_dir ^ "processes/processes.ml");;

(* TODO: Maybe it's better to not make this a functor since it doesn't work with any Composer. *)
module Piviz_make (Process : Process_type) =
  struct
  (* ------------------------------------------------------------------------- *)
  (* Same as print_pi in pi.ml but returns a string instead. Also incorporates *)
  (* term definitions from parent services in services.ml.                     *)
  (* ------------------------------------------------------------------------- *)
  
  let rec string_of tm =
    if ((fst o dest_type o type_of) tm = "Agent") then
    if tm = `Zero:(num)Agent` then "0" 
    else if (is_var tm) then (fst o dest_var) tm
    else 
    (*    let subn_string (tm1,tm2)= (
	"[" ^ (string_of_term tm1) ^ ">" ^ (string_of_term tm2) ^ "]"
      ) in*)
    let ltm_string ltm =
      let rec terms_string tml =
	(match tml with 
	   | [] -> ""
	   | [h] -> string_of_term h
	   | h::t -> ((string_of_term h) ^ ", " ^ (terms_string t)) ) in
      terms_string (dest_list ltm) in
    let comb,args = strip_comb tm in
    if ( comb = `Out:num->(num)list->(num)Agent->(num)Agent`) then 
    ("'" ^ (string_of_term (hd args)) ^ "<" ^ 
     (ltm_string ((hd o tl) args)) ^ ">."  ^ (string_of (last args)))
    else if ( comb = `In:num->(num)list->(num)Agent->(num)Agent` ) then 
    ((string_of_term (hd args)) ^ "(" ^ 
     (ltm_string ((hd o tl) args)) ^ ")."  ^ (string_of (last args)))
    else if ( comb = `Res:(num)list->(num)Agent->(num)Agent`) then 
    ("(^ " ^ (ltm_string (hd args)) ^ ")(" ^
     (string_of (last args)) ^ ")")
    else if ( comb = `Comp:(num)Agent->(num)Agent->(num)Agent`) then 
    ("(" ^ (string_of (hd args)) ^ " | " ^
     (string_of (last args)) ^ ")")
    else if ( comb = `Plus:(num)Agent->(num)Agent->(num)Agent`) then 
    ("(" ^ (string_of (hd args)) ^ " + " ^
     (string_of (last args)) ^ ")")
    (*	else if ( comb = `SUBN1:(num)Agent->num#num->(num)Agent`) then 
	  ("{" ^ (string_of (hd args)) ^ "}" ^ 
	     (subn_string (dest_pair (last args)))) *)
    else if ( is_const comb ) then 
    ("(" ^ (string_of_term tm) ^ ")") (* Need to rebuild old piviz_call to handle filters here. *)
    else if ( is_var comb ) then 
    ("(" ^ (string_of_term tm) ^ ")")
    else failwith ("nop!" ^ (string_of_term comb) ^ ":" ^ (string_of_type (type_of comb))) 
    else failwith "noop!"
  
  
  (* install_user_printer ("print_pi",(fun x -> print_string (string_of x)));; *)


  (* ------------------------------------------------------------------------- *)
  (* Functions that fix pi-calculus terms to make them appropriate for input   *)
  (* in MWB or PiVizTool.                                                      *)
  (* ------------------------------------------------------------------------- *)
  (* - Replace "t" by a fresh underscored version, because "t" corresponds to  *)
  (*   the tau action in PiVizTool.                                            *)
  (* - *TODO* replace primed variables with underscored ones (ie. a' with a_)  *)
  (*   because the single quote (') indicates an output channel and PiVizTool  *)
  (*   fails to parse in other positions.                                      *)
  (* ------------------------------------------------------------------------- *)
  
  let fix' chans tm = vsubst [mk_undered_var (`t:num`::chans) `t:num`,`t:num`] tm
  
  let fix tm = fix' (frees tm) tm
  

  (* ------------------------------------------------------------------------- *)
  (* Creates the MWB/PiVizTool definition of a defined service.                *)
  (* ------------------------------------------------------------------------- *)
  
  let def: Process.t -> string =
    fun p ->  
	let proc = fix (Process.get_proc_raw p) in
	let lh,rh = lhs proc,rhs proc in
	("agent " ^ (string_of_term lh) ^ " = " ^ (string_of rh))

  
  (* ------------------------------------------------------------------------- *)
  (* Creates a MWB/PiVizTool call to a defined service.                        *)
  (* ------------------------------------------------------------------------- *)
  (* This is trivially used below. It would be nice to have a more general     *)
  (* version where you'd supply the list of arguments.                         *)
  (* ------------------------------------------------------------------------- *)
  
  let call: Process.t -> string =
    fun p ->  (string_of_term o fix o lhs) (Process.get_proc_raw p)
  
  
  (* ------------------------------------------------------------------------- *)
  (* Creates an "interface" for a defined service for PiVizTool.               *)
  (* Based on the the CLL definition of the service, creates a Request agent   *)
  (* that supplies the arguments to the service and a Response agent that      *)
  (* expects the service output in the correct format.                         *)
  (* Finally, it creates the executable Main agent that composes the service   *)
  (* in parallel with Request and Response.                                    *)
  (* ------------------------------------------------------------------------- *)
  
  let interface: Process.t -> string =
    fun p ->
    let composeprocs procs = 
      match procs with
	  [] -> `Zero:(num)Agent`
	| [h] -> h
	| _ -> let mkPiComp x y = list_mk_icomb "Comp" [x;y] in
	       itlist mkPiComp (butlast procs) (last procs) in

    let getargs tm =
      (string_of_term o mk_tuple o dest_list o rhs o concl o Pi_calc.fn_conv o curry mk_comb Pi_calc.fn) tm in
    
    let cll = Process.get_cll p in
    let ins = find_input_terms cll
    and out = find_output_term cll in
    let req = composeprocs (map (linterm_to_pi_inv Cllpi.linprop_to_name) ins)
    and res = linterm_to_pi_inv Cllpi.linprop_to_name out in
    let reqargs = getargs req 
    and resargs = getargs res in

    ("agent Request(" ^ reqargs ^ ") = " 
     ^ string_of req ^ "\n" ^
     "agent Response(" ^ resargs ^ ") = " 
     ^ string_of res ^ "\n\n" ^
     "exec agent Main () = Request(" ^ reqargs ^ 
     ") | Response(" ^ resargs ^ ") | " ^ 
     call p ^ "\n")
 
  
  (* ------------------------------------------------------------------------- *)
  (* Creates a PiVizTool file that allows the full visualisation of a given    *)
  (* defined service.                                                          *)
  (* ------------------------------------------------------------------------- *)
  
  let deploy: Process.t -> Process.t list -> string =
    fun p deps ->
    let print_dep s = def s ^ "\n" in 
    (itlist (^) (map print_dep deps) "\n") ^ 
    def p ^ "\n\n" ^
    interface p ^ "\n\n"

  end;;
  
  
