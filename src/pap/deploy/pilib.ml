(* ========================================================================= *)
(* Tools to construct Scala code from Proofs-as-Processes style pi-calculus  *)
(* terms.                                                                    *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                  2012-2019                                *)
(* ========================================================================= *)

needs (!serv_dir ^ "pap/pap.ml");;
needs (!serv_dir ^ "processes/processes.ml");;
needs (!serv_dir ^ "api/composer.ml");;

(*
Id    : In y [a] (Out x [a] Zero)
Times : Res [x; y] (Out z [x; y] (Comp P Q))
Par   : In z [x; y] P
Plus1 : Res [x] (In z [u; v] (Out u [x] P))
Plus2 : Res [y] (In z [u; v] (Out v [y] P))
With  : Res [u; v] (Out z [u; v] (Plus (In u [x] P) (In v [y] Q)))
Cut   : Res [z] (Comp (SUBN1 P (x,z)) (SUBN1 Q (y,z)))
*)

(*
In    : In X [a] Zero
Out   : Res [a] (Out X [a] Zero)
Times : Res [x_a; x_b] (Out X [x_a; x_b] (Comp P Q))
Par   : In X [x_a; x_b] (Comp P Q)
Plus  : Res [x_x; x_y] (In X [x_u; x_v] (Plus (Out x_u [x_x] P)) (Out x_v [x_y] Q))))
With  : Res [x_u; x_v] (Out X [x_u; x_v] (Plus (In x_u [x_x] P) (In x_v [x_y] Q)))

chan = ( fst o dest_var o rand o rator o rator o rand ) pi
*)

let string_comma_list l =
  let mk_list x y = x ^ " , " ^ y in
    match l with 
	[] -> ""
      | [h] -> h
      | _ -> itlist mk_list (butlast l) (last l);;

let string_fun_ty ins out =
  let mk_ty_list x y = x ^ ", " ^ y in
  let instr = if (ins = []) then "()" else ("(" ^ (itlist mk_ty_list (butlast ins) (last ins)) ^ ")") in
  instr ^ " => " ^ out;;

let string_fun_arglist instypes =
  let inp i t = "arg"^(string_of_int i)^" :"^t in
  if (instypes = []) then "" else
    let l = butlast instypes
    and x = last instypes in
    let rec inputlist i instypes = 
      match instypes with
	  [] -> (inp i x)
	| (h::t) -> (inp i h) ^ ", " ^ (inputlist (i+1) t)
    in inputlist 0 l;;


let string_inputlist instypes =
  let inp i t = "(await(input"^(string_of_int i)^")).asInstanceOf["^((fst o fst o snd) t)^"]" in
  if (instypes = []) then "" else
    let l = butlast instypes
    and x = last instypes in
    let rec inputlist i instypes = 
      match instypes with
	  [] -> (inp i x)
	| (h::t) -> (inp i h) ^ ", " ^ (inputlist (i+1) t)
    in inputlist 0 l;;


(* Initial path must end in separator! *)
let (scala_file_path:string->string->string->string->string),
  (java_file_path:string->string->string->string->string) =
  let file_path separator path package name extension =
    let rec package_to_path path package =
      try (
	let pos = String.index package '.' in
	let left = String.sub package 0 pos
	and right = String.sub package (pos + 1) (String.length package - pos - 1) in
	  package_to_path (path ^ left ^ separator) right
      ) with Not_found -> path ^ package in
      (package_to_path path package) ^ separator ^ name ^ extension in
    (fun separator path package name -> file_path separator path package name ".scala"),
    (fun separator path package name -> file_path separator path package name ".java");;



let rec scala_type cll = try (
  if (is_var cll) then ((String.capitalize o fst o dest_var) cll,"NChan[Any]")
  else if (is_const cll) then ((String.capitalize o fst o dest_const) cll,"NChan[Any]")
  else if (is_comb cll) then (
    let comb,args = strip_comb cll in
    if (comb = `NEG`) then (scala_type o hd) args
    else if (comb = `LinTimes`) then 
      let t1,c1 = (scala_type o hd) args
      and t2,c2 = (scala_type o hd o tl) args 
      in ("("^t1^","^t2^")","PairChan["^c1^","^c2^"]")
    else if (comb = `LinPar`) then
      let t1,c1 = (scala_type o hd) args
      and t2,c2 = (scala_type o hd o tl) args 
      in ("("^t1^","^t2^")","PairChan["^c1^","^c2^"]")
    else if (comb = `LinPlus`) then
      let t1,c1 = (scala_type o hd) args
      and t2,c2 = (scala_type o hd o tl) args 
      in ("Either["^t1^","^t2^"]","OptChan["^c1^","^c2^"]")
    else if (comb = `LinWith`) then
      let t1,c1 = (scala_type o hd) args
      and t2,c2 = (scala_type o hd o tl) args 
      in ("Either["^t1^","^t2^"]","OptChan["^c1^","^c2^"]")
    else fail ()  
  )
  else fail()
) with Failure _ -> failwith ("scala_type: Unrecognised type ["^(string_of_term cll)^"]");;


type pilib_params = (string * string) * string;; (* Type of I/O, type of channel, generated code. *)

let nltab depth =
  let tab = String.make depth '\t' in
    "\n" ^ tab;;

let (PiOutCode: string -> string -> pilib_params) = 
  fun output typ ->
    ((typ,"NChan[Any]"),
     "PiOut(name,"^output^")_"
    );;

let (PiInCode :string -> pilib_params) = 
  fun typ ->
    ((typ,"NChan[Any]"),
     "PiIn[Any](name)_"
    );;

let (PiTimesCode: int -> string -> string -> string -> pilib_params -> pilib_params -> pilib_params) =
  fun depth output chan_x chan_y ((ptyp,pchan),pcode) ((qtyp,qchan),qcode) ->
    (("("^ptyp^","^qtyp^")","PairChan["^pchan^","^qchan^"]"),
     output ^ " match { " ^ (nltab (depth + 1)) ^
       "case (x,y) =>" ^ (nltab (depth + 2)) ^
       "val xout = " ^ pcode ^ (nltab (depth + 2)) ^
       "val yout = " ^ qcode ^ (nltab (depth + 2)) ^
       "PiTimes(name, \""^ chan_x ^"\", \""^ chan_y ^ "\") (xout) (yout) _" ^ (nltab (depth + 1)) ^
       "}"
    );;

let (PiParCode: int -> pilib_params -> pilib_params -> pilib_params) =
  fun depth ((ptyp,pchan),pcode) ((qtyp,qchan),qcode) ->
    (("("^ptyp^","^qtyp^")","PairChan["^pchan^","^qchan^"]"),  
     "{" ^ (nltab (depth + 1)) ^ 
       "val xin = " ^ pcode ^ (nltab (depth + 1)) ^ 
       "val yin = " ^ qcode ^ (nltab (depth + 1)) ^ 
       "PiPar(name) (xin) (yin) _"^ (nltab (depth)) ^ 
       "}"
    );;


let (PiPlusCode: int -> string -> string -> string -> pilib_params -> pilib_params -> pilib_params) =
  fun depth output chan_x chan_y ((ptyp,pchan),pcode) ((qtyp,qchan),qcode) ->
    (("Either["^ptyp^","^qtyp^"]","OptChan["^pchan^","^qchan^"]"),
     "{" ^ (nltab (depth + 1)) ^ 
       "val xout = " ^ output ^ " match {" ^ (nltab (depth + 2)) ^
       "case Left(x) =>" ^ (nltab (depth + 3)) ^
       "val xout = " ^ pcode ^ (nltab (depth + 3)) ^
       "Left(xout)" ^ (nltab (depth + 2)) ^
       "case Right(x) =>" ^ (nltab (depth + 3)) ^ 
       "val xout = " ^ qcode ^ (nltab (depth + 3)) ^
       "Right(xout)" ^ (nltab (depth + 2)) ^
       "}" ^ (nltab (depth + 1)) ^ 
       "PiPlus(name, \"" ^ chan_x ^ "\", \"" ^ chan_y ^ "\") (xout)_" ^ (nltab (depth)) ^
       "}"
    );;

let (PiWithCode: int -> string -> string -> pilib_params -> pilib_params -> pilib_params) =
  fun depth chan_x chan_y ((ptyp,pchan),pcode) ((qtyp,qchan),qcode) ->
    (("Either["^ptyp^","^qtyp^"]","OptChan["^pchan^","^qchan^"]"),  
     "{" ^ (nltab (depth + 1)) ^ 
       "val xin = " ^ pcode ^ (nltab (depth + 1)) ^ 
       "val yin = " ^ qcode ^ (nltab (depth + 1)) ^ 
       "PiWith(name, \""^chan_x^"\", \""^chan_y^"\") (xin) (yin) _"^ (nltab (depth)) ^ 
       "}"
    );;

let rec scala_service_io depth types output pi =
  (*map (fun (x,y) -> (print_string x ; print_string " --> " ; print_string (string_of_term y) ; print_newline())) types ; print_newline(); *)
  let tm x y = try (let _ = term_match [] x y in true) with Failure _ -> false 
  and (PiOut: term -> string -> pilib_params) = 
    fun pi output -> try (
      let piAtom = (fst o dest_var) (follow_path "lrlr" pi) in
      let typ = assoc piAtom types in
	(*let typ = ( String.capitalize o fst o dest_var o rand o rator o rand o rator ) pi in*)
	PiOutCode output ((fst o dest_var) typ)
    ) with Failure s -> failwith ("PiOut: " ^ s ^ " (" ^ (string_of_term(pi)) ^ ")")
  and (PiIn: term -> pilib_params) = 
    fun pi -> try (
      let piAtom = (fst o dest_var) (follow_path "lrlr" pi) in
      let typ = assoc piAtom types in
	(*let typ = ( String.capitalize o fst o dest_var o rand o rator o rand o rator ) pi in*)
	PiInCode ((fst o dest_var) typ)
    ) with Failure s -> failwith ("PiIn: " ^ s ^ " (" ^ (string_of_term(pi)) ^ ")")
  and (PiTimes:term -> string -> pilib_params) =
    fun pi output -> try (
      let chans = ((map (fst o dest_var)) o dest_list o rand o rator ) pi
      and p = ( rand o rator o rand o rand ) pi
      and q = ( rand o rand o rand ) pi
      in
      let p_r = scala_service_io (depth + 2) types "x" p 
      and q_r = scala_service_io (depth + 2) types "y" q 
      in PiTimesCode depth output (hd chans) ((hd o tl) chans) p_r q_r
    ) with Failure s -> failwith ("PiTimes: " ^ s ^ " (" ^ (string_of_term(pi)) ^ ")")
  and (PiPar:term -> pilib_params) =
    fun pi -> try (
      let p = ( rand o rator o rand ) pi
      and q = ( rand o rand ) pi
      in
      let p_r = scala_service_io (depth + 2) types "xin" p
      and q_r = scala_service_io (depth + 2) types "yin" q
      in PiParCode depth p_r q_r
    ) with Failure s -> failwith ("PiPar: " ^ s ^ " (" ^ (string_of_term(pi)) ^ ")")
  and (PiPlus:term -> string -> pilib_params) =
    fun pi output -> try (
      let chans = ((map (fst o dest_var)) o dest_list o rand o rator ) pi
      and p = ( rand o rand o rator o rand o rand ) pi
      and q = ( rand o rand o rand o rand ) pi
      in
      let p_r = scala_service_io (depth + 3) types "x" p 
      and q_r = scala_service_io (depth + 3) types "x" q
      in PiPlusCode depth output (hd chans) ((hd o tl) chans) p_r q_r
    ) with Failure s -> failwith ("PiPLus: " ^ s ^ " (" ^ (string_of_term(pi)) ^ ")")
  and (PiWith:term -> pilib_params) =
    fun pi -> try (
      let chans = ((map (fst o dest_var)) o dest_list o rand o rator ) pi
      and p = ( rand o rand o rator o rand o rand ) pi
      and q = ( rand o rand o rand o rand ) pi
      in
      let p_r = scala_service_io (depth + 3) types "xin" p
      and q_r = scala_service_io (depth + 3) types "yin" q
      in PiWithCode depth (hd chans) ((hd o tl) chans) p_r q_r
    ) with Failure s -> failwith ("PiWith: " ^ s ^ " (" ^ (string_of_term(pi)) ^ ")")
  in    
    if (tm `(Res [a] (Out A [a] Zero)):NAgent` pi) then PiOut pi output 
    else if (tm `(In X [a] Zero):NAgent` pi) then PiIn pi
    else if (tm `(In X [a; b] (Comp P Q)):NAgent` pi) then PiPar pi
    else if (tm `(Res [x; y] (Out A [x; y] (Comp P Q))):NAgent` pi) then PiTimes pi output
    else if (tm `(Res [u; v] (Out X [u; v] (Plus (In u [x] P) (In v [y] Q)))):NAgent` pi) then PiWith pi
    else if (tm `(Res [x; y] (In R [u; v] (Plus (Out u [x] P) (Out v [y] Q)))):NAgent` pi) then PiPlus pi output
    else failwith ("scala_service_io: no matching pattern for `" ^ (string_of_term pi) ^ "`");;

let linterm_to_code depth output cll =
  let term = (rhs o concl o (PURE_REWRITE_CONV[NEG_NEG;NEG_CLAUSES])) cll in
(*  let is_type x = (is_var x) && (type_of x = `:LinProp`) in
  let types = map ((fun x -> (String.lowercase x,x)) o fst o dest_var) (find_terms is_type cll) *)
  let pi,types = linterm_to_pi' Cllpi.linprop_to_name term in
    scala_service_io depth types output pi;;

let scala_atomic_trait depth name typarams chans insparams outparams =
  let rec inputfuns i insparams =
    match insparams with
	[] -> ""
      | (h::t) -> 
	"val inputf"^(string_of_int i)^" = " ^ ((snd o snd) h) ^ (nltab (depth + 2)) ^
	  "val input"^(string_of_int i)^" = future(inputf"^(string_of_int i)^" ("^(fst h)^"))" ^ (nltab (depth + 2)) ^ 
	  (inputfuns (i+1) t) in
    "trait "^(String.capitalize name)^"Trait extends ("^typarams^") {" ^ (nltab (depth + 1)) ^
      "var name = \""^name^"\"" ^ (nltab (depth + 1)) ^
      "def run("^chans^") (implicit system: ActorSystem) = {" ^ (nltab (depth + 2)) ^
      (inputfuns 0 insparams) ^
      "val outputf = " ^ ((snd o snd) outparams) ^ (nltab (depth + 2)) ^
      "outputf ("^(fst outparams)^")" ^ (nltab (depth + 1)) ^
      "}" ^ (nltab depth) ^
      "}\n\n";;



let (PiCutRuleCode: int -> string -> string -> (string * string) -> string -> (string * string) -> string) =
  fun depth chan_z pcode (pchan,ptyp) qcode (qchan,qtyp) ->
    "def _p (__"^pchan^" : NChan[Any]) = {" ^ (nltab (depth + 1)) ^ 
      "val "^pchan^" = __"^pchan^".asInstanceOf["^ptyp^"]" ^ (nltab (depth + 1)) ^ 
      pcode  ^ (nltab (depth)) ^
      "}" ^ (nltab (depth)) ^
      "def _q (__"^qchan^" : NChan[Any]) =  {" ^ (nltab (depth + 1)) ^ 
      "val "^qchan^" = __"^qchan^".asInstanceOf["^qtyp^"]" ^ (nltab (depth + 1)) ^ 
      qcode  ^ (nltab (depth)) ^
      "}" ^ (nltab (depth)) ^ 
      "PiCut(name,\""^chan_z^"\") (_p) (_q) ";;

let (PiParRuleCode: int -> string -> string -> string -> string -> string) =
  fun depth chan_z xchan ychan pcode ->
    "val _"^chan_z^" = "^chan_z^".asInstanceOf[PairChan[NChan[Any],NChan[Any]]]"  ^ (nltab (depth)) ^ 
    "PiParI(name) (_"^chan_z^") match { case ( "^xchan^" , "^ychan^" ) => {" ^ (nltab (depth + 1)) ^ 
      pcode ^ (nltab (depth)) ^ 
      "} }";;

let (PiTimesRuleCode: int -> string -> string -> (string * string) -> string -> (string * string) -> string) =
  fun depth chan_z pcode (pchan,ptyp) qcode (qchan,qtyp) ->
    "def _p (__"^pchan^" : NChan[Any]) = {" ^ (nltab (depth + 1)) ^ 
      "val "^pchan^" = __"^pchan^".asInstanceOf["^ptyp^"]" ^ (nltab (depth + 1)) ^ 
      pcode ^ (nltab (depth)) ^ 
      "}" ^ (nltab (depth)) ^ 
      "def _q (__"^qchan^" : NChan[Any]) = {" ^ (nltab (depth + 1)) ^ 
      "val "^qchan^" = __"^qchan^".asInstanceOf["^qtyp^"]" ^ (nltab (depth + 1)) ^ 
      qcode ^ (nltab (depth)) ^ 
      "}" ^ (nltab (depth)) ^ 
      "val _"^chan_z^" = "^chan_z^".asInstanceOf[PairChan[NChan[Any],NChan[Any]]]"  ^ (nltab (depth)) ^ 
      "PiTimes(name,\""^pchan^"\",\""^qchan^"\") (_p) (_q) (_"^chan_z^")";;

let (PiWithRuleCode: int -> string -> string -> (string * string) -> string -> (string * string) -> string) =
  fun depth chan_z pcode (pchan,ptyp) qcode (qchan,qtyp) ->
  "def _p (__"^pchan^" : NChan[Any]) = {" ^ (nltab (depth + 1)) ^ 
    "val "^pchan^" = __"^pchan^".asInstanceOf["^ptyp^"]" ^ (nltab (depth + 1)) ^ 
      pcode ^ (nltab (depth)) ^ 
        "}" ^ (nltab (depth)) ^ 
          "def _q (__"^qchan^" : NChan[Any]) = {" ^ (nltab (depth + 1)) ^ 
            "val "^qchan^" = __"^qchan^".asInstanceOf["^qtyp^"]" ^ (nltab (depth + 1)) ^ 
              qcode ^ (nltab (depth)) ^ 
                "}" ^ (nltab (depth)) ^ 
                  "val _"^chan_z^" = "^chan_z^".asInstanceOf[OptChan[NChan[Any],NChan[Any]]]"  ^ (nltab (depth)) ^ 
                    "PiWith(name, \"u1\", \"v1\") (_p) (_q) (_"^chan_z^")";;

let (PiPlus1RuleCode: int -> string -> string -> (string * string) -> string) =
  fun depth chan_z code (xchan,xtyp) ->
  "val _"^chan_z^" = "^chan_z^".asInstanceOf[OptChan[NChan[Any],NChan[Any]]]"  ^ (nltab (depth)) ^ 
    "PiPlus1(name, \""^xchan^"\") (_"^chan_z^") ( (__"^xchan^" : NChan[Any]) => {" ^ (nltab (depth + 1)) ^ 
      "val "^xchan^" = __"^xchan^".asInstanceOf["^xtyp^"]" ^ (nltab (depth + 1)) ^ 
        code ^ (nltab (depth)) ^ 
          " }) ";;

let (PiPlus2RuleCode: int -> string -> string -> (string * string) -> string) =
  fun depth chan_z code (ychan,ytyp) ->
  "val _"^chan_z^" = "^chan_z^".asInstanceOf[OptChan[NChan[Any],NChan[Any]]]"  ^ (nltab (depth)) ^  
    "PiPlus2(name, \""^ychan^"\") (_"^chan_z^") ( (__"^ychan^"  : NChan[Any]) => {" ^ (nltab (depth + 1)) ^ 
      "val "^ychan^" = __"^ychan^".asInstanceOf["^ytyp^"]" ^ (nltab (depth + 1)) ^ 
        code ^ (nltab (depth)) ^ 
          " }) ";;


module Pilib_make (Composer : Composer_type) = 
  struct 
    module Proc = Composer.Process

    let scala_atomic_serv depth (proc:Proc.t) ins out =
      let name = proc.Proc.name in
      let get_params c x = (fst o dest_var o rand) x , linterm_to_code 4 c x in
      let in_params = map (get_params "input") ins in
      let out_params = get_params ("(this ("^(string_inputlist in_params)^").asInstanceOf[Any])") out in
      let get_scala_typaram (_,((x,_),_)) = x 
      and get_scala_chan l x = x ^ " : " ^ (snd o fst) (assoc x l) in
      let typarams = string_fun_ty (map get_scala_typaram in_params) (get_scala_typaram out_params) in
      let chanlist = map ((get_scala_chan (out_params :: in_params)) o fst o dest_var) ((dest_tuple o rand o lhs) (Proc.get_proc_raw proc))
      in scala_atomic_trait depth name typarams (string_comma_list chanlist) in_params out_params

    let scala_atomic_service separator path package project (proc:Proc.t) =
      let cll = Proc.get_cll proc
      and name = proc.Proc.name in
      let ins = find_input_terms cll
      and out = find_output_term cll in 
      (scala_file_path separator path (package ^ ".atomictraits") ((String.capitalize name)^"Trait"),
       "package " ^ package ^ ".atomictraits\n\n" ^
         "import akka.actor.ActorSystem\n" ^
           "import uk.ac.ed.pappilib.PapPiLib._\n" ^
             "import " ^ package ^ "." ^  (String.capitalize project) ^ "Types._\n" ^ (nltab 0) ^ 
               (scala_atomic_serv 0 proc ins out))


    let PiComponentCode: Proc.t -> string list -> (string * string) list -> (string * string) list * string =
      fun proc call_chans scala_chans ->
      let def_chans = ((map (fst o dest_var)) o dest_tuple o rand o lhs o Proc.get_proc_raw) proc in
      let chan_map = zip def_chans call_chans in
      let mk_chan_list x y = x ^ " , " ^ y  in
      let get_call_chan c = (assoc c chan_map,assoc c scala_chans) in
      let chans = map (get_call_chan o fst) scala_chans in
      let channames = map fst chans in
      let chanl = itlist mk_chan_list (butlast channames) (last channames) in
      chans , (String.uncapitalize proc.Proc.name) ^ ".run(" ^ chanl ^ ")"


    let rec scala_composition_code: int -> (string * (Proc.t * (string * string) list)) list -> term -> ((string * string) list) * string =
      fun depth available pi ->
      (*  ( print_term pi ; print_newline () ; *)
      let tm x y = try (let _ = term_match [] x y in true) with Failure _ -> false 
      and (PiId:term -> ((string * string) list) * string) =
        fun pi -> try (
                    let a = (fst o dest_var o (follow_path "lrlr")) pi
                    and x = (fst o dest_var o (follow_path "rllr")) pi
                    and y = (fst o dest_var o (follow_path "llr")) pi in
                    (*      let typ = "NChan[" ^ (String.capitalize (String.sub a 0 (String.rindex a '_'))) ^ "]" in *)
                    let typ = "NChan[Any]" in
                    ([(x,typ);(y,typ)],"PiId (name) ("^y^") ("^x^")")
                  ) with Failure s -> failwith ("PiId: " ^ s)
      and (PiCut:term -> ((string * string) list) * string) =
        fun pi -> try (
                    let p = (follow_path "rlrlr") pi
                    and q = (follow_path "rrlr") pi
                    and z = (fst o dest_var o (follow_path "lrlr")) pi
                    and x = (fst o dest_var o (follow_path "rlrrlr")) pi
                    and y = (fst o dest_var o (follow_path "rrrlr")) pi in
                    let (pchans,pcode) = scala_composition_code (depth+1) available p 
                    and (qchans,qcode) = scala_composition_code (depth+1) available q in
                    let ((_,ptyp),pchans') = remove (fun (c,_) -> (c = x)) pchans
                    and ((_,qtyp),qchans') = remove (fun (c,_) -> (c = y)) qchans in
                    let chans = pchans' @ qchans' in
                    chans, PiCutRuleCode depth z pcode (x,ptyp) qcode (y,qtyp)
                  ) with Failure s -> failwith ("PiCut: " ^ s)
      and (PiCut':term -> ((string * string) list) * string) =
        fun pi -> try (
                    let p = (follow_path "rlr") pi
                    and q = (follow_path "rr") pi
                    and z = (fst o dest_var o (follow_path "lrlr")) pi in
                    let (pchans,pcode) = scala_composition_code (depth+1) available p 
                    and (qchans,qcode) = scala_composition_code (depth+1) available q in
                    let ((_,ptyp),pchans') = remove (fun (c,_) -> (c = z)) pchans
                    and ((_,qtyp),qchans') = remove (fun (c,_) -> (c = z)) qchans in
                    let chans = pchans' @ qchans' in
                    (chans, PiCutRuleCode depth z pcode (z,ptyp) qcode (z,qtyp))
                  ) with Failure s -> failwith ("PiCut': " ^ s)  
      and (PiPar:term -> ((string * string) list) * string) =
        fun pi -> try (
                    let p = (follow_path "r") pi
                    and z = (fst o dest_var o (follow_path "llr")) pi 
                    and x = (fst o dest_var o (follow_path "lrlr")) pi 
                    and y = (fst o dest_var o (follow_path "lrrlr")) pi in
                    let (pchans,pcode) = scala_composition_code (depth+2) available p in
                    let ((_,xtyp),pchans') = remove (fun (c,_) -> (c = x)) pchans in
                    let ((_,ytyp),pchans'') = remove (fun (c,_) -> (c = y)) pchans' in
                    let ztyp = "PairChan[NChan[Any],NChan[Any]]" in
                    let chans = (z, ztyp) :: pchans'' in
                    (chans, PiParRuleCode depth z x y pcode)
                  ) with Failure s -> failwith ("PiPar: " ^ s)  
      and (PiTimes:term -> ((string * string) list) * string) =
        fun pi -> try (
                    let p = (follow_path "rrlr") pi
                    and q = (follow_path "rrr") pi
                    and z = (fst o dest_var o (follow_path "rllr")) pi
                    and x = (fst o dest_var o (follow_path "lrlr")) pi
                    and y = (fst o dest_var o (follow_path "lrrlr")) pi in
                    let (pchans,pcode) = scala_composition_code (depth+1) available p 
                    and (qchans,qcode) = scala_composition_code (depth+1) available q in
                    let ((_,ptyp),pchans') = remove (fun (c,_) -> (c = x)) pchans
                    and ((_,qtyp),qchans') = remove (fun (c,_) -> (c = y)) qchans in
                    let ztyp = "PairChan[NChan[Any],NChan[Any]]" in
                    let chans = (z, ztyp) :: (pchans' @ qchans') in 
                    (chans, PiTimesRuleCode depth z pcode (x,ptyp) qcode (y,qtyp))
                  ) with Failure s -> failwith ("PiTimes: " ^ s)
      and (PiWith:term -> ((string * string) list) * string) =
        fun pi -> try (
                    let p = (follow_path "rrlrr") pi
                    and q = (follow_path "rrrr") pi
                    and z = (fst o dest_var o (follow_path "rllr")) pi
                    and x = (fst o dest_var o (follow_path "rrlrlrlr")) pi
                    and y = (fst o dest_var o (follow_path "rrrlrlr")) pi in
                    let (pchans,pcode) = scala_composition_code (depth+1) available p 
                    and (qchans,qcode) = scala_composition_code (depth+1) available q in
                    let ((_,ptyp),pchans') = remove (fun (c,_) -> (c = x)) pchans
                    and ((_,qtyp),qchans') = remove (fun (c,_) -> (c = y)) qchans in
                    let ztyp = "OptChan[NChan[Any],NChan[Any]]" in
                    let chans = (z, ztyp) :: (pchans' @ qchans') in 
                    (chans, PiWithRuleCode depth z pcode (x,ptyp) qcode (y,qtyp)) 
                  ) with Failure s -> failwith ("PiWith: " ^ s)
      and (PiPlus1:term -> ((string * string) list) * string) =
        fun pi -> try (
                    let p = (follow_path "rrr") pi
                    and z = (fst o dest_var o (follow_path "rllr")) pi
                    and x = (fst o dest_var o (follow_path "lrlr")) pi in
                    let (pchans,pcode) = scala_composition_code (depth+1) available p in
                    let ((_,ptyp),pchans') = remove (fun (c,_) -> (c = x)) pchans in
                    let ztyp = "OptChan[NChan[Any],NChan[Any]]" in
                    let chans = (z, ztyp) :: pchans' in 
                    (chans, PiPlus1RuleCode depth z pcode (x,ptyp)) 
                  ) with Failure s -> failwith ("PiPlus1: " ^ s)
      and (PiPlus2:term -> ((string * string) list) * string) =
        fun pi -> try (
                    let q = (follow_path "rrr") pi
                    and z = (fst o dest_var o (follow_path "rllr")) pi
                    and y = (fst o dest_var o (follow_path "lrlr")) pi in
                    let (qchans,qcode) = scala_composition_code (depth+1) available q in
                    let ((_,qtyp),qchans') = remove (fun (c,_) -> (c = y)) qchans in
                    let ztyp = "OptChan[NChan[Any],NChan[Any]]" in
                    let chans = (z, ztyp) :: qchans' in 
                    (chans, PiPlus2RuleCode depth z qcode (y,qtyp)) 
                  ) with Failure s -> failwith ("PiPlus2: " ^ s)
      and (PiComponent: term -> ((string * string) list) * string) =
        fun pi -> try (
                    let name = (fst o dest_var o rator) pi 
                    and call_chans = (map (fst o dest_var) o dest_tuple o rand) pi in
                    let proc,chans = assoc name available in
	                PiComponentCode proc call_chans chans
                  ) with Failure s -> failwith ("PiComponent: " ^ s)
      in    
      if (tm `In y [a] (Out x [a] Zero)` pi) then PiId pi
      else if (tm `(Res [z] (Comp (SUBN1 (P) (x,z)) (SUBN1 (Q) (y,z)))):NAgent` pi) then PiCut pi
      else if (tm `(Res [z] (Comp (P) (Q))):NAgent` pi) then PiCut' pi
      else if (tm `(In z [x; y] P):NAgent` pi) then PiPar pi
      else if (tm `(Res [x; y] (Out z [x; y] (Comp P Q))):NAgent` pi) then PiTimes pi
      else if (tm `(Res [x] (In z [u; v] (Out u [x] P))):NAgent` pi) then PiPlus1 pi
      else if (tm `(Res [y] (In z [u; v] (Out v [y] Q))):NAgent` pi) then PiPlus2 pi
      else if (tm `(Res [u; v] (Out z [u; v] (Plus (In u [x] P) (In v [y] Q)))):NAgent` pi) then PiWith pi
      else if (is_var (rator pi)) then PiComponent pi
      else failwith ("scala_composition_code: no matching pattern for `" ^ (string_of_term pi) ^ "`")

      
    let scala_response_fun depth typaram chan inparams =
      "def response("^chan^") = {" ^ (nltab (depth + 1)) ^
        "val inputf = " ^ ((snd o snd) inparams) ^ (nltab (depth + 1)) ^
          "val input = future(inputf ("^(fst inparams)^"))" ^ (nltab (depth + 1)) ^ 
            "(await(input)).asInstanceOf["^typaram^"]" ^ (nltab depth) ^
              "}"

    let scala_response depth (proc:Proc.t) = 
      let cll = Proc.get_cll proc in 
  let input = invert_ll_term (find_output_term cll) in
  let get_params c x = (fst o dest_var o rand) x , linterm_to_code (depth + 1) c x in
  let in_params = get_params "input" input in
  let get_scala_typaram (_,((x,_),_)) = x 
  and get_scala_chan (x,((_,y),_)) = x ^ " : " ^ y in
  let typaram = get_scala_typaram in_params
  and chan = get_scala_chan in_params
  in scala_response_fun depth typaram chan in_params

let scala_request_fun depth typarams chans outparams =
  (*  let typ = List.fold_right (fun x y -> "Pair["^x^","^y^"]") (butlast typarams) (last typarams) in *)
  (*  let rec mk_intuple i =
    let rec mk_intuple' i k =
      match i with 
	  0 -> "_in" ^ (string_of_int k)
	| _ -> "(_in" ^ (string_of_int (k-i)) ^ " , " ^ (mk_intuple' (i-1) k) ^ ")" 
    in mk_intuple' (i-1) (i-1)
  in *)
  let mk_spawn chans =
    let rec mk_spawn' i chans =
      match chans with
	    [] -> "PiZero"
	  | [c] -> "outputf"^(string_of_int i)^" ("^c^")"
	  | c :: l -> "outputf"^(string_of_int i)^" ("^c^") | " ^ mk_spawn' (i+1) l
    in "Spawn < " ^ (mk_spawn' 0 chans) ^ " >"
  in
  let rec outputfuns i outparams =
    match outparams with
	  [] -> ""
    | (h::t) -> 
	   "val outputf"^(string_of_int i)^" = " ^ ((snd o snd) h) ^ (nltab (depth + 1)) ^
	     (outputfuns (i+1) t) 
  in
  "def request("^chans^") = {" ^ (nltab (depth + 1)) ^
    (outputfuns 0 outparams) ^ (nltab (depth + 1)) ^
      (mk_spawn (map fst outparams)) ^ (nltab depth) ^
        "}"

let scala_request depth (proc:Proc.t) = 
  let cll = Proc.get_cll proc in 
  let outs = map invert_ll_term (find_input_terms cll) in
  let get_params c x = (fst o dest_var o rand) x , linterm_to_code (depth + 2) c x in
  let rec get_outparams i outs =
    match outs with
	  [] -> []
    | h :: t -> (get_params ("(arg"^(string_of_int i)^".asInstanceOf[Any])") h) :: (get_outparams (i+1) t)
  in
  let out_params = get_outparams 0 outs in
  let get_scala_typaram (_,((x,_),_)) = x 
  and get_scala_chan (x,((_,y),_)) = x ^ " : " ^ y in
  let typarams = map get_scala_typaram out_params
  and chans = string_comma_list (map get_scala_chan out_params)
  in scala_request_fun depth typarams chans out_params


let scala_composite_apply_fun depth proc in_params out_param call =
  let mk_chan (c,(_,t)) = "val "^c^" = new "^t^"(\""^c^"\")" ^ (nltab (depth + 1)) 
  and mk_list x y = x ^ " , " ^ y in
  let chanlist l = if (l = []) then "" else itlist mk_list (butlast l) (last l) in
  "override def apply ( " ^ (string_fun_arglist (map (fst o snd) in_params))  ^ " ) :" ^ ((fst o snd) out_param) ^ " = {" ^ (nltab (depth + 1)) ^
    scala_request (depth + 1) proc ^ "\n" ^ (nltab (depth + 1)) ^
      scala_response (depth + 1) proc ^ "\n" ^ (nltab (depth + 1)) ^
        (itlist (^) (map mk_chan in_params) (nltab (depth + 1))) ^
          (mk_chan out_param) ^
            "Spawn < request("^(chanlist (map fst in_params))^") | this.run("^call^") > ;" ^ (nltab (depth + 1)) ^
              "await(future (response("^(fst out_param)^")))" ^ (nltab depth) ^
                "}\n"

(*
let scala_apply_composite name =
  let cll = (get_service_cll o get_service) name in 
  let ins = find_input_terms cll
  and out = find_output_term cll 
  and mk_chan x = (fst o dest_var o rand) x , (snd o scala_type o rand o rator) x 
  and chans = map (fst o dest_var) ((dest_tuple o rand o lhs o snd o strip_forall) (get_service name).proc_def) in
    scala_main_class name (map mk_chan ins) (mk_chan out) (string_comma_list chans);;
 *)


(* typarams = Scala function type *)
(* params = components (class parameters) *)
(* chans = pi-calculus call channel parameters *)
(* code = generated code *)

let scala_composite_class depth (proc:Proc.t) typarams params in_params out_param chans code =
  let name = proc.Proc.name in
  let get_scala_chan l x = x ^ " : " ^ snd (assoc x l) in
  "class "^(String.capitalize name)^" ("^params^") (implicit system: ActorSystem) extends (" ^ typarams ^ ") {" ^ (nltab (depth + 1)) ^
    "var name = \""^name^"\"" ^ (nltab (depth + 1)) ^
      "def run("^(string_comma_list (map (get_scala_chan (out_param :: in_params)) chans))^") = {" ^ (nltab (depth + 2)) ^
        code ^ (nltab (depth + 1)) ^
          "}\n" ^ (nltab (depth + 1)) ^ 
            scala_composite_apply_fun (depth + 1) proc in_params out_param (string_comma_list chans) ^ (nltab depth) ^
              "}\n\n"

let scala_composite_service separator path package project proc deplist =
  let depth = 0 in
  let cll = Proc.get_cll proc in 
  let ins = find_input_terms cll
  and out = find_output_term cll in
  let get_params x = (fst o dest_var o rand) x , (scala_type o rand o rator) x in
  let in_params = map get_params ins in
  let out_params = get_params out in
  let typarams = string_fun_ty (map (fst o snd) in_params) ((fst o snd) out_params) in
  let procdef = Proc.get_proc_raw proc in
  let chanlist = map (fst o dest_var) ((dest_tuple o rand o lhs) procdef) in

  let pi = rhs procdef 
  and mk_dep (x:Proc.t) =
    let name = x.Proc.name in String.uncapitalize(name) ^ " : " ^ String.capitalize(name) ^ "Trait" in
  
  let get_chancll p = map ((fun l -> (fst o dest_var o hd o tl) l,hd l) o snd o strip_comb) ((get_ll_terms o Proc.get_cll) p) in

  let mk_avl_chan (ch,cll) = ch,(snd o scala_type) cll in
  (*  and mk_chan clls ch = ch ^ " : " ^ ((snd o scala_type) (assoc ch clls)) in*)
  let mk_avl p = p.Proc.name , (p , map mk_avl_chan (get_chancll p)) in

  let deps_decl = map mk_dep deplist 
  (*  and chans = map (mk_chan (get_chancll name)) (get_chanlist name) *)
  and avls = map mk_avl deplist in
  let _,code = scala_composition_code (depth + 2) avls pi in
  (scala_file_path separator path (package ^ ".compositions") (String.capitalize proc.Proc.name),
   "package " ^ package ^ ".compositions\n\n" ^
     "import akka.actor.ActorSystem\n" ^
       "import uk.ac.ed.pappilib.PapPiLib._\n" ^
         "import " ^ package ^ "." ^ (String.capitalize project) ^ "Types._" ^ (nltab 0) ^ 
           "import " ^ package ^ ".atomictraits._\n" ^ (nltab 0) ^ 
             scala_composite_class depth proc typarams (string_comma_list deps_decl) in_params out_params chanlist code);;


let scala_atomic_instance_class depth name intypes outtype =
  "class "^(String.capitalize name)^" extends "^(String.capitalize name)^"Trait {" ^ (nltab (depth + 1)) ^
    "override def apply( "^ (string_fun_arglist intypes) ^" ) :"^outtype^" = {" ^ (nltab (depth + 2)) ^
      "// TODO: Instantiate this method." ^ (nltab (depth + 1)) ^
        "}" ^ (nltab (depth)) ^
          "}\n"

let scala_atomic_instance separator path package project proc =
  let cll = Proc.get_cll proc in 
  let ins = find_inputs cll
  and out = find_output cll in
  (scala_file_path separator path (package ^ ".instances") (String.capitalize proc.Proc.name),
   "package " ^ package ^ ".instances\n\n" ^
     (*      "import scala.concurrent.pilib._\n" ^
      "import uk.ac.ed.pappilib.PapPiLib._\n" ^*)
     "import " ^ package ^ "." ^  (String.capitalize project) ^ "Types._\n" ^ 
       "import " ^ package ^ ".atomictraits._\n" ^ (nltab 0) ^ 
         scala_atomic_instance_class 0 proc.Proc.name (map (fst o scala_type) ins) ((fst o scala_type) out))



let scala_types_object separator path package project procs =
  let get_props x = (map (fst o dest_var)) (find_terms is_var x) in
  let types p = (setify o flat o (map get_props) o get_ll_props o Proc.get_cll) p in
  let all_types = (setify o flat o (map types)) procs in
  (*(map types (name :: (Service.get_all_parents name))) in*)
  let scala_typedec t = "type " ^ (String.capitalize t) ^ " = String" ^ (nltab 1) in
  (scala_file_path separator path package ((String.capitalize project) ^ "Types"),
   "package " ^ package ^ "\n\n" ^
     "package object " ^ (String.capitalize project) ^ "Types\n" ^
       "{" ^ (nltab 1) ^
         "// TODO: Instantiate the following types:" ^ (nltab 1) ^
           (itlist (^) (map scala_typedec all_types) "\n") ^
             "}")

let scala_main separator path package project proc deps =
  let is_atomic x = x.Proc.actions == [] in
  let atomic,composite =  partition is_atomic deps in
  (*  and depmap = map (fun x -> x.Proc.name,x) deps in *)
  
  let scala_atomic_inst p = "val "^(String.uncapitalize p.Proc.name)^" = new " ^(String.capitalize p.Proc.name)^ (nltab 2)
  and scala_composite_inst p =
    let ldeps = map String.uncapitalize (Proc.get_dep_strings p) in
    "val "^(String.uncapitalize p.Proc.name)^" = new " ^(String.capitalize p.Proc.name)^"("^(string_comma_list ldeps)^")" ^ (nltab 2)
  in
  let params = map (String.uncapitalize o fst o scala_type o rand o rator o invert_ll_term) ((find_input_terms o Proc.get_cll) proc) in
  (scala_file_path separator path package ((String.capitalize proc.Proc.name)^"Main"),
   "package " ^ package ^ "\n\n" ^
     "import akka.actor.ActorSystem\n" ^ 
       "import " ^ package ^ "." ^  (String.capitalize project) ^ "Types._\n" ^ 
         "import " ^ package ^ ".compositions._\n" ^ 
           "import " ^ package ^ ".instances._\n" ^ (nltab 0) ^ 
             "object "^(String.capitalize proc.Proc.name)^"Main {" ^ (nltab 1) ^
               "def main(args: Array[String]): Unit = {" ^ (nltab 2) ^
                 "implicit val system = ActorSystem(\""^(String.capitalize proc.Proc.name)^"\")\n" ^ (nltab 2) ^
                   (itlist (^) (map scala_atomic_inst atomic) (nltab 2)) ^
                     (itlist (^) (map scala_composite_inst composite) (nltab 2)) ^
                       (scala_composite_inst proc) ^ (nltab 2) ^
                         "// TODO: Provide actual parameters:" ^ (nltab 2) ^
                           "val result = "^(String.uncapitalize proc.Proc.name)^"( "^(string_comma_list params)^" )" ^ (nltab 2) ^
                             "system.shutdown()" ^ (nltab 1) ^
                               "}" ^ (nltab 0) ^
                                 "}")

  
(* TODO : runner, complete deploy *)

let java_runner separator path package project name =
  (java_file_path separator path package ((String.capitalize name)^"Runner"),
   "package " ^ package ^ ";\n\n" ^
     "public class " ^ (String.capitalize name) ^ "Runner {" ^ (nltab 1) ^
       "public static void main(String[] args) {" ^ (nltab 2) ^
         (String.capitalize name)^"Main.main(args);" ^ (nltab 1) ^
           "}" ^ (nltab 0) ^
             "}")

let scala_deploy separator path package project main java proc deps =
  let is_atomic x = x.Proc.actions == [] in
  let atomic,composite =  partition is_atomic deps
  and depmap = map (fun x -> x.Proc.name,x) deps in
  let atomictraits = map (scala_atomic_service separator path package project) atomic
  and compositeclasses = map (fun p -> scala_composite_service separator path package project p (Proc.get_deps depmap p)) composite
  and compositeclass = [scala_composite_service separator path package project proc (Proc.get_deps depmap proc)]
  and javarunner = if (java && main) then [java_runner separator path package project proc.Proc.name] else []
  and atomicinstances = map (scala_atomic_instance separator path package project) atomic
  and typesobject = [scala_types_object separator path package project (proc :: deps)]
  and mainclass = if (main) then [scala_main separator path package project proc deps] else []
  in
  (atomictraits @ compositeclasses @ compositeclass @ javarunner ,
   atomicinstances @ typesobject @ mainclass)

(* (overwrite,optional) *)


let scala_deploy_print separator path package project main java proc deps =
  let overwrite,optional = scala_deploy separator path package project main java proc deps
  and print_file (addr,content) = print_string ("[" ^ addr ^ "]\n" ^ content ^ "\n\n") in
  print_string "--- OVERWRITE ---\n\n" ;
  map print_file overwrite ;
  print_string "--- OPTIONAL ---\n\n" ;
  map print_file optional 

(*
scala_deploy_print "/" "/home/kane/PapPiLib/" "uk.ac.ed.skiexample" "SkiExample" "Ski" true true;;
 *)

let deploy separator path package project main java proc deps =
  let ovr,opt = scala_deploy separator path package project main java proc deps in
  let mk_res over (path,content) = (path,content,over) in
  Composer.Response.Deploy ("PiLib", map (mk_res true) ovr @ map (mk_res false) opt)
  end ;;
