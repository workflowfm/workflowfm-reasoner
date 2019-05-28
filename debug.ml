 xcll = Proc.get_cll mypa;;
 let xname = mypa.Proc.name;;
 let xins = find_input_terms xcll
 and xout = find_output_term xcll;; 

 let xterm = (rhs o concl o (PURE_REWRITE_CONV[NEG_NEG;NEG_CLAUSES])) xcll;;
 let xis_type x = (is_var x) && (type_of x = `:LinProp`);;
 let xtypes = map ((fun x -> (String.lowercase x,x)) o fst o dest_var) (find_terms xis_type xcll);;
 in ((scala_service_io depth types output) o (linterm_to_pi Cllpi.linprop_to_name)) term;;

 let xtm = `(NEG A <> cPa_A_1:num)` ;;
             let myf tm =
               let chan = rand tm in
               linprop_to_pi Cllpi.linprop_to_name (string_of_term chan ^ "_") chan `C:LinProp` ;;

                                                                                         myf xtm;;
 
 BufferBug
   Optionals: A ++ B --> A ++ C ++ D
                                     A ++ B ++ C --> A ++ B
                                                            A --> A ++ B
	                                                                     A ++ B --> A ++ C
	                                                                                       Ctrl - S
	                                                                                                notes
	                                                                                                "Create copy node" + different icon
	                                                                                                                       "Create join node" + different icon
	                                                                                                                                              Several create process windows
	                                                                                                                                              Load compositions into existing workspace

 
let explode_char s =
  let rec exap n l =
      if n < 0 then l else
      exap (n - 1) ((String.get s n)::l) in
  exap (String.length s - 1) [];;

let ascii_str s =
  (String.concat "_" o map (string_of_int o Char.code) o explode_char) s ;;

  let rec linprop_to_name tm =
    try
      if (tm = `LinOne`) then "1"
      else if (tm = `LinZero`) then "0"
      else if (tm = `Top`) then "T"
      else if (tm = `Bottom`) then "_I_"
      else
	let comb,args = strip_comb tm in
	if (is_var comb) then 
	  (ascii_str o string_of_term) comb
	else if (comb = `NEG`) then
	  linprop_to_name (hd args)
	else if (comb = `LinTimes`) then
	  "l_" ^ (linprop_to_name (hd args)) ^ "_X_" ^ (linprop_to_name ((hd o tl) args)) ^ "_r"
	else if (comb = `LinPar`) then
	  "l_" ^ (linprop_to_name (hd args)) ^ "_R_" ^ (linprop_to_name ((hd o tl) args)) ^ "_r"
	else if (comb = `LinPlus`) then
	  "l_" ^ (linprop_to_name (hd args)) ^ "_P_" ^ (linprop_to_name ((hd o tl) args)) ^ "_r"
	else if (comb = `LinWith`) then
	  "l_" ^ (linprop_to_name (hd args)) ^ "_W_" ^ (linprop_to_name ((hd o tl) args)) ^ "_r"
	else failwith ""
    with Failure s -> failwith ("linprop_to_name (" ^ string_of_term(tm) ^ ") :" ^ s);;


 let linprop_to_chan linprop_to_name prefix postfix tm =
    if (String.length prefix = 0)
    then mk_var ((linprop_to_name tm)^"_"^postfix,Pi_calc.chantp)
    else mk_var (prefix^"_"^(linprop_to_name tm)^"_"^postfix,Pi_calc.chantp);;		       

  let linprops_to_chans linprop_to_name prefix tms =
    let mk_chan (n,i) = linprop_to_chan linprop_to_name prefix (string_of_int i) n in
    map mk_chan (zip tms (1--(length tms)));;

  let cll_to_proc linprop_to_name = Pi_calc.cll_to_proc linprop_to_name;;
    
 let pr_cr linprop_to_name name ins out =
    let ins = map (try_type `:LinProp`) ins
    and out = try_type `:LinProp` out in
    let incs = linprops_to_chans linprop_to_name ("c"^name) ins
    and outc = linprop_to_chan linprop_to_name ("o"^name) "" out in
    let inpairs = zip ins incs in
    let proc = cll_to_proc linprop_to_name (Cllpi.mk_cll_def_raw name inpairs (out,outc)) in
    proc;;

  
linprops_to_chans (ascii_str o string_of_term) "c" [`A ** B`;`C ++ D`];;
pr_cr (ascii_str o string_of_term) "P" [`A`;`B ++ C`] `D` ;;
pr_cr (ascii_str o string_of_term) "P" [`A ** B`;`C ++ D`] `E ** (F ++ G)` ;;

pr_cr (linprop_to_name) "P" [`A`;`B ++ C`] `D` ;;
pr_cr (linprop_to_name) "P" [`A ** B`;`C ++ D`] `E ** (F ++ G)` ;;

  
open Json_type.Browse;;
let xtbl = make_table (objekt xx);;

let xprov = list Cll_json.to_prov_entry (field xtbl "prov");;

let xact = Cll_json.to_action (field xtbl "action");;

let xfld = field xtbl "rhs";;
let xlhs = Json_comp.to_process (field xtbl "lhs");;
let xrhs = Json_comp.to_process (field xtbl "rhs");;
let xstate = Json_comp.to_actionstate (field xtbl "state");;
    (act,lhs,rhs,state);;
    let p,s = Process.compose1 act state lhs rhs in
    [composition_result act p s];;


let xxtbl = make_table (objekt xfld);;
let xxname = string (field xxtbl "name");;
let xxinputs = list Json_comp.to_iopair (field xxtbl "inputs");;
let xxoutput = Json_comp.to_iopair (field xxtbl "output");;
let xxproc = Json_comp.to_agent (field xxtbl "proc");;
let xxactions = list Json_comp.to_action (field xxtbl "actions");;
    and copier = bool (field tbl "copier")
    and intermediate = bool (field tbl "intermediate") in
    ({Process.name = name; 
      Process.inputs = inputs ;
      Process.output = output ;
      Process.proc = proc ;
      Process.actions = actions ;
      Process.copier = copier ;
      Process.intermediate = intermediate ;
     }:Process.t);;

(* Compose *)
let xtbl = make_table (objekt xx);;
let xname = string (field xtbl "name");;
let xdeps = list Json_comp.to_process (field xtbl "components");;
let xacts = list Json_comp.to_action (field xtbl "actions");;
let xstate = Json_comp.to_actionstate (field xtbl "state");;

let xp,xinters,xs = Proc.compose xstate xname xdeps xacts;;
      let comp_res (a,(s,p)) = composition_result a p s in
      map comp_res (zip acts inters)
      (* let res = (composition_result (last acts) p s) :: (map comp_res (zip acts inters)) in
      rev res (* This sends 2 results for the last action, but that's ok. *) *)

(* Json_composer.to_agent *)
	  
 let xto_agent j = try (
    let op,arg = (dest_comb o parse_term) j in
    let tm = mk_icomb (op,Proc.try_proc_type arg) in
    let tinst = (map (fun x -> Proc.chantp,x) o filter is_vartype o map type_of o frees) tm in
    inst tinst tm
  ) with Failure _ -> failwith "Json_composer.to_agent: failed to parse agent definition" ;; (* TODO: Is that good enough? *)
		   
 xto_agent "P3 (cP3_Z_1,oP3_R_) = Comp (In cP3_Z_1 [cP3_Z_1__a_Z] Zero) (Res [oP3_R___a_R] (Out oP3_R_ [oP3_R___a_R] Zero))";;
 xto_agent "Co (cP1_X_1,oP2_Z_) = CutProc Y z8 cP2_Y_1 y8 (P2 (cP2_Y_1,oP2_Z_)) (P1 (cP1_X_1,y8))";;
(map (fun x -> Proc.chantp,x) o  filter is_vartype o map type_of o frees o parse_term) "Co (cP1_X_1,oP2_Z_) = CutProc Y z8 cP2_Y_1 y8 (P2 (cP2_Y_1,oP2_Z_)) (P1 (cP1_X_1,y8))";;

let xx = Json_io.json_of_string "{\"name\":\"Co2\",\"actions\":[{\"act\":\"JOIN\",\"larg\":\"Co\",\"lsel\":\"\",\"rarg\":\"P3\",\"rsel\":\"(NEG Z)\",\"res\":\"Co2\"}],\"components\":[{\"name\":\"Co\",\"inputs\":[{\"channel\":\"cP1_X_1\",\"cll\":{\"type\":\"var\",\"name\":\"X\",\"args\":[]}}],\"output\":{\"channel\":\"oP2_Z_\",\"cll\":{\"type\":\"var\",\"name\":\"Z\",\"args\":[]}},\"proc\":\"Co (cP1_X_1,oP2_Z_) \\u003d\\nCutProc Y z8 cP2_Y_1 y8 (P2 (cP2_Y_1,oP2_Z_)) (P1 (cP1_X_1,y8))\",\"actions\":[{\"act\":\"JOIN\",\"larg\":\"P1\",\"lsel\":\"\",\"rarg\":\"P2\",\"rsel\":\"(NEG Y)\",\"res\":\"Co\"}],\"copier\":false,\"intermediate\":false,\"checked\":true,\"valid\":true},{\"name\":\"P3\",\"inputs\":[{\"channel\":\"cP3_Z_1\",\"cll\":{\"type\":\"var\",\"name\":\"Z\",\"args\":[]}}],\"output\":{\"channel\":\"oP3_R_\",\"cll\":{\"type\":\"var\",\"name\":\"R\",\"args\":[]}},\"proc\":\"P3 (cP3_Z_1,oP3_R_) \\u003d\\nComp (In cP3_Z_1 [cP3_Z_1__a_Z] Zero)\\n(Res [oP3_R___a_R] (Out oP3_R_ [oP3_R___a_R] Zero))\",\"actions\":[],\"copier\":false,\"intermediate\":false,\"checked\":true,\"valid\":true}],\"state\":{\"ctr\":8,\"buffered\":[],\"joined\":[]},\"command\":\"compose\",\"executed\":false}";;

let xx = Json_io.json_of_string "{\"action\":{\"act\":\"JOIN\",\"larg\":\"Zzz\",\"lsel\":\"\",\"rarg\":\"P\",\"rsel\":\"A\",\"res\":\"[Step3]\"},\"lhs\":{\"name\":\"Zzz\",\"inputs\":[{\"channel\":\"cZzz_A_1\",\"cll\":{\"type\":\"var\",\"name\":\"A\",\"args\":[]}}],\"output\":{\"channel\":\"oZzz_lB_B_x_C_rB_\",\"cll\":{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"var\",\"name\":\"B\",\"args\":[]},{\"type\":\"var\",\"name\":\"C\",\"args\":[]}]}},\"proc\":\"Zzz (cZzz_A_1,oZzz_lB_B_x_C_rB_) \\u003d\\nComp (In cZzz_A_1 [cZzz_A_1__a_A] Zero)\\n(Res [oZzz_lB_B_x_C_rB__B; oZzz_lB_B_x_C_rB__C]\\n(Out oZzz_lB_B_x_C_rB_ [oZzz_lB_B_x_C_rB__B; oZzz_lB_B_x_C_rB__C]\\n(Comp\\n (Res [oZzz_lB_B_x_C_rB___a_B]\\n (Out oZzz_lB_B_x_C_rB__B [oZzz_lB_B_x_C_rB___a_B] Zero))\\n(Res [oZzz_lB_B_x_C_rB___a_C]\\n(Out oZzz_lB_B_x_C_rB__C [oZzz_lB_B_x_C_rB___a_C] Zero)))))\",\"actions\":[],\"copier\":false,\"intermediate\":false,\"checked\":true,\"valid\":true},\"rhs\":{\"name\":\"P\",\"inputs\":[{\"channel\":\"c2\",\"cll\":{\"type\":\"var\",\"name\":\"X\",\"args\":[]}}],\"output\":{\"channel\":\"c3\",\"cll\":{\"type\":\"var\",\"name\":\"Y\",\"args\":[]}},\"proc\":\"\",\"actions\":[],\"copier\":false,\"intermediate\":true,\"checked\":true,\"valid\":false},\"state\":{\"ctr\":0,\"buffered\":[],\"joined\":[]},\"command\":\"compose1\",\"executed\":false}";;

let xx = Json_io.json_of_string "{\"action\":{\"act\":\"JOIN\",\"larg\":\"_Step13\",\"lsel\":\"rlr\",\"rarg\":\"P1\",\"rsel\":\"(NEG B) \\u003c\\u003e cP1_B_1\",\"res\":\"_Step14\"},\"lhs\":{\"name\":\"_Step13\",\"inputs\":[{\"channel\":\"cL5_x_X_1\",\"cll\":{\"type\":\"var\",\"name\":\"X\",\"args\":[]}}],\"output\":{\"channel\":\"y79\",\"cll\":{\"type\":\"plus\",\"name\":\"\",\"args\":[{\"type\":\"var\",\"name\":\"Y\",\"args\":[]},{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"var\",\"name\":\"B\",\"args\":[]},{\"type\":\"var\",\"name\":\"G\",\"args\":[]}]}]}},\"proc\":\"_Step13 (cL5_x_X_1,y79) \\u003d\\nCutProc (A ++ (B ** G)) z84 x79 y84\\n(WithProc (NEG A) (NEG (B ** G)) x79 b76 c79 u79 v79\\n (PlusLProc Y (B ** G) y79 oR5_x_Y_ up79 vp79\\n (CutProc (B ++ A) z76 cR5_x_lB_B_Plus_A_rB_1 cR5_x_lB_B_Plus_A_rB_1\\n  (R5_x (cR5_x_lB_B_Plus_A_rB_1,oR5_x_Y_))\\n (PlusRProc B A cR5_x_lB_B_Plus_A_rB_1 y77 u77 v77 (IdProc A b76 y77 m78))))\\n(PlusRProc Y (B ** G) y79 d79 uq79 vq79\\n(ParProc (NEG B) (NEG G) c79 x80 y80\\n(TimesProc B G d79 x81 y81 (IdProc B x80 x81 m82) (IdProc G y80 y81 m83)))))\\n(L5_x (cL5_x_X_1,y84))\",\"actions\":[{\"act\":\"JOIN\",\"larg\":\"L5_x\",\"lsel\":\"lr\",\"rarg\":\"R5_x\",\"rsel\":\"(NEG (B ++ A)) \\u003c\\u003e cR5_x_lB_B_Plus_A_rB_1\",\"res\":\"_Step13\"}],\"copier\":false,\"intermediate\":true,\"checked\":true,\"valid\":true},\"rhs\":{\"name\":\"P1\",\"inputs\":[{\"channel\":\"cP1_B_1\",\"cll\":{\"type\":\"var\",\"name\":\"B\",\"args\":[]}},{\"channel\":\"cP1_G_2\",\"cll\":{\"type\":\"var\",\"name\":\"G\",\"args\":[]}}],\"output\":{\"channel\":\"oP1_R_\",\"cll\":{\"type\":\"var\",\"name\":\"R\",\"args\":[]}},\"proc\":\"P1 (cP1_B_1,cP1_G_2,oP1_R_) \\u003d\\nComp (In cP1_B_1 [cP1_B_1__a_B] Zero)\\n(Comp (In cP1_G_2 [cP1_G_2__a_G] Zero)\\n(Res [oP1_R___a_R] (Out oP1_R_ [oP1_R___a_R] Zero)))\",\"actions\":[],\"copier\":false,\"intermediate\":false,\"checked\":true,\"valid\":true},\"state\":{\"ctr\":84,\"buffered\":[],\"joined\":[],\"iprov\":[],\"prov\":[{\"name\":\"_Step13\",\"prov\":{\"type\":\"plus\",\"name\":\"\",\"args\":[{\"type\":\"source\",\"name\":\"R5_x\",\"args\":[]},{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"source\",\"name\":\"L5_x\",\"args\":[]},{\"type\":\"source\",\"name\":\"L5_x\",\"args\":[]}]}]}},{\"name\":\"P1\",\"prov\":{\"type\":\"source\",\"name\":\"P1\",\"args\":[]}}]},\"command\":\"compose1\",\"succeeded\":false}";;


(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

let myst = Actionstate.create "TEST" 0;;
let rec add_provs procs st =
    match procs with
      | [] -> st
      | p :: t ->
	let n,prov = Proc.get_atomic_prov p in
	add_provs t (Actionstate.add_prov n prov st);;
let mycomp lbl procs acts =
  let p,_,s = Proc.compose (add_provs procs myst) lbl procs acts in p,s;;

(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)
Process.get_proc_raw mypa;;

let piki proc =
  let cll = Proc.get_cll proc
  and name = proc.Proc.name in
  let ins = find_input_terms cll
  and out = find_output_term cll in
  
  let get_param cll =
    let term = (rhs o concl o (PURE_REWRITE_CONV[NEG_NEG;NEG_CLAUSES])) cll in
    linterm_to_pi' Cllpi.linprop_to_name term in
  let in_params = map get_param ins in
  let out_params = get_param out in
  in_params,out_params;;

let mypa = Proc.create "Pa" [`X`] `A` ;;
let mypb = Proc.create "Pb" [`A`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "" "Pb" "(NEG A)" "R1";;
mycomp "R1" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `A ** B` ;;
let mypb = Proc.create "Pb" [`A`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "(NEG A)" "R1";;
mycomp "R1" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `A ** B ** C` ;;
let mypb = Proc.create "Pb" [`A`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "(NEG A)" "R1";;
mycomp "R1" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `A ** B ** C` ;;
let mypb = Proc.create "Pb" [`A`] `D` ;;
let mypc = Proc.create "Pc" [`B`] `E` ;;
let mypd = Proc.create "Pd" [`C`] `F` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "(NEG A)" "R1";;
let myact2 = Action.create "JOIN" "R1" "lrr" "Pc" "(NEG B)" "R2";;
let myact3 = Action.create "JOIN" "R2" "r" "Pd" "(NEG C)" "Res";;
mycomp "R1" [mypa;mypb;mypc;mypd] [myact1];;
mycomp "R2" [mypa;mypb;mypc;mypd] [myact1;myact2];;
mycomp "Res" [mypa;mypb;mypc;mypd] [myact1;myact2;myact3];;


let mypa = Proc.create "Pa" [`A ++ C`;`B ++ (D ** E)`] `C ** (G ++ H)` ;;
let mypa = Proc.create "Pa" [`A`;`B`] `C ** D` ;;
let mypb = Proc.create "Pb" [`C`;`E`] `G` ;;
let mypc = Proc.create "Pc" [`D`;`G`] `H` ;;
let myact1 = Action.create "JOIN" "Pa" "l" "Pb" "(NEG C)" "Res";;
let myact2 = Action.create "JOIN" "Res" "r" "Pc" "(NEG D)" "Rez";;
Proc.compose myst "Res" [mypa;mypb;mypc] [myact1];;
Proc.compose myst "Rez" [mypa;mypb;mypc] [myact1;myact2];;
(* xxx Provenance? *)

let mypa = Proc.create "Pa" [`A`;`B`] `C ** D` ;;
let mypb = Proc.create "Pb" [`C`;`E`] `G` ;;
let mypc = Proc.create "Pc" [`G`] `H` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG C" "Res";;
let myact2 = Action.create "JOIN" "Res" "lr" "Pc" "NEG G" "Rez";;
mycomp "Res" [mypa;mypb;mypc] [myact1];;
mycomp "Rez" [mypa;mypb;mypc] [myact1;myact2];;

let mypa = Proc.create "Pa" [`C`;`E`] `G` ;;
let mypb = Proc.create "Pb" [`A`;`B`] `C ++ D` ;;
let myact1 = Action.create "JOIN" "Pb" "lr" "Pa" "NEG C" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;
xxx;;
let mypa = Proc.create "Pa" [`A`;`B`] `C ++ D` ;;
let mypb = Proc.create "Pb" [`D`;`G`] `H` ;;
let myact1 = Action.create "JOIN" "Pa" "r" "Pb" "NEG D" "Roz";;
mycomp "Roz" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`A`;`B`] `C ** D ** X` ;;
let mypb = Proc.create "Pb" [`C`] `G` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG C" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`A`] `C ++ D` ;;
let mypb = Proc.create "Pb" [`C`;`E`;`F`] `G` ;;
let mypc = Proc.create "Pc" [`J`;`K`] `E ** L` ;;
let myact1 = Action.create "JOIN" "Pc" "l" "Pb" "NEG E" "Res";;
let myact2 = Action.create "JOIN" "Pa" "l" "Res" "NEG C" "Rez";;
Proc.compose myst "Res" [mypa;mypb;mypc] [myact1];;
Proc.compose myst "Rez" [mypa;mypb;mypc] [myact1;myact2];;

let mypa = Proc.create "Pa" [`A`] `C ++ D` ;;
let mypb = Proc.create "Pb" [`C`] `G` ;;
let mypc = Proc.create "Pc" [`D`] `H` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG C" "Res";;
let myact2 = Action.create "JOIN" "Res" "r" "Pc" "NEG D" "Rez";;
mycomp "Res" [mypa;mypb;mypc] [myact1];;
mycomp "Rez" [mypa;mypb;mypc] [myact1;myact2];;

let mypa = Proc.create "Pa" [`W`] `(A**B) ++ (C**D)` ;;
let mypb = Proc.create "Pb" [`A`;`B`;`C`] `Z` ;;
let myact1 = Action.create "JOIN" "Pa" "lrlr" "Pb" "NEG A" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;
(* is C ** C ** D actually the best outcome? *)

let mypa = Proc.create "Pa" [`A`] `B` ;;
let mypb = Proc.create "Pb" [`B`] `C` ;;
let myact1 = Action.create "JOIN" "Pa" "l" "Pb" "NEG B" "Res";;
Proc.compose myst "Res" [mypa;mypb] [myact1];;
let myres,_,myst2 = it;;
let mypc = Proc.create "Pc" [`C`] `D` ;;
let myact2 = Action.create "JOIN" "Res" "l" "Pc" "NEG C" "Roz";;
Proc.compose myst2 "Roz" [mypc;myres] [myact2];;
let myroz = fst3 it;;
print_string (Piviz.deploy myroz [myres;mypa;mypb;mypc]);;

let mypa = Proc.create "P1" [`X`] `Y` ;;
let mypb = Proc.create "P2" [`Y`] `Z` ;;
let mypc = Proc.create "P3" [`Z`] `R` ;;
let myst = Actionstate.create 7;;
let myact1 = Action.create "JOIN" "P1" "" "P2" "(NEG Y)" "Co";;
Proc.compose myst "Co" [mypa;mypb] [myact1];;
let myco,_,myst2 = it;;
let myst2 = Actionstate.create (Actionstate.ctr myst2);;
let myact2 = Action.create "JOIN" "Co" "" "P3" "(NEG Z)" "Co2";;
Proc.compose myst2 "Co2" [myco;mypc] [myact2];;
let myroz = fst3 it;;

print_string (Piviz.deploy myroz [myres;mypa;mypb;mypc]);;

let mypa = Proc.create "P1" [`X`] `Z` ;;
let mypb = Proc.create "P2" [`Y`] `Z` ;;
let myact1 = Action.create "WITH" "P1" "(NEG X)" "P2" "(NEG Y)" "Co";;
mycomp "Co" [mypa;mypb] [myact1];;

let mypa = Proc.create "P1" [`X`;`A`;`B`] `Z` ;;
let mypb = Proc.create "P2" [`Y`] `Z` ;;
let myact1 = Action.create "WITH" "P1" "(NEG X)" "P2" "(NEG Y)" "Co";;
mycomp "Co" [mypa;mypb] [myact1];;

let mypa = Proc.create "P1" [`X`] `A ** B` ;;
let mypb = Proc.create "P2" [`Y`] `B ** A` ;;
let myact1 = Action.create "WITH" "P1" "(NEG X)" "P2" "(NEG Y)" "Co";;
mycomp "Co" [mypa;mypb] [myact1];;

let mypa = Proc.create "P1" [`X`;`A`] `Z` ;;
let mypb = Proc.create "P2" [`Y`;`B`] `W` ;;
let myact1 = Action.create "WITH" "P1" "(NEG X)" "P2" "(NEG Y)" "Co";;
mycomp "Co" [mypa;mypb] [myact1];;

let mypa = Proc.create "P1" [`X`;`A`;`C`] `Z` ;;
let mypb = Proc.create "P2" [`Y`;`B`;`D`] `W` ;;
let myact1 = Action.create "WITH" "P1" "(NEG X)" "P2" "(NEG Y)" "Co";;
mycomp "Co" [mypa;mypb] [myact1];;

let mypa = Proc.create "P1" [`X`;`A`;`C`] `Z` ;;
let mypb = Proc.create "P2" [`Y`;`B`;`C`] `W` ;;
let myact1 = Action.create "WITH" "P1" "(NEG X)" "P2" "(NEG Y)" "Co";;
mycomp "Co" [mypa;mypb] [myact1];;

let mypa = Proc.create "P1" [`X`;`A`;`C`;`C`;`C`;`C`] `Z` ;;
let mypb = Proc.create "P2" [`Y`;`B`;`C`;`C`;`C`] `W` ;;
let myact1 = Action.create "WITH" "P1" "(NEG X)" "P2" "(NEG Y)" "Co";;
mycomp "Co" [mypa;mypb] [myact1];; 

let mypa = Proc.create "P1" [`X`;`A ++ B`] `C` ;;
let mypb = Proc.create "P2" [`Y`;`B ++ A`] `C` ;;
let myact1 = Action.create "WITH" "P1" "(NEG X)" "P2" "(NEG Y)" "Co";;
mycomp "Co" [mypa;mypb] [myact1];;

let mypa = Proc.create "P1" [`X`;`A ++ B`] `C` ;;
let mypb = Proc.create "P2" [`Y`;`B ++ A`;`A ++ B`] `C` ;;
let myact1 = Action.create "WITH" "P1" "(NEG X)" "P2" "(NEG Y)" "Co";;
mycomp "Co" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `A ++ B` ;;
let mypb = Proc.create "Pb" [`A ++ B`] `Y` ;;
let mypb = Proc.create "Pb" [`B ++ A`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "" "Pb" "(NEG (A ++ B))" "Res";;
let myact1 = Action.create "JOIN" "Pa" "" "Pb" "NEG (B ++ A)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `A ** B` ;;
let mypb = Proc.create "Pb" [`C ++ (A ** B)`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "" "Pb" "NEG (C ++ (A ** B))" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `A ** B ** C` ;;
let mypb = Proc.create "Pb" [`(C ** A) ** B`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "" "Pb" "NEG ((C ** A) ** B)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `D ** (A ++ B) ** C` ;;
let mypb = Proc.create "Pb" [`B ++ A`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "rlrlr" "Pb" "NEG (B ++ A)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `A ++ (B ** G)` ;;
let mypb = Proc.create "Pb" [`B ++ A`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "rlr" "Pb" "NEG (B ++ A)" "Res";;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG (B ++ A)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;
(* TODO: Can we get output Y ++ (Y ** G) ?!? *)

let mypa = Proc.create "Pa" [`X`] `A ++ B` ;;
let mypb = Proc.create "Pb" [`A ++ C ++ D`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG (A ++ C ++ D)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `A ++ B ++ C` ;;
let mypb = Proc.create "Pb" [`A ++ B`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG (A ++ B)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;
(* TODO Get output Y ++ C !!? - see next example! *)

let mypa = Proc.create "Pa" [`X`] `(A ++ B) ++ C` ;;
let mypb = Proc.create "Pb" [`A ++ B`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG (A ++ B)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `A ++ C` ;;
let mypb = Proc.create "Pb" [`A ++ B`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG (A ++ B)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `A` ;;
let mypb = Proc.create "Pb" [`(A ** B) ++ C`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "" "Pb" "NEG ((A ** B) ++ C)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;
(* TODO Yikes! Need to buffer B in larg!!! *)

(* Is it possible to get a connection to a composite input that results in 
non-leaf provenance??? *)
let mypa = Proc.create "Pa" [`X`] `B ** C` ;;

let mypb = Proc.create "Pb" [`(A ** B) ++ C`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "" "Pb" "NEG ((A ** B) ++ C)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `(A ++ B) ** (C ++ D)` ;;
let mypb = Proc.create "Pb" [`B ++ A`;`D ++ C`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG (B ++ A)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `C ++ (A ** B)` ;;
let mypb = Proc.create "Pb" [`C`] `B ** A` ;;
let mypb = Proc.create "Pb" [`C`] `A ** B` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG C" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `C ++ (A ** (B ++ D))` ;;
let mypb = Proc.create "Pb" [`C`] `(B ++ D) ** A` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG C" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `A ++ (B ** C)` ;;
let mypb = Proc.create "Pb" [`A`] `Y ++ (C ** B)` ;;
let mypb = Proc.create "Pb" [`A`] `(C ** B) ++ Y` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG A" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `(B ** C) ++ A` ;;
let mypb = Proc.create "Pb" [`A`] `Y ++ (C ** B)` ;;
let mypb = Proc.create "Pb" [`A`] `(C ** B) ++ Y` ;;
let myact1 = Action.create "JOIN" "Pa" "r" "Pb" "NEG A" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `A ** A` ;;
let mypb = Proc.create "Pb" [`A`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "r" "Pb" "NEG A" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`;`X`] `R` ;;
let mypb = Proc.create "Pb" [`A`] `X` ;;
let mypc = Proc.create "Pc" [`W`] `A ** A` ;;
let myact1 = Action.create "JOIN" "Pb" "" "Pa" "NEG X" "St1";;
let myact2 = Action.create "JOIN" "Pb" "" "St1" "NEG X" "St2";;
let myact3 = Action.create "JOIN" "Pc" "lr" "St2" "NEG A" "St3";;
mycomp "St1" [mypa;mypb] [myact1];;
mycomp "St2" [mypa;mypb] [myact1;myact2];;
mycomp "St3" [mypa;mypb;mypc] [myact1;myact2;myact3];;

let mypa = Proc.create "Pa" [`X`;`X`] `R` ;;
let mypb = Proc.create "Pb" [`A ++ B`] `X` ;;
let mypc = Proc.create "Pc" [`W`] `(A ++ B) ** (A ++ B)` ;;
let myact1 = Action.create "JOIN" "Pb" "" "Pa" "NEG X" "St1";;
let myact2 = Action.create "JOIN" "Pb" "" "St1" "NEG X" "St2";;
let myact3 = Action.create "JOIN" "Pc" "lrlr" "St2" "NEG (A ++ B)" "St3";;
mycomp "St1" [mypa;mypb] [myact1];;
mycomp "St2" [mypa;mypb] [myact1;myact2];;
mycomp "St3" [mypa;mypb;mypc] [myact1;myact2;myact3];;

let mypa = Proc.create "Pa" [`X`;`X`] `R` ;;
let mypb = Proc.create "Pb" [`A`] `X` ;;
let mypc = Proc.create "Pc" [`W`] `A ++ B` ;;
let myact1 = Action.create "JOIN" "Pb" "" "Pa" "NEG X" "St1";;
let myact2 = Action.create "JOIN" "Pb" "" "St1" "NEG X" "St2";;
let myact3 = Action.create "JOIN" "Pc" "lr" "St2" "NEG A" "St3";;
mycomp "St2" [mypa;mypb] [myact1;myact2];;
mycomp "St3" [mypa;mypb;mypc] [myact1;myact2;myact3];;

let mypa = Proc.create "Pa" [`A`;`A`] `R` ;;
let mypc = Proc.create "Pc" [`W`] `(A ++ B) ** (A ++ B)` ;;
let myact1 = Action.create "JOIN" "Pc" "lrlr" "Pa" "NEG A" "St1";;
mycomp "St1" [mypa;mypc] [myact1];;

let mypa = Proc.create "Pa" [`X`;`X`] `R` ;;
let mypb = Proc.create "Pb" [`A`] `X` ;;
let mypc = Proc.create "Pc" [`W`] `(A ++ B) ** (A ++ B)` ;;
let myact1 = Action.create "JOIN" "Pb" "" "Pa" "NEG X" "St1";;
let myact2 = Action.create "JOIN" "Pb" "" "St1" "NEG X" "St2";;
let myact3 = Action.create "JOIN" "Pc" "lrlr" "St2" "NEG A" "St3";;
mycomp "St2" [mypa;mypb] [myact1;myact2];;
mycomp "St3" [mypa;mypb;mypc] [myact1;myact2;myact3];;

let mypa = Proc.create "Pa" [`A`;`C`] `R` ;;
let mypb = Proc.create "Pb" [`W`] `(A ++ B)` ;;
let myact1 = Action.create "JOIN" "Pb" "lr" "Pa" "NEG A <> cPa_A_1" "St1";;
mycomp "St1" [mypa;mypb] [myact1];;

let mypb = Proc.create "Pb" [`W`] `(A ++ B) ** (C ++ (C ** B))` ;;
let myact1 = Action.create "JOIN" "Pb" "lrlr" "Pa" "NEG A <> cPa_A_1" "St1";;
mycomp "St1" [mypa;mypb] [myact1];;
let myact2 = Action.create "JOIN" "St1" "rrlr" "Pa" "NEG C <> cPa_C_2" "St2";;
mycomp "St2" [mypa;mypb] [myact1;myact2];;

let mypa = Proc.create "Pa" [`X`] `(A ++ B) ** (A ++ B)` ;;
let mypb = Proc.create "Pb" [`A ++ B`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "lrlr" "Pb" "NEG (A ++ B)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `(A ++ B) ** (A ++ B)` ;;
let mypb = Proc.create "Pb" [`A ++ B`;`A`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "lrlr" "Pb" "NEG (A ++ B)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `(A ++ B) ** ((A ** Z) ++ B)` ;;
let mypb = Proc.create "Pb" [`A ++ B`;`A`;`Z`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "lrlr" "Pb" "NEG (A ++ B)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `(A ++ B) ** (A ++ B)` ;;
let mypb = Proc.create "Pb" [`A ++ B`;`A ++ B`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "lrlr" "Pb" "NEG (A ++ B)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `(C ++ A ++ B) ** (A ++ B)` ;;
let mypb = Proc.create "Pb" [`A ++ B`;`A`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "lrrlr" "Pb" "NEG (A ++ B)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`X`] `(C ++ A ++ B) ** (A ++ B)` ;;
let mypb = Proc.create "Pb" [`A ++ B`;`A ++ B`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "lrrlr" "Pb" "NEG (A ++ B)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;


let mypa = Proc.create "Pa" [`X`] `A` ;;
let mypb = Proc.create "Pb" [`Y`] `B ++ C` ;;
let mypc = Proc.create "Pc" [`A`] `R` ;;
let mypd = Proc.create "Pd" [`B`] `S` ;;
let mype = Proc.create "Pe" [`R`;`S`] `Q` ;;
let myact1 = Action.create "TENSOR" "Pa" "lr" "Pb" "NEG (A)" "S1";;
let myact2 = Action.create "JOIN" "Pd" "" "Pe" "NEG (S)" "S2";;
let myact3 = Action.create "JOIN" "Pc" "" "S2" "NEG (R)" "S3";;
let myact4 = Action.create "JOIN" "S1" "rlr" "S3" "NEG (B)" "S4";;
mycomp "S1" [mypa;mypb;mypc;mypd;mype] [myact1];;
mycomp "S2" [mypa;mypb;mypc;mypd;mype] [myact1;myact2];;
mycomp "S3" [mypa;mypb;mypc;mypd;mype] [myact1;myact2;myact3];;
mycomp "S4" [mypa;mypb;mypc;mypd;mype] [myact1;myact2;myact3;myact4];;

let mypa = Proc.create "Pa" [`W`] `D ** (E ++ A)` ;;
let mypb = Proc.create "Pb" [`A`;`D`;`C`] `G` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG D" "Res";;
let myact1 = Action.create "JOIN" "Pa" "rr" "Pb" "NEG A" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`W`] `A ++ E` ;;
let mypb = Proc.create "Pb" [`E`] `G ++ A` ;;
let myact1 = Action.create "JOIN" "Pa" "r" "Pb" "NEG E" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`W`] `A ++ B` ;;
let mypb = Proc.create "Pb" [`A ++ C ++ D`] `G` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG (A ++ C ++ D)" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;





let asms = [Proc.get_cll myst2; Proc.get_cll mypc];;
let chans = itlist (@) (map get_ll_channels asms) [];;

g (list_mk_exists (chans,(list_mk_binop `==>` (asms@[`XYZ:bool`]))));;
e (REPEAT META_EXISTS_TAC);;
e (DISCH_THEN (LABEL_TAC "St2"));;
e (DISCH_THEN (LABEL_TAC "Pc"));;

let myxx = Proc.create "St2" [`A`;`A`] `R` ;;

let mysetgoal procs =
  let asms = map (gen_ll_channels o Proc.get_cll) procs in
  let preptac p = DISCH_THEN (META_SPEC_ALL_LABEL_TAC p.Proc.name) in
  let glvar = genvar `:bool` in
  ignore (g (itlist (curry mk_imp) asms (mk_exists(glvar,glvar)))) ;
  e (MAP_EVERY preptac procs THEN META_EXISTS_TAC);;

mysetgoal [mypa;mypb];;
e (ETAC_TAC 0 (Cllpi.lldrule_tac ~lbl:"P1" ~reslbl:"Res"
	      [(`A:LinProp`,`X`);(mk_var("a",Cllpi.Pcalc.chantp),`cP1_X_1`);
	       (`B:LinProp`,`Z`);
	       (`C:LinProp`,`Y`);(mk_var("c",Cllpi.Pcalc.chantp),`cP2_Y_1`)]
	      Clltac.Rules.ll_with_serv));;
e (Cllpi.ll_meta_lbl_asm "P2" (top_metas (p())));;

let PRINT_GOAL_TAC gl =
  print_goal gl; print_newline(); ALL_TAC gl;;

let PRINT_TAC s gl =
  print_string s; print_newline(); ALL_TAC gl;;

let myp = Proc.create "P" [`X ++ Y`] `(X ++ Y) ** (X ++ Y) ** (X ++ Y) ** (X ++ Y)` ;;
let myp1 = Proc.create "P1" [`X ++ Y`] `O1` ;;
let myp2 = Proc.create "P2" [`X ++ Y`] `O2` ;;
let myp3 = Proc.create "P3" [`X ++ Y`] `O3` ;;
let myp4 = Proc.create "P4" [`X ++ Y`] `O4` ;;
let myst = Actionstate.create 1;;
let myact1 = Action.create "JOIN" "P" "lrlr" "P1" "(NEG (X ++ Y))" "S1";;
let myact2 = Action.create "JOIN" "S1" "rlr" "P2" "(NEG (X ++ Y))" "S2";;
let myact3 = Action.create "JOIN" "S2" "lrlrlr" "P3" "(NEG (X ++ Y))" "S3";;
let myact4 = Action.create "JOIN" "S3" "lrlrlr" "P4" "(NEG (X ++ Y))" "S4";;

Proc.compose myst "S1" [myp;myp1;myp2;myp3;myp4] [myact1];;
Proc.compose myst "S3" [myp;myp1;myp2;myp3;myp4] [myact1;myact2;myact3];;
Proc.compose myst "S3" [myp;myp1;myp2;myp3;myp4] [myact1;myact2;myact3;myact4];;

let mys3,_,myst2 = Proc.compose myst "S3" [myp;myp1;myp2;myp3;myp4] [myact1;myact2;myact3];;
let myact4' = Action.create "JOIN" "S3" "lrlrlr" "P4" "(NEG (X ++ Y))" "S4";;
Proc.compose myst2 "S1" [myp;myp1;myp2;myp3;myp4;mys3] [myact4'];;


myff (mypf,myst);;

let mypa = Proc.create "P1" [`X`;`A`;`C`] `Z` ;;
let mypb = Proc.create "P2" [`Y`;`B`;`C`] `W` ;;
let myact1 = Action.create "WITH" "P1" "(NEG X)" "P2" "(NEG Y)" "Co";;

mysetgoal [mypa;mypb];;
e (ETAC_TAC' Actionstate.print (Actionstate.create 0) (REFRESH_CHANS_TAC "P1"));;
e (ETAC_TAC' Actionstate.print (Actionstate.create 1) (Action.apply myact1));;
e (Cllpi.ll_meta_lbl_asm "Co" (top_metas(p())));;
top_thm();;
(instantiate (top_inst(p())) o snd o strip_exists o concl o UNDISCH_ALL o top_thm) ();;
   


let mypa = Proc.create "Pa" [`X`;`X`] `R` ;;
let mypb = Proc.create "Pb" [`A`] `X` ;;
let mypc = Proc.create "Pc" [`W`] `A ** A` ;;
let myact1 = Action.create "JOIN" "Pb" "" "Pa" "NEG X" "St1";;
let myact2 = Action.create "JOIN" "Pb" "" "St1" "NEG X" "St2";;
let myact3 = Action.create "JOIN" "Pc" "lr" "St2" "NEG A" "St3";;
mysetgoal [mypa;mypb;mypc];;
e (ETAC_TAC' Actionstate.print (Actionstate.create 0) (Action.apply myact1));;
(* e (ETAC_TAC' Actionstate.print (Actionstate.create 3) (REFRESH_CHANS_TAC "Pb"));;
e (ETAC_TAC' Actionstate.print (Actionstate.create 4) (REFRESH_CHANS_TAC "St1"));; *)
e (ETAC_TAC' Actionstate.print (Actionstate.create 3) (Action.apply myact2));;


(* =========================================================================== *)
(* PI SUB  *)
(* =========================================================================== *)

let varpairs,newtm = pi_instvars (mk_icomb (`FN`,myres));;
let agentpaths,newtm' = INST_AGENTS newtm [] (!defined_agents);;
let mythm = NAMES_REDUCE_CONV newtm';;
let res = UNINST_AGENTS ((rhs o concl) thm) agentpaths;;
((pi_uninst varpairs) o rhs o concl) mythm;;


(* let PI_VAR_RED conv tm = *)
let varpairs,newtm = pi_instvars qqterm ;;
let agentpaths,newtm' = INST_AGENTS newtm [] (!defined_agents);;

let newtm'' =  mk_icomb (`FN`,newtm');;
let mytm =  mk_icomb (`FN`,mytm);;


my_time NAMES_REDUCE_CONV mytm;;



let thm = conv newtm';;
let res = UNINST_AGENTS ((rhs o concl) thm) agentpaths;;
pi_uninst varpairs res;;


let mytm2 =  `NAMES
   (Res [46]
   (Comp
     (Res [29]
     (Comp
       (Comp (In 4 [0] Zero)
       (Comp (In 5 [1] Zero)
       (Res [2; 3] (Out 6 [2; 3] (Comp (Out 2 [16] Zero) (Out 3 [19] Zero))))))
      (In 28 [20; 21]
      (Res [27]
      (Comp
        (Res [14]
        (Comp
          (Comp (In 8 [7] Zero) (Comp (In 9 [10] Zero) (Out 11 [12] Zero)))
        (Comp (In 13 [12] Zero) (Out 15 [18] Zero)) ))
       (Comp (In 20 [16] Zero)
       (Comp (In 21 [19] Zero)
       (Comp (In 26 [18] Zero)
       (Res [24; 25]
       (In 30 [22; 23]
       (Plus (Out 22 [24] (Out 24 [35] Zero))
       (Out 23 [25] (Out 25 [17] Zero))))))))
      )))
    ))
    (Res [31; 38]
    (Out 45 [31; 38]
    (Plus
     (In 31 [37]
     (Res [36]
     (In 39 [33; 32]
     (Out 33 [36] (Comp (In 37 [35] Zero) (Out 36 [34] Zero))))))
    (In 38 [42]
    (Res [43] (In 39 [40; 41] (Out 41 [43] (In 42 [44] (Out 43 [44] Zero)))))))))
   ))` ;;

let mytm2 =  `piSUBN1
   (Res [46]
   (Comp
     (Res [29]
     (Comp
       (Comp (In 4 [0] Zero)
       (Comp (In 5 [1] Zero)
       (Res [2; 3] (Out 6 [2; 3] (Comp (Out 2 [16] Zero) (Out 3 [19] Zero))))))
      (In 28 [20; 21]
      (Res [27]
      (Comp
        (Res [14]
        (Comp
          (Comp (In 8 [7] Zero) (Comp (In 9 [10] Zero) (Out 11 [12] Zero)))
        (Comp (In 13 [12] Zero) (Out 15 [18] Zero)) ))
       (Comp (In 20 [16] Zero)
       (Comp (In 21 [19] Zero)
       (Comp (In 26 [18] Zero)
       (Res [24; 25]
       (In 30 [22; 23]
       (Plus (Out 22 [24] (Out 24 [35] Zero))
       (Out 23 [25] (Out 25 [17] Zero))))))))
      )))
    ))
    (Res [31; 38]
    (Out 45 [31; 38]
    (Plus
     (In 31 [37]
     (Res [36]
     (In 39 [33; 32]
     (Out 33 [36] (Comp (In 37 [35] Zero) (Out 36 [34] Zero))))))
    (In 38 [42]
    (Res [43] (In 39 [40; 41] (Out 41 [43] (In 42 [44] (Out 43 [44] Zero)))))))))
   )) (21,50)` ;;


my_time NAMES_REDUCE_CONV mytm2;;
my_time (NAMES_CONV NUM_REDUCE_CONV) mytm2;;
my_time (PISUBN1_CONV []) mytm2;;
Time: 4.640290 ;;


let rec SUBN_CONV tm =
  if (is_strconst "Zero" (rand tm)) then PURE_REWRITE_CONV[piSUBN_RECURSION] tm else
  let comb,args = strip_comb (rand tm) in
  let conv =
    if (is_strcomb "Out" comb) then 
    PATH_CONV "rr" (NAMES_CONV eqconv) THENC RAND_CONV (REWRITE_CONV[APPEND])
(*    else if (is_strcomb "In" comb) then
    PATH_CONV "rr" (NAMES_CONV eqconv) THENC RAND_CONV (REWRITE_CONV[APPEND])
    else if (is_strcomb "Tau" comb) then 
    NAMES_CONV eqconv
    else if (is_strcomb "Res" comb) then 
    PATH_CONV "r" (NAMES_CONV eqconv) THENC REWRITE_CONV[APPEND]
    else if (is_strcomb "Match" comb) then 
    PATH_CONV "rr" (NAMES_CONV eqconv)
    else if (is_strcomb "Comp" comb) then 
    PATH_CONV "lr" (NAMES_CONV eqconv) THENC PATH_CONV "r" (NAMES_CONV eqconv) THENC REWRITE_CONV[APPEND]
    else if (is_strcomb "Plus" comb) then 
    PATH_CONV "lr" (NAMES_CONV eqconv) THENC PATH_CONV "r" (NAMES_CONV eqconv) THENC REWRITE_CONV[APPEND]
    else if (is_strcomb "Repl" comb) then 
    NAMES_CONV eqconv *)
    else failwith ("SUBN_CONV: Unknown pi-calculus combinator: " ^ (string_of_term comb)) in
  (PURE_ONCE_REWRITE_CONV[piSUBN_RECURSION] THENC conv) tm;;


let mytm = `(FN (Comp (In 33 [7; 6] (In 7 [8; 9] Zero))
   (Res [11; 16]
   (Out 32 [11; 16]
   (Plus (In 11 [12] (Res [15] (In 17 [14; 13] (Out 14 [15] Zero))))
   (In 16 [20]
   (Res [21]
   (In 17 [18; 19]
   (Out 19 [21]
   (In 20 [22] (Out 21 [22] (Comp (In 29 [25] Zero)
     (Comp (In 30 [26] Zero)
     (Res [27; 28]
     (Out 32 [27; 28] (Comp (Out 27 [23] Zero) (Out 28 [24] Zero))))))))))))))))) LDIFF [26]` ;;

	    Time: 0.412025;;

let xy = `FN (Out 1 [2;3] Zero)` ;;
let xy = `FN (In 1 [2;3] Zero)` ;;
let xy = `FN (In 1 [2;3] (Out 1 [2;3;4;5] Zero))` ;;
let xy = `SUBN (Out 1 [2;3] Zero) (SUB1F 1 3)` ;;

PURE_ONCE_REWRITE_CONV [FN;NAMES;BN] xy;;


let xx = (rhs o concl) it ;;
follow_path "lrllr" xx;;
NUM_REDUCE_CONV it;;

FN_CONV NUM_REDUCE_CONV xy;;

let xx = `[1; 2; 3; 4; 5] LDIFF [2; 3]` ;;
let xx = `[1; 2; 3; 4; 5; 3; 6; 7] DEL 3` ;;
	  
let PRINTSN_CONV tm = 
  let comb = (fst o strip_comb) tm in 
  if comb = `(SUBN1):(num)Agent->num#num->(num)Agent` then 
    (print_term tm ; print_newline () ; print_newline (); failwith "") else
    (failwith "");;

let PRINT_CONV conv tm = print_term tm ; print_newline () ; print_newline () ; conv tm;;


let newtm = `SUBN1
  (Res [0; 1]
     (In 2 [5;6] (Res [3;4] (Out 5 [0;1]
			       (Comp Zero (Res [4] (Comp (SUBN1 Zero (2,4)) (SUBN1 Zero (3,4)))))))))
  (5,6)` ;;


my_time PISUBN1_CONV newtm;;


(* =========================================================================== *)
(* BUFFER_TAC *)
(* =========================================================================== *)

g `?P x. (|-- (' (NEG A <> ii) ^' (A <> oo)) P)` ;;
g `?P x. (|-- (' (NEG (A ** B) <> ii) ^' ((A ** B) <> oo)) P)` ;;
g `?P x. (|-- (' (NEG (A ** B ** C ** D) <> ii) ^' ((A ** B ** C ** D) <> oo)) P)` ;;
g `?P x. (|-- (' (NEG (A ++ B) <> ii) ^' ((A ++ B) <> oo)) P)` ;;
g `?P x. (|-- (' (NEG (A ++ (B ** C ++ D)) <> ii) ^' ((A ++ (B ** C ++ D)) <> oo)) P)` ;;
g `?P x. (|-- (' (NEG ((A ** C ++ D) ++ (B ** C ++ D)) <> ii) ^' (((A ** C ++ D) ++ (B ** C ++ D)) <> oo)) P)` ;;
e (REPEAT META_EXISTS_TAC);;
e (ETAC_TAC' Actionstate.print (Actionstate.create 0) Clltac.BUFFER_TAC);;
top_thm();;
instantiate (top_inst (p())) `P:NAgent` ;;

g `?P x. (|-- (' (NEG A <> ai) ^' (NEG B <> bi) ^' ((A ** B) <> oo)) P)` ;;
g `?P x. (|-- (' (NEG A <> ai) ^' (NEG (B ++ C) <> bi) ^' ((A ** B ++ C) <> oo)) P)` ;;
e (REPEAT META_EXISTS_TAC);;
e (ETAC_TAC' Actionstate.print (Actionstate.create 0) Clltac.PARBUF_TAC);;
top_thm();;
instantiate (top_inst (p())) `P:NAgent` ;;




				      
(* =========================================================================== *)
(* OLD TESTS THAT NEED PORTING *)
(* =========================================================================== *)


let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' (((A ** D) ++ (E ++ K)) <> ae)) Pa) ==>
  (|-- (' (NEG (A ** D) <> a)^' (NEG B <> b)^' (NEG G <> g)^' (NEG H <> h)^' (NEG J <> j)
	^ ' (((C ** L) ++ M) <> c)) Pb) ==>
P` ;;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' (((A ** D) ++ (E ++ K)) <> ae)) Pa) ==>
  (|-- (' (NEG (E ++ K) <> a)^' (NEG B <> b)^' (NEG G <> g)^' (NEG H <> h)^' (NEG J <> j)
	^ ' (((C ** L) ++ M) <> c)) Pb) ==>
P` ;;
(*  (|-- (' (NEG W <> w)^' (NEG B <> b) ^ ' ((C ++ (B ** E)) <> x)) P)` ;;*)

gll mytm;;
e (REPEAT META_EXISTS_TAC);;
e (REPEAT DISCH_TAC);;
e (FIRST_ASSUM (OPT_INPUT_TAC `A:LinProp` `E:LinProp`));;
e (FIRST_ASSUM (OPT_INPUT_TAC `A ** D` `E ++ K`));;
e COMP_OUTPUT_BUFFER_TAC;;
e (lldrule_tac [`C`,`A ++ E`;`G`,`' (NEG W <> w)`] ll_cut);;
e (lldrule_tac [`C`,`(A ** D) ++ E ++ K`;`G`,`' (NEG W <> w)`] ll_cut);;
ellma();;
top_thm();;
b();;

instantiate ((snd o fst3 o hd o p) ()) `P:bool` ;;


let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' (((A ++ D) ** (B ** H)) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a)^' (NEG B <> b)^ '(C <> c)) Pb) ==>
P` ;;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' (((A ++ D) ** (B ** H)) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a)^' (NEG B <> b)^ '(A <> c)) Pb) ==>
P` ;;
(*  (|-- (' (NEG W <> w)^' (NEG B <> b) ^ ' ((C ++ (B ** E)) <> x)) P)` ;;*)

let mydeb mytm = (gll mytm ; ell (REPEAT META_EXISTS_TAC THEN REPEAT (DISCH_THEN LABEL_SERV) THEN LABEL_JOIN_TAC "Pa" "Pb"));;





(* ************************************************************ *)
(* ************************************************************ *)
(* ******************** TESTS START HERE! ********************* *)
(* ************************************************************ *)
(* ************************************************************ *)

Cenv.Composer.Proc_store.get (snd (Cenv.get myid)) "Pe";;
Cenv.Composer.Proc_store.get_parents (snd (Cenv.get myid)) "Pe";;
let xdep_defs =  map ((fun x -> x.Cenv.Composer.Proc.proc_def) o (Cenv.Composer.Proc_store.get (snd (Cenv.get myid)))) it;;
let xproc = (rhs o concl o REWRITE_CONV[piSUBN1;piSUBN] o rhs o concl o REWRITE_CONV Cllpi.CLL_PROCS o rhs o snd o strip_forall) (Cenv.get_proc_def myid "Pe");;


let xproc = `(piSUB NCH (Pc (z0,cPa_A_1__,cPa_B_2__,cPb_E_2__)) (FEMPTY |+ (z0,z1)))` ;;
let xdep_defs = [(hd o tl) xdep_defs];;
let xathms = map ASSUME (filter (is_agent_def `:num`) xdep_defs);;
let xthm1 = REWRITE_CONV xathms xproc;;

	     
(* TODO TODO Pa is free in assumption of Pc so it doesn't rewrite xproc! *)

DEPTH_CONV (PI_AGENT_REDUCE_CONV xdep_defs reduce_pap_subs (PI_CONV PI_SUBN_CONV)) xproc;;





let xcll = Cc.Proc.mk_cll_def [] "Pa" [`NEG A`;`NEG B`] `C ** D` ;;
let xproc = Cllpi.cll_to_proc xcll;;
let xchans = (dest_list o rhs o concl o Cllpi.proc_fn_conv o mk_icomb) (Cllpi.proc_fn,xproc);;
let xcall = Cc.Proc.mk_call "Pa" xchans;;
let xdef = list_mk_forall (xchans,(mk_eq (xcall,xproc)));;
REWRITE_CONV Cllpi.CLL_PROCS xproc;;


let (LABEL_PROC:thm_tactic) =
  let get_label thm =
    try (
      let agent = (fst o strip_comb o Cllpi.process_of_term o concl) thm in
        if (is_const agent) then (fst o dest_const) agent
        else if (is_var agent) then (fst o dest_var) agent
        else ""
    ) with Failure _ -> "" in
    fun thm ->
      LABEL_TAC (get_label thm) thm;;

let mysetup tm =
  let _ = g tm in
  e (REPEAT META_EXISTS_TAC THEN REPEAT (DISCH_THEN LABEL_PROC));;



let mytm = `?P x. (|-- (' (NEG W <> w) ^ ' (A <> a)) Pa) ==>
  (|-- (' (NEG A <> a)^' (B <> b)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "" "Pb" "" "Res");;
 
let mytm =  `?P x:num. (|-- (' (NEG W <> w) ^ ' ((A ** B) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a)^' (NEG C <> c)
	^ ' (D <> d)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "l" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((A ** B) <> ae)) Pa) ==>
  (|-- (' (NEG B <> b)^' (NEG C <> c)
	^ ' (D <> d)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "r" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((A ** B) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a)^' (NEG B <> b)^' (NEG C <> c)
	^ ' (D <> d)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "l" "Pb" "" "Res");;
b();;
e (Ct.JOIN_TAC "Pa" "r" "Pb" "" "Res");;


let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((A ** B ** C) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a)^' (NEG B <> b)^' (NEG C <> c)
	^ ' (D <> d)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "l" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((A ** B ** C ** D) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a)^' (NEG D <> b)^' (NEG G <> c)
	^ ' (D <> d)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "l" "Pb" "" "Res");;
b();;
e (Ct.JOIN_TAC "Pa" "rrr" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((A ** B ** C ** D) <> ae)) Pa) ==>
  (|-- (' (NEG G <> a)^' (NEG H <> b)^' (NEG J <> c)
	^ ' (K <> d)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "l" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' (((A ** B) ** E) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a)^' (NEG B <> b)^' (NEG C <> c)
	^ ' (D <> d)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "lr" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((A ++ E) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a)^' (NEG B <> b)^' (NEG C <> c)
	^ ' (E <> e)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "l" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((E ++ A) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a)^' (NEG B <> b)^' (NEG C <> c)
	^ ' (E <> e)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "r" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' (((E ++ A)) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a) ^ ' (E <> e)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "r" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' (((A ++ E)) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a) ^ ' (E <> e)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "l" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' (((A ** B) ++ E) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a)^' (NEG B <> b)^' (NEG C <> c)
	^ ' (D <> d)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "ll" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((A ++ E) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a)^' (NEG B <> b)^' (NEG E <> c)
	^ ' (D <> d)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "l" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' (((A ** B) ++ E) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a)^' (NEG B <> b)^' (NEG E <> c)
	^ ' (D <> d)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "l" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((B ** (A ++ E)) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a) ^ ' (E <> e)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "rl" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((D ** (E ++ A)) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a)^' (NEG B <> b)^' (NEG C <> c)
	^ ' (E <> e)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "rr" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((D ** (E ++ A)) <> ae)) Pa) ==>
  (|-- (' (NEG D <> d)^' (NEG C <> c)
	^ ' (G <> g)) Pb) ==>
P` ;;
mysetup mytm;;
(* Interesting case: options are ignored unless selected (prioritized) *)
e (Ct.JOIN_TAC "Pa" "ll" "Pb" "" "Res");;


let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((D ** (E ++ A)) <> ae)) Pa) ==>
  (|-- (' (NEG A <> a)^' (NEG D <> d)^' (NEG C <> c)
	^ ' (G <> g)) Pb) ==>
P` ;;
mysetup mytm;;
(* Interesting case: options are ignored unless selected (prioritized) *)
e (Ct.JOIN_TAC "Pa" "ll" "Pb" "" "Res");; 
b();;
e (Ct.JOIN_TAC "Pa" "rr" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((A ++ E) <> ae)) Pa) ==>
  (|-- (' (NEG E <> c)
	^ ' ((A ++ G) <> d)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "r" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((A ++ E) <> ae)) Pa) ==>
  (|-- (' (NEG E <> c)
	^ ' ((G ++ A) <> d)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "r" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((A ++ E) <> ae)) Pa) ==>
  (|-- (' (NEG A <> c)
	^ ' ((E ++ G) <> d)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "l" "Pb" "" "Res");;

let mytm =  `?P x. (|-- (' (NEG W <> w) ^ ' ((A ++ E) <> ae)) Pa) ==>
  (|-- (' (NEG A <> c)
	^ ' ((G ++ E) <> d)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.JOIN_TAC "Pa" "l" "Pb" "" "Res");;


let mytm =  `?P x. 
  (|-- (' (NEG A <> na) ^ ' ((G ** H)  <> g)) Pa) ==>
  (|-- (' (NEG B <> n)^' (NEG C <> c)^ ' (E <> e)) Pb) ==>
  (|-- (' (NEG W <> w) ^ ' ((A ** B) <> ab)) Pc) ==>
P` ;;
mysetup mytm;;
e (Ct.TENSOR_TAC "Pa" "" "Pb" "" "Res");;
e (Ct.JOIN_TAC "Pc" "l" "Res" "" "Res2");;
b();;
b();;
e (Ct.JOIN_TAC "Pc" "l" "Pa" "" "Res");;
e (Ct.JOIN_TAC "Res" "r" "Pb" "" "Res2");;

let mytm =  `?P x. 
  (|-- (' (NEG A <> na) ^ ' (B <> b)) Pa) ==>
  (|-- (' (NEG A <> naa) ^ ' (B <> bb)) Pb) ==>
  (|-- (' (NEG A <> naaa) ^ ' (B <> bbb)) Pc) ==>
P` ;;

let mytm =  `?P x. 
  (|-- (' (NEG W <> nw) ^ ' ((A ++ C) <> b)) Pa) ==>
  (|-- (' (NEG (A ++ C) <> nc) ^ ' (D <> d)) Pb) ==>
P` ;;

let mytm =  `?P x. 
  (|-- (' (NEG A <> a) ^ ' (NEG B <> b) ^ ' (NEG C <> c) ^ ' (D <> d)) Pa) ==>
  (|-- (' (NEG X <> x) ^ ' (NEG Y <> y) ^ ' (NEG C <> c) ^ ' (NEG W <> w) ^ ' (Z <> z)) Pb) ==>
P` ;;


let mytm =  `?P x. 
  (|-- (' (NEG A <> a) ^ ' (D <> d)) Pa) ==>
  (|-- (' (NEG X <> x) ^ ' (Z <> z)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.WITH_TAC "Pa" "NEG A <> a" "Pb" "NEG X <> x" "Res");;

let mytm =  `?P x. 
  (|-- (' (NEG A <> a) ^ ' (D <> da)) Pa) ==>
  (|-- (' (NEG X <> x) ^ ' (D <> db)) Pb) ==>
P` ;;
mysetup mytm;;

e (Ct.WITH_TAC "Pa" "NEG A <> a" "Pb" "NEG X <> x" "Res");;

let mytm =  `?P x. 
  (|-- (' (NEG A <> a) ^ ' (NEG B <> b) ^ ' (NEG C <> c) ^ ' (D <> d)) Pa) ==>
  (|-- (' (NEG X <> x) ^ ' (NEG Y <> y) ^ ' (NEG W <> w) ^ ' (Z <> z)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.WITH_TAC "Pa" "NEG A <> a" "Pb" "NEG X <> x" "Res");;
e (Ct.WITH_TAC "Pa" "NEG A <> a" "Paa" "NEG B <> b" "Res");;

let mytm =  `?P x. 
  (|-- (' (NEG A <> a) ^ ' (NEG B <> b) ^ ' (NEG C <> c) ^ ' (D <> d)) Pa) ==>
  (|-- (' (NEG X <> x) ^ ' (NEG Y <> y) ^ ' (NEG W <> w) ^ ' (Z <> z)) Pb) ==>
P` ;;
mysetup mytm;;
e (Ct.WITH_TAC "Pa" "NEG A <> a" "Pb" "NEG X <> x" "Res");;
e (Ct.WITH_TAC "Pa" "NEG A <> a" "Paa" "NEG B <> b" "Res");;

mk_llservice "P" `(' (NEG R <> r) ^ ' ((A ** B ** C) <> z))` ;;
mk_llservice "P1" `(' (NEG R <> r) ^ ' ((A ** B) <> z))` ;;
print_string (scala_atomic_service "P1");;

let rec cll_latex chans tm =
let replace input output =
    Str.global_replace (Str.regexp_string input) output in

  let rec clltm_latex tm =
    let comb,args = strip_comb tm in
      try
        if (is_var comb) then
          ((replace "_" "\\_") o fst o dest_var) comb
        else if (comb = `NEG`) then
          (((clltm_latex o  hd) args) ^ "^\\bot")
        else if (comb = `LinTimes`) then
          ("(" ^ (clltm_latex (hd args)) ^ " \\otimes " ^ (clltm_latex (hd (tl args))) ^ ")")
        else if (comb = `LinPar`) then
          ("(" ^ (clltm_latex (hd args)) ^ " \\parr " ^ (clltm_latex (hd (tl args))) ^ ")")
        else if (comb = `LinPlus`) then
          ("(" ^ (clltm_latex (hd args)) ^ " \\oplus " ^ (clltm_latex (hd (tl args))) ^ ")")
        else if (comb = `LinWith`) then
          ("(" ^ (clltm_latex (hd args)) ^ " \\with " ^ (clltm_latex (hd (tl args))) ^ ")")
        else failwith ""
      with Failure s -> failwith ("clltm_latex (" ^ string_of_term(tm) ^ ") :" ^ s) in

  let tm_latex ltm =
    let _,args = strip_comb ltm in
    let cll,chan = hd args,(hd o tl) args in
    let cll' = clltm_latex cll in
    let chan' = (fst o dest_var) chan in
      if (chans) then (chan' ^ " \\cln " ^ cll') else cll' in

  let rec tms_latex tml =
    (match tml with
       | [] -> ""
       | [h] -> (tm_latex o snd o dest_comb) h
       | h::t -> (((tm_latex o snd o dest_comb) h) ^ ",\\ " ^ (tms_latex t))
    ) in

  let _,args = strip_comb tm in
  let clls,proc = (rev o strip_munion o hd) args,(hd o tl) args in
    if (chans)
    then ("\\vdash " ^ (piviz_string proc) ^ "\\cc " ^ (tms_latex clls))
    else ("\\vdash " ^ (tms_latex clls));;


let my_hash = Hashtbl.create 50;;
Hashtbl.add my_hash "h" "hello";
Hashtbl.add my_hash "w" "wine";;
Hashtbl.replace my_hash "t" "tralala";;
Hashtbl.length my_hash;;
Hashtbl.fold (fun k v l -> v::l) my_hash [];;
Hashtbl.iter (fun k v -> Hashtbl.replace my_hash k (v^"1")) my_hash;;
Hashtbl.mem my_hash "h";;
Hashtbl.mem my_hash "x";;

module type Patata =
  sig
  val a : int
  val b : int
  end ;;

module Patatata : Patata =
  struct
  let a = 1
  let b = 2
  end;;

module type Ntomata =
  sig
  val xuma : int
  end ;;

module Patatontomata (Pa : Patata) : Ntomata =
  struct
  let xuma = Pa.a + Pa.b
  end ;;

module Salata (Nt : Ntomata) : sig
val karoto : int
end = struct
let karoto = Nt.xuma * 2
end;;

module Sout = Salata(Patatontomata(Patatata));;




let myout = `(X ++ Y) ** (X ++ Y) ** (X ++ Y) ** (X ++ Y)` ;;
let myout = `(X ++ Y) ** (A ++ B) ** (C ++ D) ** (E ++ F)` ;;
let myout = `(X ++ Y) ** A ** B` ;;
let mypath = "lrlr";;

let mypath = "rlr";;
let mypath = "rlr";;

let mysetup tm =
  let _ = g tm in
  e (REPEAT META_EXISTS_TAC THEN (DISCH_THEN (LABEL_TAC "P")));;

follow_path mypath myout;;

let mytm =  `?P. (|-- (' (NEG (X ++ Y) <> a) ^ ' (R <> r)) P) ==> XYZ` ;;
mysetup mytm;;
let mytm =  `?P. (|-- (' (NEG (X) <> a) ^ ' ((A ** B ** C) <> r)) P) ==> XYZ` ;;
mysetup mytm;;

let myout = `(X ++ Y) ** A ** B` ;;
let mypath = "rlr";;

let mytm =  `?P. (|-- (' (NEG (X) <> a) ^ ' ((R) <> r)) P) ==> XYZ` ;;
let mypath = "lrlr";;
mysetup mytm;;

let mytm =  `?P. (|-- (' (NEG (Y) <> a) ^ ' ((R) <> r)) P) ==> XYZ` ;;
let mypath = "lrr";;
mysetup mytm;;

let mytm =  `?P. (|-- (' (NEG (A) <> a) ^ ' ((R) <> r)) P) ==> XYZ` ;;
let mypath = "rlr";;
mysetup mytm;;

e (Actionstate.TAC (INPUT_TAC myout mypath "P"));;

let myout = `((Z ** ( A ++ B )) ** (C ++ D) ) ** (X ++ Y)` ;;

let mytm =  `?P. (|-- (' (NEG (X ++ Y) <> a) ^ ' ((R) <> r)) P) ==> XYZ` ;;
let mypath = "r";;
mysetup mytm;;

let mytm =  `?P. (|-- (' (NEG (Y) <> a) ^ ' ((R) <> r)) P) ==> XYZ` ;;
let mypath = "rlrr";;
mysetup mytm;;

let mytm =  `?P. (|-- (' (NEG (A) <> a) ^ ' ((R) <> r)) P) ==> XYZ` ;;
let mypath = "rlr";;
mysetup mytm;;

e (Actionstate.TAC (INPUT_TAC myout mypath "P"));;


let myout = `((X ++ Y) ** O3 ** O2) ** O1` ;;
let mypath = "lrlrlr";;
let mytm =  `?P. (|-- (' (NEG (X ++ Y) <> a) ^ ' (R <> r)) P) ==> XYZ` ;;
mysetup mytm;;
(*  ' (((R ** B) ** (X ++ Y)) <> z3 *)
e (Actionstate.TAC (INPUT_TAC myout mypath "P"));;


	      

	      
let mytm =  `?P. (|-- (' (NEG A <> a) ^ ' (NEG B <> b) ^ ' (NEG C <> c) ^ ' (X <> x)) P) ==> XYZ` ;;
mysetup mytm;;

let XINPUT_TAC out path = (Actionstate.TAC (INPUT_TAC out path "P"));;

e (XINPUT_TAC `A:LinProp` "");;
b();;
e (XINPUT_TAC `G:LinProp` "");;

e (XINPUT_TAC `A ** B` "lr");;
b();;
e (XINPUT_TAC `A ** B ** C` "lrlr");;
b();;
e (XINPUT_TAC `B ** B` "lr");;
b();;
e (XINPUT_TAC `A ** B ** B` "lr");;
b();;
e (XINPUT_TAC `A ** B ** B ** C` "lr");;
b();;
e (XINPUT_TAC `A ** B ** C ** B` "lr");;
b();;
e (XINPUT_TAC `B ** C` "l");;
e (XINPUT_TAC `A ** B ** C` "l");;
b();;
b();;
e (XINPUT_TAC `(A ** B) ** (A ** B)` "ll");;
b();;
e (XINPUT_TAC `(A ** D) ** (E ** F)` "ll");;
b();;
e (XINPUT_TAC `(A ** B) ** B` "rr");;
b();;
e (XINPUT_TAC `(A ** B) ** B` "lr");;
b();;
e (XINPUT_TAC `D ** C` "l");;
e (XINPUT_TAC `D ** C` "r");;
b();;
e (XINPUT_TAC `D ** E` "l");;
e (XINPUT_TAC `D ** E` "r");;

e (XINPUT_TAC `A ++ E` "lr");;
b();;
e (XINPUT_TAC `A ++ E` "r");;
e (XINPUT_TAC `(A ** B) ++ E` "ll");;
b();;
e (XINPUT_TAC `(A ** B) ++ E` "ll");;
b();;

e (COPY_TAC ("Pa","Paa"));;
e (Ct.WITH_TAC "Pa" "NEG A <> a" "Paa" "NEG B <> b" "Res");; (* TODO: bug? *)

(* -- *)

let mytm =  `?P. (|-- (' (NEG X <> x) ^ ' (Y <> y)) Pa) ==> P` ;;
mysetup mytm;;


e (INPUT_TAC `X ++ Y` "l" xlbl);;
b();;

e (INPUT_TAC `Y ++ X` "r" xlbl);;
b();;

let mytm =  `?P. (|-- (' (NEG X <> x) ^ ' ((A ++ B) <> y)) Pa) ==> P` ;;
mysetup mytm;;

e (INPUT_TAC `X ++ A` "l" xlbl);;
b();;
e (INPUT_TAC `X ++ B` "l" xlbl);;
b();;
e (INPUT_TAC `A ++ X` "r" xlbl);;
b();;
e (INPUT_TAC `B ++ X` "r" xlbl);;
b();;
e (INPUT_TAC `C ++ X` "r" xlbl);;
b();;
e (INPUT_TAC `X ++ C` "l" xlbl);;
b();;
e (INPUT_TAC `(X ** A) ++ (C ** D)` "ll" xlbl);;
b();;


module type Patatype =
  sig
  val pat : int -> int
  val ntom : int -> int
  end;;

module Patata: Patatype =
struct
let pat i = i + 1
let ntom i = i * 2
end;;

module Ntomata: functor (Pat:Patatype) -> Patatype =
  functor (Pat:Patatype) ->
  struct
  open Pat
  let pat i = .pat i + 5
  let ntom = ntom
  end;;

module Patntom = Ntomata(Patata);;
Patntom.ntom 5;;
Patntom.pat 5;;




(* JSON *)

let myins = [`A:LinProp`;`B:LinProp`;`C++D`];;
let myout = `A ** (B ++ C) ** D` ;;
let mypins = map Json_comp.from_linprop myins;;
let mypout = Json_comp.from_linprop myout;;
let mycmd = Object [
  ("command", String "create");
  ("name", String "Pa");
  ("inputs", Array mypins);
  ("output", mypout) ];;

let myres = Json_composer_io.execute_string (Json_io.string_of_json mycmd);;

(* Myjson.to_process myres;;*)

let mycreate name ins out =
  let jins = map Json_comp.from_linprop ins
  and jout = Json_comp.from_linprop out in
  Json_composer_io.execute_string (
    Json_io.string_of_json (
      Object [
	("command", String "create");
	("name", String name);
	("inputs", Array jins);
	("output", jout) ]));
    Proc.create name ins out;;


let mypa = mycreate "Pa" [`A:LinProp`;`B:LinProp`] `C ** D` ;;
let mypb = mycreate "Pb" [`C:LinProp`;`E:LinProp`] `G:LinProp` ;;
let mypd = mycreate "Pd" [`D:LinProp`;`G:LinProp`] `H:LinProp` ;;
let myst = Actionstate.create 0;;					      
let myact1 = Action.create "JOIN" "Pa" "l" "Pb" "" "Res";;
let myactq = Action.create "JOIN" "Res" "r" "Pd" "" "Rez";;


let mycompose st name deps acts res =
  let str = 
    Json_io.string_of_json (
      Object [
	("command", String "compose_all");
	("name", String name);
	("components", Array (map Json_comp.from_process deps));
	("actions", Array (map Json_comp.from_action acts));
	("state", Json_comp.from_actionstate st);
	("result", String res) ]) in
  print_string str; print_newline(); (* str;; *)
  Json_composer_io.execute_string str;
  Proc.compose st name deps acts res;;

let mypc,myinters,myst = mycompose myst "Pc" [mypa;mypb] [myact1] "Res";;
let mypf,myinters,myst = mycompose myst "Pf" [mypa;mypb;mypd] [myact1;myact3] "Rez";;

open Json_type.Browse;;

let myjsonstr = mycompose myst "Pc" [mypa;mypb] [myact1] "Res";;
let myjson = Json_io.json_of_string myjsonstr;;
let xtbl = make_table (objekt myjson) ;;
let xname = string (field xtbl "name");;
let xdeps = list Json_comp.to_process (field xtbl "components");;
let xacts = list Json_comp.to_action (field xtbl "actions");;
let xres = string (field xtbl "result");;
let xstate = Json_comp.to_actionstate (field xtbl "state");;

let myp,_,mys = Proc.compose xstate xname xdeps xacts xres;;
[Json_comp.composition_result xacts myp mys];;

;;

let op,arg = dest_comb xproc in
mk_icomb (op,Proc.try_proc_type arg);;



(* Isabelle Light *)
(* rule_tac *)

g `?a:num b:num P. |-- ('(NEG (A ** (B ** C)) <> a) ^ '(((A ** B) ** C) <> b)) P` ;;
g `?a:num b:num P. |-- ('(NEG (A ** (B ** D)) <> a) ^ '(((A ** B) ** C) <> b)) P` ;;
g `?a:num b:num P. |-- ('(NEG (A ** (B ** C)) <> a) ^ '((A ** D) <> b)) P` ;;
g `?a:num b:num P. |-- ('(NEG (A ** (B ** C)) <> a) ^ '((G ** D) <> b)) P` ;;
g `?a:num b:num P. |-- ('(NEG (A ** (B ** (C ** D))) <> a) ^ '((G ++ ((A ** B) ** (C ** D))) <> b)) P` ;;
g `?a:num b:num P. |-- ('(NEG (A ** (B ++ C)) <> a) ^ '((G ++ ((A ** B) ++ (A ** C))) <> b)) P` ;;
g `?a:num b:num P. |-- ('(NEG (A) <> a) ^ '((A ++ (B ** (C ++ D))) <> b)) P` ;;
g `?a:num b:num P. |-- ('(NEG (B ** C) <> a) ^ '((A ++ (B ** (C ++ D))) <> b)) P` ;;
g `?a:num b:num P. |-- ('(NEG (B ** D) <> a) ^ '((A ++ (B ** (C ++ D))) <> b)) P` ;;
g `?a:num b:num P. |-- ('(NEG (((B ++ C) ** A) ++ D) <> a) ^ '(((B ** A) ++ (C ** A) ++ D) <> b)) P` ;;
g `?a:num b:num P. |-- ('(NEG ((A ** B) ++ (A ** C)) <> a) ^ '((A ** (B ++ C)) <> b)) P` ;;
g `?a:num b:num P. |-- ('(NEG ((A ** ((B ** J) ++ E)) ++ ((A ++ (G ** H)) ** C)) <> a) ^ '(((A ** ((B ** J) ++ E)) ++ ((A ++ (G ** H)) ** C)) <> b)) P` ;;
g `?a:num b:num P. |-- ('(NEG (A ** B ** C) <> a) ^ '(((A ** B ** D) ++ (A ** B ** E) ++ (A ** B ** G) ++ (A ** B ** H) ++ (A ** B ** C)) <> b)) P` ;;
g `?a:num b:num P. |-- ('(NEG (A ** B ** C) <> a) ^ '(((A ** B ** D) ++ (A ** B ** E) ++ (A ** B ** C) ++ (A ** B ** H) ++ (A ** B ** G)) <> b)) P` ;;


e (REPEAT META_EXISTS_TAC);;
e (simp[NEG_CLAUSES]);;
e (REPEAT (Cllpi.TAC(Cllpi.llrule Cllpi.ll_par)));;
(get_ll_props o snd o top_goal)();;
e (Cllpi.TAC CLL_PROVE_ETAC);;
e (Cllpi.TAC Clltac.BUFFER_ETAC);;
b();;
instantiate (top_inst(p())) `P:NAgent` ;;






(* Debug VALID *)

let ((xmvs,xinst),xglr,xjust),_ = (erule_seqtac [`C`,`LinOne`] ll_cut (1,top_metas(p())) (top_realgoal()));;
let ((xmvs,xinst),xglr,xjust),_ = prove_by_seq "Pa" (1,top_metas(p())) (top_realgoal());;
let ((xmvs,xinst),xglr,xjust),_ = (XINPUT_TAC ~glfrees:(gl_frees (top_realgoal())) xprimary ((map rand o find_input_terms o concl) xthmr) xout xlprov xact.Action.lsel xact.Action.rarg) (!mystate) (top_realgoal());;

let xfake_thm (asl,w) =
  let asms = itlist (union o hyp o snd) asl [] in
  mk_fthm(asms,w);;

let xths = map xfake_thm xglr;;
let xjthm = stime "XTHM" (xjust null_inst) xths;;
let xasl',xw' = dest_thm(xjust null_inst xths);;
let xasl'',xw'' = inst_goal xinst (top_realgoal());;
aconv xw' xw'';;

xw',xw'';;

let xmaxasms = itlist (fun (_,th) -> union (insert (concl th) (hyp th))) xasl'' [];;
let xasms' = subtract xasl' [`_FALSITY_`];;
map (fun t -> exists (aconv t) xmaxasms) xasms';;


(* Debug Proc.compose/prove *)

let xasms = map (gen_ll_channels o Proc.get_cll) [mypa;mypb];;
let xlabels = map (fun x -> x.Proc.name) [mypa;mypb];;
let xnewvar = genvar `:bool` ;;
let xglvar = mk_undered_var [xnewvar] xnewvar;;
let xgltm = mk_exists (xglvar,xglvar);;
let xgl = itlist (fun x y -> mk_imp (x,y)) xasms xgltm;;
let xgs = [mk_goalstate([],xgl),myst];;
let xinittac = Actionstate.ASTAC (MAP_EVERY (fun s -> (DISCH_THEN (META_SPEC_ALL_LABEL_TAC s))) xlabels THEN
				  REPEAT META_EXISTS_TAC);;
let xgs' = apply_etac xinittac xgs;;
let xxgst,xxst = hd xgs';;
let xxgst' = xxgst,Actionstate.reset xxst;;
let (xxnewgst,xxnewst) as xxres = eby (EVALID (Action.apply myact1)) xxgst';;
let xxnewproc = (Proc.from_cll myact1.Action.res true [myact1] o concl o assoc myact1.Action.res o fst o hd o snd3) xxnewgst;;
let xgs'' = xxres::xgs';;	
let xprocs = [xxnewproc];;
let xstates = (map snd o butlast o butlast) xgs'';;
let xmetas =  (fst o fst3 o fst o hd) xgs'';;
let xxtac =  ETAC (USE_THEN "R1" (UNIFY_ACCEPT_TAC [xglvar] o PURE_REWRITE_RULE[MUNION_AC]));;
let xresgs = apply_etac xxtac xgs'' ;;
let xthm,xstate' = get_ethm xresgs;;
let xinst = (snd o fst3 o fst o hd) xresgs;;
xinst,xthm,zip xstates xprocs,xstate';;
((instantiate xinst) o snd o strip_exists o concl o UNDISCH_ALL) xthm;;
			      

let xgl = ((hd o snd3 o fst) xxgst');;
let xl = assoc "Pa" (fst xgl);;
let xr = assoc "Pb" (fst xgl);;


g xgl;;
eseq (SEQTAC (MAP_EVERY (fun s -> (DISCH_THEN (META_SPEC_ALL_LABEL_TAC s))) xlabels THEN
			REPEAT META_EXISTS_TAC));;
eseq (drule_seqtac ~lbl:"Pb" ~reslbl:"R" [`C:LinProp`,`A`; `G:(LinTerm)multiset`,`' (NEG X <> cPa_X_1)`] Cllpi.ll_cut);;
eseq (prove_by_seq "Pa");;

eseq (ETHENL (drule_seqtac ~lbl:"P2" ~reslbl:"P2" 
			   [(`A:LinProp`,`W`);(`B:LinProp`,`A ** C`);
			    (`D:(LinTerm)multiset`,`' (NEG A <> cP1_A_2)^
' (NEG C <> cP1_C_6)`)] 
			   Cllpi.ll_times)
	      [ Clltac.PARBUF_ETAC ; ALL_ETAC ]);;
eseq (ETHENL (drule_seqtac ~lbl:"P1" ~reslbl:"P1" 
			   [(`A:LinProp`,`Z`);(`B:LinProp`,`B`);
			    (`D:(LinTerm)multiset`,`' (NEG B <> cP2_B_2)`)] 
			   Cllpi.ll_times)
	     [ Clltac.PARBUF_ETAC ; ALL_ETAC ]);;

eseq (drule_seqtac ~lbl:"P1" ~reslbl:"Co"
		  [(`A:LinProp`,`X`);(`a`,`cP1_X_1`);
		   (`B:LinProp`,`Z ** B`);
		   (`C:LinProp`,`Y`);(`c`,`cP2_Y_1`);
		   (`D:LinProp`,`W ** A ** C`)]
		  Clltac.Rules.ll_with_outputs);;
eseq (prove_by_seq "P2");;

e (RULE_ASSUM_TAC NORMALIZE_MULTISET);;
e (REPEAT GEN_TAC THEN CONV_TAC NORM_MSET_CONV);;

let xth = assoc "P2" (fst(top_realgoal()));;
let xlc = subtract (union [] (intersect (frees (concl xth)) (freesl(hyp xth)))) (top_metas(p())) ;;



let rec acker m n =
  if m=0 then (n+1) else
  if n=0 then (acker (m-1) 1) else
    (acker (m-1) (acker m (n-1)));;

let pikos res =
  print_string ("*** Composing: " ^ res) ; print_newline () ; reset_time() ;
  let _ = acker 3 10 in
  print_string ("*** Goal setup complete." ^ " (" ^ (string_of_float (rget_time())) ^ ")") ; print_newline ();
  let x = acker 3 11 in
  print_string ("*** Theorem reconstruction complete." ^ " (" ^ (string_of_float (rget_time())) ^ ")")  ; print_newline ();
  x;;


let jstring =  "{\"name\":\"Composition2\",\"actions\":[{\"act\":\"JOIN\",\"larg\":\"SetAssignmentResponsible\",\"lsel\":\"\",\"rarg\":\"CheckOutcome\",\"rsel\":\"(NEG HealthcareActor)\",\"res\":\"_Step1\"},{\"act\":\"JOIN\",\"larg\":\"ProvideService\",\"lsel\":\"lr\",\"rarg\":\"_Step1\",\"rsel\":\"(NEG CompletedHealthcareService)\",\"res\":\"_Step4\"},{\"act\":\"JOIN\",\"larg\":\"Copy_OpenContract_2\",\"lsel\":\"r\",\"rarg\":\"_Step4\",\"rsel\":\"(NEG OpenContract)\",\"res\":\"_Step5\"},{\"act\":\"JOIN\",\"larg\":\"AwardContract\",\"lsel\":\"\",\"rarg\":\"_Step5\",\"rsel\":\"(NEG OpenContract)\",\"res\":\"_Step6\"},{\"act\":\"JOIN\",\"larg\":\"Copy_ServiceProvider_2\",\"lsel\":\"lr\",\"rarg\":\"_Step6\",\"rsel\":\"(NEG ServiceProvider)\",\"res\":\"_Step7\"},{\"act\":\"JOIN\",\"larg\":\"DecideCollaboration\",\"lsel\":\"lrr\",\"rarg\":\"_Step7\",\"rsel\":\"(NEG ServiceProvider)\",\"res\":\"_Step9\"},{\"act\":\"JOIN\",\"larg\":\"RequestAssignment\",\"lsel\":\"lr\",\"rarg\":\"_Step9\",\"rsel\":\"(NEG Assignment)\",\"res\":\"Composition2\"}],\"components\":[{\"name\":\"DecideCollaboration\",\"inputs\":[{\"channel\":\"cDecideCollaboration_RequestedContract_1\",\"cll\":{\"type\":\"var\",\"name\":\"RequestedContract\",\"args\":[]}}],\"output\":{\"channel\":\"oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB_\",\"cll\":{\"type\":\"plus\",\"name\":\"\",\"args\":[{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"var\",\"name\":\"AcceptedContract\",\"args\":[]},{\"type\":\"var\",\"name\":\"ServiceProvider\",\"args\":[]}]},{\"type\":\"var\",\"name\":\"RejectedContract\",\"args\":[]}]}},\"proc\":\"DecideCollaboration\\n(cDecideCollaboration_RequestedContract_1,\\n oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB_) \\u003d\\nComp\\n(In cDecideCollaboration_RequestedContract_1\\n [cDecideCollaboration_RequestedContract_1__a_RequestedContract]\\nZero)\\n(Res\\n [oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__lB_AcceptedContract_x_ServiceProvider_rB; oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__RejectedContract]\\n(In\\n oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB_\\n [oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB___opt_lB_AcceptedContract_x_ServiceProvider_rB; oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB___opt_RejectedContract]\\n(Plus\\n (Out\\n  oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB___opt_lB_AcceptedContract_x_ServiceProvider_rB\\n  [oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__lB_AcceptedContract_x_ServiceProvider_rB]\\n (Res\\n  [oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__lAcceptedContract; oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__lServiceProvider]\\n (Out\\n  oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__lB_AcceptedContract_x_ServiceProvider_rB\\n  [oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__lAcceptedContract; oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__lServiceProvider]\\n (Comp\\n  (Res\\n   [oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__ll_a_AcceptedContract]\\n  (Out\\n   oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__lAcceptedContract\\n   [oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__ll_a_AcceptedContract]\\n  Zero))\\n (Res\\n  [oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__lr_a_ServiceProvider]\\n (Out\\n  oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__lServiceProvider\\n  [oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__lr_a_ServiceProvider]\\n Zero))))))\\n(Out\\n oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB___opt_RejectedContract\\n [oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__RejectedContract]\\n(Res\\n [oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__r_a_RejectedContract]\\n(Out\\n oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__RejectedContract\\n [oDecideCollaboration_lB_lB_AcceptedContract_x_ServiceProvider_rB_Plus_RejectedContract_rB__r_a_RejectedContract]\\nZero))))))\",\"actions\":[],\"copier\":false,\"intermediate\":false,\"checked\":true,\"valid\":true},{\"name\":\"CheckOutcome\",\"inputs\":[{\"channel\":\"cCheckOutcome_OpenContract_1\",\"cll\":{\"type\":\"var\",\"name\":\"OpenContract\",\"args\":[]}},{\"channel\":\"cCheckOutcome_CompletedHealthcareService_2\",\"cll\":{\"type\":\"var\",\"name\":\"CompletedHealthcareService\",\"args\":[]}},{\"channel\":\"cCheckOutcome_HealthcareActor_3\",\"cll\":{\"type\":\"var\",\"name\":\"HealthcareActor\",\"args\":[]}}],\"output\":{\"channel\":\"oCheckOutcome_lB_CheckedHealthcareService_x_ClosedContract_rB_\",\"cll\":{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"var\",\"name\":\"CheckedHealthcareService\",\"args\":[]},{\"type\":\"var\",\"name\":\"ClosedContract\",\"args\":[]}]}},\"proc\":\"CheckOutcome\\n(cCheckOutcome_OpenContract_1,\\n cCheckOutcome_CompletedHealthcareService_2,\\n cCheckOutcome_HealthcareActor_3,\\n oCheckOutcome_lB_CheckedHealthcareService_x_ClosedContract_rB_) \\u003d\\nComp\\n(In cCheckOutcome_OpenContract_1\\n [cCheckOutcome_OpenContract_1__a_OpenContract]\\nZero)\\n(Comp\\n (In cCheckOutcome_CompletedHealthcareService_2\\n  [cCheckOutcome_CompletedHealthcareService_2__a_CompletedHealthcareService]\\n Zero)\\n(Comp\\n (In cCheckOutcome_HealthcareActor_3\\n  [cCheckOutcome_HealthcareActor_3__a_HealthcareActor]\\n Zero)\\n(Res\\n [oCheckOutcome_lB_CheckedHealthcareService_x_ClosedContract_rB__CheckedHealthcareService; oCheckOutcome_lB_CheckedHealthcareService_x_ClosedContract_rB__ClosedContract]\\n(Out oCheckOutcome_lB_CheckedHealthcareService_x_ClosedContract_rB_\\n [oCheckOutcome_lB_CheckedHealthcareService_x_ClosedContract_rB__CheckedHealthcareService; oCheckOutcome_lB_CheckedHealthcareService_x_ClosedContract_rB__ClosedContract]\\n(Comp\\n (Res\\n  [oCheckOutcome_lB_CheckedHealthcareService_x_ClosedContract_rB__l_a_CheckedHealthcareService]\\n (Out\\n  oCheckOutcome_lB_CheckedHealthcareService_x_ClosedContract_rB__CheckedHealthcareService\\n  [oCheckOutcome_lB_CheckedHealthcareService_x_ClosedContract_rB__l_a_CheckedHealthcareService]\\n Zero))\\n(Res\\n [oCheckOutcome_lB_CheckedHealthcareService_x_ClosedContract_rB__r_a_ClosedContract]\\n(Out\\n oCheckOutcome_lB_CheckedHealthcareService_x_ClosedContract_rB__ClosedContract\\n [oCheckOutcome_lB_CheckedHealthcareService_x_ClosedContract_rB__r_a_ClosedContract]\\nZero)))))))\",\"actions\":[],\"copier\":false,\"intermediate\":false,\"checked\":true,\"valid\":true},{\"name\":\"ProvideService\",\"inputs\":[{\"channel\":\"cProvideService_OpenContract_1\",\"cll\":{\"type\":\"var\",\"name\":\"OpenContract\",\"args\":[]}},{\"channel\":\"cProvideService_PendingHealthcareService_2\",\"cll\":{\"type\":\"var\",\"name\":\"PendingHealthcareService\",\"args\":[]}}],\"output\":{\"channel\":\"oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB_\",\"cll\":{\"type\":\"plus\",\"name\":\"\",\"args\":[{\"type\":\"var\",\"name\":\"CompletedHealthcareService\",\"args\":[]},{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"var\",\"name\":\"Obstacle\",\"args\":[]},{\"type\":\"var\",\"name\":\"PendingHealthcareService\",\"args\":[]}]}]}},\"proc\":\"ProvideService\\n(cProvideService_OpenContract_1,\\n cProvideService_PendingHealthcareService_2,\\n oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB_) \\u003d\\nComp\\n(In cProvideService_OpenContract_1\\n [cProvideService_OpenContract_1__a_OpenContract]\\nZero)\\n(Comp\\n (In cProvideService_PendingHealthcareService_2\\n  [cProvideService_PendingHealthcareService_2__a_PendingHealthcareService]\\n Zero)\\n(Res\\n [oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__CompletedHealthcareService; oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__lB_Obstacle_x_PendingHealthcareService_rB]\\n(In\\n oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB_\\n [oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB___opt_CompletedHealthcareService; oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB___opt_lB_Obstacle_x_PendingHealthcareService_rB]\\n(Plus\\n (Out\\n  oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB___opt_CompletedHealthcareService\\n  [oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__CompletedHealthcareService]\\n (Res\\n  [oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__l_a_CompletedHealthcareService]\\n (Out\\n  oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__CompletedHealthcareService\\n  [oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__l_a_CompletedHealthcareService]\\n Zero)))\\n(Out\\n oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB___opt_lB_Obstacle_x_PendingHealthcareService_rB\\n [oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__lB_Obstacle_x_PendingHealthcareService_rB]\\n(Res\\n [oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__rObstacle; oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__rPendingHealthcareService]\\n(Out\\n oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__lB_Obstacle_x_PendingHealthcareService_rB\\n [oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__rObstacle; oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__rPendingHealthcareService]\\n(Comp\\n (Res\\n  [oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__rl_a_Obstacle]\\n (Out\\n  oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__rObstacle\\n  [oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__rl_a_Obstacle]\\n Zero))\\n(Res\\n [oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__rr_a_PendingHealthcareService]\\n(Out\\n oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__rPendingHealthcareService\\n [oProvideService_lB_CompletedHealthcareService_Plus_lB_Obstacle_x_PendingHealthcareService_rB_rB__rr_a_PendingHealthcareService]\\nZero))))))))))\",\"actions\":[],\"copier\":false,\"intermediate\":false,\"checked\":true,\"valid\":true},{\"name\":\"RequestAssignment\",\"inputs\":[{\"channel\":\"cRequestAssignment_Patient_1\",\"cll\":{\"type\":\"var\",\"name\":\"Patient\",\"args\":[]}},{\"channel\":\"cRequestAssignment_HealthcareActor_2\",\"cll\":{\"type\":\"var\",\"name\":\"HealthcareActor\",\"args\":[]}},{\"channel\":\"cRequestAssignment_HealthcareService_3\",\"cll\":{\"type\":\"var\",\"name\":\"HealthcareService\",\"args\":[]}}],\"output\":{\"channel\":\"oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB_\",\"cll\":{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"var\",\"name\":\"Assignment\",\"args\":[]},{\"type\":\"var\",\"name\":\"RequestedContract\",\"args\":[]},{\"type\":\"var\",\"name\":\"ServiceRequester\",\"args\":[]},{\"type\":\"var\",\"name\":\"PendingHealthcareService\",\"args\":[]}]}},\"proc\":\"RequestAssignment\\n(cRequestAssignment_Patient_1,\\n cRequestAssignment_HealthcareActor_2,\\n cRequestAssignment_HealthcareService_3,\\n oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB_) \\u003d\\nComp\\n(In cRequestAssignment_Patient_1 [cRequestAssignment_Patient_1__a_Patient]\\nZero)\\n(Comp\\n (In cRequestAssignment_HealthcareActor_2\\n  [cRequestAssignment_HealthcareActor_2__a_HealthcareActor]\\n Zero)\\n(Comp\\n (In cRequestAssignment_HealthcareService_3\\n  [cRequestAssignment_HealthcareService_3__a_HealthcareService]\\n Zero)\\n(Res\\n [oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__Assignment; oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB]\\n(Out\\n oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB_\\n [oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__Assignment; oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB]\\n(Comp\\n (Res\\n  [oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__l_a_Assignment]\\n (Out\\n  oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__Assignment\\n  [oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__l_a_Assignment]\\n Zero))\\n(Res\\n [oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rRequestedContract; oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rlB_ServiceRequester_x_PendingHealthcareService_rB]\\n(Out\\n oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB\\n [oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rRequestedContract; oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rlB_ServiceRequester_x_PendingHealthcareService_rB]\\n(Comp\\n (Res\\n  [oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rl_a_RequestedContract]\\n (Out\\n  oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rRequestedContract\\n  [oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rl_a_RequestedContract]\\n Zero))\\n(Res\\n [oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rrServiceRequester; oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rrPendingHealthcareService]\\n(Out\\n oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rlB_ServiceRequester_x_PendingHealthcareService_rB\\n [oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rrServiceRequester; oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rrPendingHealthcareService]\\n(Comp\\n (Res\\n  [oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rrl_a_ServiceRequester]\\n (Out\\n  oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rrServiceRequester\\n  [oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rrl_a_ServiceRequester]\\n Zero))\\n(Res\\n [oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rrr_a_PendingHealthcareService]\\n(Out\\n oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rrPendingHealthcareService\\n [oRequestAssignment_lB_Assignment_x_lB_RequestedContract_x_lB_ServiceRequester_x_PendingHealthcareService_rB_rB_rB__rrr_a_PendingHealthcareService]\\nZero)))))))))))))\",\"actions\":[],\"copier\":false,\"intermediate\":false,\"checked\":true,\"valid\":true},{\"name\":\"Copy_ServiceProvider_2\",\"inputs\":[{\"channel\":\"cCopy_ServiceProvider_2_ServiceProvider_1\",\"cll\":{\"type\":\"var\",\"name\":\"ServiceProvider\",\"args\":[]}}],\"output\":{\"channel\":\"oCopy_ServiceProvider_2_lB_ServiceProvider_x_ServiceProvider_rB_\",\"cll\":{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"var\",\"name\":\"ServiceProvider\",\"args\":[]},{\"type\":\"var\",\"name\":\"ServiceProvider\",\"args\":[]}]}},\"proc\":\"Copy_ServiceProvider_2\\n(cCopy_ServiceProvider_2_ServiceProvider_1,\\n oCopy_ServiceProvider_2_lB_ServiceProvider_x_ServiceProvider_rB_) \\u003d\\nComp\\n(In cCopy_ServiceProvider_2_ServiceProvider_1\\n [cCopy_ServiceProvider_2_ServiceProvider_1__a_ServiceProvider]\\nZero)\\n(Res\\n [oCopy_ServiceProvider_2_lB_ServiceProvider_x_ServiceProvider_rB__ServiceProvider; oCopy_ServiceProvider_2_lB_ServiceProvider_x_ServiceProvider_rB__ServiceProvider]\\n(Out oCopy_ServiceProvider_2_lB_ServiceProvider_x_ServiceProvider_rB_\\n [oCopy_ServiceProvider_2_lB_ServiceProvider_x_ServiceProvider_rB__ServiceProvider; oCopy_ServiceProvider_2_lB_ServiceProvider_x_ServiceProvider_rB__ServiceProvider]\\n(Comp\\n (Res\\n  [oCopy_ServiceProvider_2_lB_ServiceProvider_x_ServiceProvider_rB__l_a_ServiceProvider]\\n (Out\\n  oCopy_ServiceProvider_2_lB_ServiceProvider_x_ServiceProvider_rB__ServiceProvider\\n  [oCopy_ServiceProvider_2_lB_ServiceProvider_x_ServiceProvider_rB__l_a_ServiceProvider]\\n Zero))\\n(Res\\n [oCopy_ServiceProvider_2_lB_ServiceProvider_x_ServiceProvider_rB__r_a_ServiceProvider]\\n(Out\\n oCopy_ServiceProvider_2_lB_ServiceProvider_x_ServiceProvider_rB__ServiceProvider\\n [oCopy_ServiceProvider_2_lB_ServiceProvider_x_ServiceProvider_rB__r_a_ServiceProvider]\\nZero)))))\",\"actions\":[],\"copier\":true,\"intermediate\":false,\"checked\":true,\"valid\":true},{\"name\":\"AwardContract\",\"inputs\":[{\"channel\":\"cAwardContract_AcceptedContract_1\",\"cll\":{\"type\":\"var\",\"name\":\"AcceptedContract\",\"args\":[]}},{\"channel\":\"cAwardContract_ServiceProvider_2\",\"cll\":{\"type\":\"var\",\"name\":\"ServiceProvider\",\"args\":[]}}],\"output\":{\"channel\":\"oAwardContract_OpenContract_\",\"cll\":{\"type\":\"var\",\"name\":\"OpenContract\",\"args\":[]}},\"proc\":\"AwardContract\\n(cAwardContract_AcceptedContract_1,\\n cAwardContract_ServiceProvider_2,\\n oAwardContract_OpenContract_) \\u003d\\nComp\\n(In cAwardContract_AcceptedContract_1\\n [cAwardContract_AcceptedContract_1__a_AcceptedContract]\\nZero)\\n(Comp\\n (In cAwardContract_ServiceProvider_2\\n  [cAwardContract_ServiceProvider_2__a_ServiceProvider]\\n Zero)\\n(Res [oAwardContract_OpenContract___a_OpenContract]\\n(Out oAwardContract_OpenContract_\\n [oAwardContract_OpenContract___a_OpenContract]\\nZero)))\",\"actions\":[],\"copier\":false,\"intermediate\":false,\"checked\":true,\"valid\":true},{\"name\":\"Copy_OpenContract_2\",\"inputs\":[{\"channel\":\"cCopy_OpenContract_2_OpenContract_1\",\"cll\":{\"type\":\"var\",\"name\":\"OpenContract\",\"args\":[]}}],\"output\":{\"channel\":\"oCopy_OpenContract_2_lB_OpenContract_x_OpenContract_rB_\",\"cll\":{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"var\",\"name\":\"OpenContract\",\"args\":[]},{\"type\":\"var\",\"name\":\"OpenContract\",\"args\":[]}]}},\"proc\":\"Copy_OpenContract_2\\n(cCopy_OpenContract_2_OpenContract_1,\\n oCopy_OpenContract_2_lB_OpenContract_x_OpenContract_rB_) \\u003d\\nComp\\n(In cCopy_OpenContract_2_OpenContract_1\\n [cCopy_OpenContract_2_OpenContract_1__a_OpenContract]\\nZero)\\n(Res\\n [oCopy_OpenContract_2_lB_OpenContract_x_OpenContract_rB__OpenContract; oCopy_OpenContract_2_lB_OpenContract_x_OpenContract_rB__OpenContract]\\n(Out oCopy_OpenContract_2_lB_OpenContract_x_OpenContract_rB_\\n [oCopy_OpenContract_2_lB_OpenContract_x_OpenContract_rB__OpenContract; oCopy_OpenContract_2_lB_OpenContract_x_OpenContract_rB__OpenContract]\\n(Comp\\n (Res\\n  [oCopy_OpenContract_2_lB_OpenContract_x_OpenContract_rB__l_a_OpenContract]\\n (Out oCopy_OpenContract_2_lB_OpenContract_x_OpenContract_rB__OpenContract\\n  [oCopy_OpenContract_2_lB_OpenContract_x_OpenContract_rB__l_a_OpenContract]\\n Zero))\\n(Res\\n [oCopy_OpenContract_2_lB_OpenContract_x_OpenContract_rB__r_a_OpenContract]\\n(Out oCopy_OpenContract_2_lB_OpenContract_x_OpenContract_rB__OpenContract\\n [oCopy_OpenContract_2_lB_OpenContract_x_OpenContract_rB__r_a_OpenContract]\\nZero)))))\",\"actions\":[],\"copier\":true,\"intermediate\":false,\"checked\":true,\"valid\":true},{\"name\":\"SetAssignmentResponsible\",\"inputs\":[{\"channel\":\"cSetAssignmentResponsible_Assignment_1\",\"cll\":{\"type\":\"var\",\"name\":\"Assignment\",\"args\":[]}},{\"channel\":\"cSetAssignmentResponsible_ServiceProvider_2\",\"cll\":{\"type\":\"var\",\"name\":\"ServiceProvider\",\"args\":[]}}],\"output\":{\"channel\":\"oSetAssignmentResponsible_HealthcareActor_\",\"cll\":{\"type\":\"var\",\"name\":\"HealthcareActor\",\"args\":[]}},\"proc\":\"SetAssignmentResponsible\\n(cSetAssignmentResponsible_Assignment_1,\\n cSetAssignmentResponsible_ServiceProvider_2,\\n oSetAssignmentResponsible_HealthcareActor_) \\u003d\\nComp\\n(In cSetAssignmentResponsible_Assignment_1\\n [cSetAssignmentResponsible_Assignment_1__a_Assignment]\\nZero)\\n(Comp\\n (In cSetAssignmentResponsible_ServiceProvider_2\\n  [cSetAssignmentResponsible_ServiceProvider_2__a_ServiceProvider]\\n Zero)\\n(Res [oSetAssignmentResponsible_HealthcareActor___a_HealthcareActor]\\n(Out oSetAssignmentResponsible_HealthcareActor_\\n [oSetAssignmentResponsible_HealthcareActor___a_HealthcareActor]\\nZero)))\",\"actions\":[],\"copier\":false,\"intermediate\":false,\"checked\":true,\"valid\":true}],\"state\":{\"ctr\":379,\"buffered\":[],\"joined\":[],\"iprov\":[],\"prov\":[{\"name\":\"DecideCollaboration\",\"prov\":{\"type\":\"plus\",\"name\":\"\",\"args\":[{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"source\",\"name\":\"DecideCollaboration\",\"args\":[]},{\"type\":\"source\",\"name\":\"DecideCollaboration\",\"args\":[]}]},{\"type\":\"source\",\"name\":\"DecideCollaboration\",\"args\":[]}]}},{\"name\":\"CheckOutcome\",\"prov\":{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"source\",\"name\":\"CheckOutcome\",\"args\":[]},{\"type\":\"source\",\"name\":\"CheckOutcome\",\"args\":[]}]}},{\"name\":\"ProvideService\",\"prov\":{\"type\":\"plus\",\"name\":\"\",\"args\":[{\"type\":\"source\",\"name\":\"ProvideService\",\"args\":[]},{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"source\",\"name\":\"ProvideService\",\"args\":[]},{\"type\":\"source\",\"name\":\"ProvideService\",\"args\":[]}]}]}},{\"name\":\"RequestAssignment\",\"prov\":{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"source\",\"name\":\"RequestAssignment\",\"args\":[]},{\"type\":\"source\",\"name\":\"RequestAssignment\",\"args\":[]},{\"type\":\"source\",\"name\":\"RequestAssignment\",\"args\":[]},{\"type\":\"source\",\"name\":\"RequestAssignment\",\"args\":[]}]}},{\"name\":\"Copy_ServiceProvider_2\",\"prov\":{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"source\",\"name\":\"Copy_ServiceProvider_2\",\"args\":[]},{\"type\":\"source\",\"name\":\"Copy_ServiceProvider_2\",\"args\":[]}]}},{\"name\":\"AwardContract\",\"prov\":{\"type\":\"source\",\"name\":\"AwardContract\",\"args\":[]}},{\"name\":\"Copy_OpenContract_2\",\"prov\":{\"type\":\"times\",\"name\":\"\",\"args\":[{\"type\":\"source\",\"name\":\"Copy_OpenContract_2\",\"args\":[]},{\"type\":\"source\",\"name\":\"Copy_OpenContract_2\",\"args\":[]}]}},{\"name\":\"SetAssignmentResponsible\",\"prov\":{\"type\":\"source\",\"name\":\"SetAssignmentResponsible\",\"args\":[]}}],\"chanmap\":[]},\"command\":\"compose\",\"succeeded\":false}";;

time (ignore o Json_composer_io.execute) jstring;;
(*
40.832
41.012

33.06
33.124
33.064

13.504
13.384
13.396

6.3
6.47
7

2.56
*)

needs "services/dev/make.ml";;
let mystate = ref (Actionstate.create 0);;
let xsetstate st = mystate:= st;;
let xtac (tac:Actionstate.t etactic) = e (ETAC_TAC' xsetstate (!mystate) tac);;


open Json_type.Browse;;
let xj = Json_io.json_of_string jstring;;
let xtbl = make_table (objekt xj);;
let xcommand = string (field xtbl "command");;

let xname = string (field xtbl "name")
and xdeps = list Json_comp.to_process (field xtbl "components")
and xacts = list Json_comp.to_action (field xtbl "actions")
and xstate = Json_comp.to_actionstate (field xtbl "state");;
(* Process.compose state name deps acts  *)
(* prove state deps acts name *)

let xasms = map (gen_ll_channels o Proc.get_cll) xdeps;;
let xlabels = map (fun x -> x.Proc.name) xdeps;;
let xnewvar = genvar `:bool` ;;
let xglvar = mk_undered_var [xnewvar] xnewvar;;
let xgltm = mk_exists (xglvar,xglvar);;
let xgl = itlist (fun x y -> mk_imp (x,y)) xasms xgltm;;

g xgl;;
mystate := xstate;;
xtac (Actionstate.ASTAC (MAP_EVERY (fun s -> (DISCH_THEN (META_SPEC_ALL_LABEL_TAC s))) xlabels THEN
				  REPEAT META_EXISTS_TAC));;
let xaid = -1;;

let xaid = xaid + 1;;
mystate := Actionstate.reset (!mystate);;
if (xaid >= 6)
then (print_string "\n\n\n\n*** STOP *** STOP  *** STOP  *** STOP *** STOP ***\n\n\n\n"; print_newline())
else ignore(e (ETAC_TAC' xsetstate (!mystate) (Action.apply (el xaid xacts))));;


let xact = el 6 xacts;;
let xatac = Action.get xact.Action.act
and xthml = try ( assoc xact.Action.larg ((fst o top_realgoal)()) )
  with Failure _ -> failwith ("APPLY ACTION '"^xact.Action.act^"': No such process '"^xact.Action.larg^"'")
and xthmr = try ( assoc xact.Action.rarg ((fst o top_realgoal)()) )
  with Failure _ -> failwith ("APPLY ACTION '"^xact.Action.act^"': No such process '"^xact.Action.rarg^"'");; 


let xout = find_output (concl xthml)
and xinlist = (find_input_terms o concl) xthmr
and xinputs = (list_mk_munion o (map mk_msing) o find_input_terms o concl) xthml;;
let xprimary = try ( parse_term xact.Action.rsel )
  with Failure _ -> failwith ("JOIN_TAC: Failed to parse term `"^xact.Action.rsel^"`");;
let xprimary = if (is_llneg xprimary) then xprimary else mk_llneg xprimary;;
let xlprov = try ( assoc xact.Action.larg (!mystate).Actionstate.prov ) with Failure _ -> (
  warn true ("JOIN_TAC: Failed to find provenance for output of: " ^ xact.Action.larg);
  prov_of_tm xact.Action.larg xout)
and xrprov = try ( assoc xact.Action.rarg (!mystate).Actionstate.prov ) with Failure _ -> (
  warn true ("JOIN_TAC: Failed to find provenance for output of: " ^ xact.Action.rarg);
  prov_of_tm xact.Action.rarg (find_output (concl xthmr)));;

  stime "ACT6" e (ETAC_TAC' xsetstate (!mystate) (Action.apply (el xaid xacts)));;

e (COPY_TAC (xact.Action.rarg,"_right_"));;
(*
INPUT_TAC primary ((map rand o find_input_terms o concl) thmr) out lprov act.Action.lsel act.Action.rarg;
primary inchans target prov priority lbl -> INPUT_TAC' (Some primary) inchans (Some (explode priority)) true target prov lbl
*)
reset_time();e (ETAC_TAC (!mystate) (Clltac.INPUT_TAC (gl_frees (top_realgoal())) xprimary ((map rand o find_input_terms o concl) xthmr) xout xlprov xact.Action.lsel xact.Action.rarg));print_string ("*** Done:" ^ " (" ^ (string_of_float (rget_time())) ^ ")")  ; print_newline ();;
(* latest: staff: 0.44 - without assums: 0.38*)
e (KEEP_ASSUMS_TAC [xact.Action.larg;xact.Action.rarg]);;

let xrest = filter (fun (s,_) -> not (mem s [xact.Action.larg;xact.Action.rarg])) ((fst o top_realgoal)());;
e (REMOVE_ASSUMS_TAC (map fst xrest));;
time e (MAP_EVERY (fun s,th -> LABEL_TAC s th) xrest);;
let SELECT_ASSUM_ETAC l tac st (asl,_ as gl) =
  let rest = filter (fun s,_ -> not (mem s l)) asl in
    ETHEN (ETAC (REMOVE_ASSUMS_TAC (map fst rest))) (ETHEN tac (ETAC (MAP_EVERY (fun s,th -> LABEL_TAC s th) rest))) st gl;;
b();;
reset_time();e (ETAC_TAC (!mystate) (SELECT_ASSUM_ETAC [xact.Action.larg;xact.Action.rarg] (Clltac.INPUT_TAC (gl_frees (top_realgoal())) xprimary ((map rand o find_input_terms o concl) xthmr) xout xlprov xact.Action.lsel xact.Action.rarg)));print_string ("*** Done:" ^ " (" ^ (string_of_float (rget_time())) ^ ")")  ; print_newline ();;
(* kane: 7.304 - no assums: 3.252 *)

stime "GLFREES" (ignore o gl_frees) (top_realgoal());;


ignore(b());;
ignore(e (ETAC_TAC' xsetstate (!mystate) (TIME_ETAC "DRULE" (Actionstate.CLL_TAC 
				   (drule_seqtac ~lbl:"_Step9" ~reslbl:"_Step9"
						 [`A:LinProp`,`PendingHealthcareService:LinProp`; (* rand of NEG *)
			  `a:num`,`cProvideService_PendingHealthcareService_2:num`;
			  `B:LinProp`,`ServiceRequester:LinProp`;
			  `b:num`,`cProvideService_PendingHealthcareService_2:num`] (* TODO This needs testing? *)
						 Clltac.Rules.ll_filter_input)))));;
(* 0.0287 *)
e (ETAC_TAC (!mystate) (TIME_ETAC "Prove" Clltac.CLL_PROVE_TAC));;
e (ETAC_TAC (!mystate) (TIME_ETAC "Prove" XCLL_PROVE_TAC));;
   (*  FAILED: 0.0283 *)

   let rec (XXCLL_PROVE_INPUT_ETAC:term list->seqtactic) =
      fun glf s gl ->
      let rec withProof s ((_,tm) as gl) =
	let wtm = find_ll_prop (is_binary "LinWith") tm in
	let comb,args = strip_comb wtm in
	let lh,rh = hd args,(hd o tl) args in
	ETHEN
	(TIME_ETAC "WITH" (rule_seqtac ~glfrees:glf [(`A:LinProp`,lh);
		      (`B:LinProp`,rh)] Cllpi.ll_with))
	(XXCLL_PROVE_INPUT_ETAC glf) s gl in
      EEVERY [
      ETAC (PURE_REWRITE_TAC[NEG_CLAUSES]) ;
      EREPEAT (TIME_ETAC "PAR" (ruleseq ~glfrees:glf Cllpi.ll_par)) ;
      EREPEAT withProof ] s gl;;
	
    let rec (XXCLL_PROVE_OUTPUT_ETAC:term list->seqtactic) =
      fun glf s ((_,tm) as gl) ->
      try (
      let out = find_output tm in
      if (is_var out) then (
        TIME_ETAC "ID" (Cllpi.llid out) s gl
      )
      else let comb,args = strip_comb out in
	   if (comb = `LinTimes`) then
	   let lh,rh = hd args,(hd o tl) args in
	   if (is_var lh) then
	   let nlh = mk_llneg lh in
           let nltm = mk_msing ( find_ll_term ((=) nlh) tm ) in
	   ETHEN
            (TIME_ETAC "TIMESL" (rule_seqtac ~glfrees:glf [(`A:LinProp`,lh);
			  (`B:LinProp`,rh);
			  (`G:(LinTerm)multiset`,nltm)] Cllpi.ll_times))
	    (XXCLL_PROVE_OUTPUT_ETAC glf) s gl
	   else if (is_var rh) then
	   let nrh = mk_llneg rh in
           let nrtm = mk_msing ( find_ll_term ((=) nrh) tm ) in
	   (ETHEN
	    (ETHENL
	     (TIME_ETAC "TIMESR" (rule_seqtac ~glfrees:glf [(`A:LinProp`,lh);
			   (`B:LinProp`,rh);
			   (`D:(LinTerm)multiset`,nrtm)] Cllpi.ll_times))
	     [ ALL_ETAC ; XXCLL_PROVE_OUTPUT_ETAC glf ])
	    (XXCLL_PROVE_OUTPUT_ETAC glf)) s gl
	   else
	   let iterms = find_input_terms tm in
	   let rec timesProof index s gl =
	     match nextSubsetIndex(index) with
	       | None -> failwith "XXCLL_PROVE_OUTPUT_ETAC"
	       | Some(i) ->
		   let subset = getIndexedSubset i iterms in
		   let dcontext = list_mk_munion (map mk_msing subset) in
		   let tac = TIME_ETAC "TIMES" (rule_seqtac ~glfrees:glf [(`A:LinProp`,lh);
					  (`B:LinProp`,rh);
					  (`D:(LinTerm)multiset`,dcontext)] Cllpi.ll_times) in
		   let select = Clltac.cllCombSelect out in
		   if (select <= 0)
		   then 		  
		   (EORELSE (ETHEN tac (XXCLL_PROVE_OUTPUT_ETAC glf)) (timesProof i)) s gl
		   else
		   (EORELSE (ETHEN 
			     (ETHENL tac [ ALL_ETAC ; XXCLL_PROVE_OUTPUT_ETAC glf ])
			     (XXCLL_PROVE_OUTPUT_ETAC glf))
			    (timesProof i)) s gl in
	   timesProof (createSubsetIndex iterms) s gl
		      
           else if (comb = `LinPlus`) then
	   let select = Clltac.cllCombSelect out in
	   if (select <= 0)
	   then (EORELSE (ETHEN (TIME_ETAC "PLUS1" (ruleseq ~glfrees:glf Cllpi.ll_plus1)) (XXCLL_PROVE_OUTPUT_ETAC glf))
			 (ETHEN (TIME_ETAC "PLUS2" (ruleseq ~glfrees:glf Cllpi.ll_plus2)) (XXCLL_PROVE_OUTPUT_ETAC glf))) s gl
	   else (EORELSE (ETHEN (TIME_ETAC "PLUS2" (ruleseq ~glfrees:glf Cllpi.ll_plus2)) (XXCLL_PROVE_OUTPUT_ETAC glf))
			 (ETHEN (TIME_ETAC "PLUS1" (ruleseq ~glfrees:glf Cllpi.ll_plus1)) (XXCLL_PROVE_OUTPUT_ETAC glf))) s gl
										      
           else
           failwith "XXCLL_PROVE_OUTPUT_ETAC"    
      ) with Failure _ -> failwith "XXCLL_PROVE_OUTPUT_ETAC"



	
    let (XXCLL_PROVE_ETAC:?glfrees:term list->seqtactic) =
      fun ?(glfrees=[]) s gl ->
	try (
	  EEVERY [
	    XXCLL_PROVE_INPUT_ETAC glfrees;
	    XXCLL_PROVE_OUTPUT_ETAC glfrees] s gl
      ) with Failure s -> failwith ("XXCLL_PROVE_TAC: " ^ s)

    let (XXCLL_PROVE_TAC:?glfrees:term list->astactic) =
      fun ?(glfrees=[]) s gl ->
      Actionstate.CLL_TAC (XXCLL_PROVE_ETAC ~glfrees:glfrees) s gl (* (gl_frees gl)*)
			  

 let (XXFILTER_TAC:?glfrees:term list-> string -> term -> term -> bool -> astactic) =
      let PRINT_PROVEN str st gl =
	(print_string ("-- Proven: " ^ str) ;
	 print_newline();
	 ALL_ETAC st gl) in
      fun ?(glfrees=[]) lbl cllTerm targetProp isInput st gl ->
	print_string ("Trying to match: " ^ (string_of_term cllTerm) ^ " - with : " ^ (string_of_term targetProp));
	print_newline();
	if (isInput) then
	  if ((rand o rand o rator) cllTerm = targetProp) then Actionstate.CLL_TAC ALL_ETAC st gl
	  else 
	    ETHENL (TIME_ETAC "DRULE" (Actionstate.CLL_TAC 
		      (drule_seqtac ~lbl:lbl ~reslbl:lbl ~glfrees:glfrees
			 [`A:LinProp`,(rand o rand o rator) cllTerm; (* rand of NEG *)
			  `a:num`,rand cllTerm;
			  `B:LinProp`,targetProp;
			  `b:num`,rand cllTerm] (* TODO This needs testing? *)
			 Clltac.Rules.ll_filter_input)))
		   [ (*ETHEN REM_AS_TAC*) (TIME_ETAC "PROVE" (XXCLL_PROVE_TAC ~glfrees:glfrees)) ;
		PRINT_PROVEN ("|-- NEG (" ^ (string_of_term targetProp) ^ ") , (" ^ ((string_of_term o rand o rand o rator) cllTerm) ^ ")")
	      ] st gl
	else
	  if ((rand o rator) cllTerm = targetProp) then Actionstate.CLL_TAC ALL_ETAC st gl
	  else
	    ETHENL (Actionstate.CLL_TAC 
		      (drule_seqtac ~lbl:lbl ~reslbl:lbl
			 [`A:LinProp`,(rand o rator) cllTerm;
			  `a:num`,rand cllTerm;
			  `B:LinProp`,targetProp;
			  `b:num`,rand cllTerm] (* TODO This needs testing? *)
			 Clltac.Rules.ll_filter_output))
		   [ (*ETHEN REM_AS_TAC*) (TIME_ETAC "PROVE" Clltac.CLL_PROVE_TAC) ;
		PRINT_PROVEN ("|-- NEG (" ^ ((string_of_term o rand o rator) cllTerm) ^ ") , (" ^ (string_of_term targetProp) ^ ")")
	      ] st gl;;
	      


print_string "XXX";;
    
      

    
Trying to match: NEG Assignment <> cSetAssignmentResponsible_Assignment_1 - with : Assignment **
RequestedContract **
ServiceRequester **
PendingHealthcareService
DRULE: 0.0242
PROVE - FAILED: 0.0797
Trying to match: NEG PendingHealthcareService <> cProvideService_PendingHealthcareService_2 - with : RequestedContract ** ServiceRequester ** PendingHealthcareService
DRULE: 0.0241
PROVE - FAILED: 0.061
Trying to match: NEG RequestedContract <> cDecideCollaboration_RequestedContract_1 - with : RequestedContract ** ServiceRequester ** PendingHealthcareService
DRULE: 0.0242
PROVE - FAILED: 0.0607
Trying to match: NEG PendingHealthcareService <> cProvideService_PendingHealthcareService_2 - with : RequestedContract ** ServiceRequester ** PendingHealthcareService
DRULE: 0.0241
PROVE - FAILED: 0.0607
Trying to match: NEG RequestedContract <> cDecideCollaboration_RequestedContract_1 - with : RequestedContract ** ServiceRequester ** PendingHealthcareService
DRULE: 0.0242
PROVE - FAILED: 0.0609
Trying to match: NEG PendingHealthcareService <> cProvideService_PendingHealthcareService_2 - with : RequestedContract
DRULE: 0.0238
PROVE - FAILED: 0.027
Trying to match: NEG RequestedContract <> cDecideCollaboration_RequestedContract_1 - with : RequestedContract
Trying to match: NEG PendingHealthcareService <> cProvideService_PendingHealthcareService_2 - with : ServiceRequester ** PendingHealthcareService
DRULE: 0.024
PROVE - FAILED: 0.0424
Trying to match: NEG PendingHealthcareService <> cProvideService_PendingHealthcareService_2 - with : ServiceRequester ** PendingHealthcareService
DRULE: 0.024
PROVE - FAILED: 0.0423
Trying to match: NEG PendingHealthcareService <> cProvideService_PendingHealthcareService_2 - with : ServiceRequester
DRULE: 0.0239
PROVE - FAILED: 0.027
Trying to match: NEG PendingHealthcareService <> cProvideService_PendingHealthcareService_2 - with : ServiceRequester
DRULE: 0.0241
PROVE - FAILED: 0.0269
Buffering: ServiceRequester
BUFFER_TAC: |-- ' (ServiceRequester <> b430)^' (NEG ServiceRequester <> buf430) (...)
INPUT_TAC' ServiceRequester ** PendingHealthcareService: 0.2684
INPUT_TAC' RequestedContract ** ServiceRequester ** PendingHealthcareService: 0.6106
INPUT_TAC' Assignment **
RequestedContract **
ServiceRequester **
PendingHealthcareService: 0.9345
*** Done: (2.5727)
val it : unit = ()
  #
  (* ****** *)
Trying to match: NEG Assignment <> cSetAssignmentResponsible_Assignment_1 - with : Assignment **
RequestedContract **
ServiceRequester **
PendingHealthcareService
DRULE: 0.0148
PROVE - FAILED: 0.0121
Trying to match: NEG PendingHealthcareService <> cProvideService_PendingHealthcareService_2 - with : RequestedContract ** ServiceRequester ** PendingHealthcareService
DRULE: 0.0146
PROVE - FAILED: 0.009
Trying to match: NEG RequestedContract <> cDecideCollaboration_RequestedContract_1 - with : RequestedContract ** ServiceRequester ** PendingHealthcareService
DRULE: 0.0146
PROVE - FAILED: 0.0089
Trying to match: NEG PendingHealthcareService <> cProvideService_PendingHealthcareService_2 - with : RequestedContract ** ServiceRequester ** PendingHealthcareService
DRULE: 0.0146
PROVE - FAILED: 0.0089
Trying to match: NEG RequestedContract <> cDecideCollaboration_RequestedContract_1 - with : RequestedContract ** ServiceRequester ** PendingHealthcareService
DRULE: 0.0146
PROVE - FAILED: 0.0089
Trying to match: NEG PendingHealthcareService <> cProvideService_PendingHealthcareService_2 - with : RequestedContract
DRULE: 0.0143
PROVE - FAILED: 0.0065
Trying to match: NEG RequestedContract <> cDecideCollaboration_RequestedContract_1 - with : RequestedContract
Trying to match: NEG PendingHealthcareService <> cProvideService_PendingHealthcareService_2 - with : ServiceRequester ** PendingHealthcareService
DRULE: 0.0144
PROVE - FAILED: 0.0064
Trying to match: NEG PendingHealthcareService <> cProvideService_PendingHealthcareService_2 - with : ServiceRequester ** PendingHealthcareService
DRULE: 0.0144
PROVE - FAILED: 0.0063
Trying to match: NEG PendingHealthcareService <> cProvideService_PendingHealthcareService_2 - with : ServiceRequester
DRULE: 0.0143
PROVE - FAILED: 0.0065
Trying to match: NEG PendingHealthcareService <> cProvideService_PendingHealthcareService_2 - with : ServiceRequester
DRULE: 0.0143
PROVE - FAILED: 0.0066
Buffering: ServiceRequester
BUFFER_TAC: |-- ' (ServiceRequester <> b430)^' (NEG ServiceRequester <> buf430) (...)
INPUT_TAC' ServiceRequester ** PendingHealthcareService: 0.1231
INPUT_TAC' RequestedContract ** ServiceRequester ** PendingHealthcareService: 0.2572
INPUT_TAC' Assignment **
RequestedContract **
ServiceRequester **
PendingHealthcareService: 0.3719
*** Done: (0.6942)

;;

REWRITE_CONV [] `a = b + 1 ==> b = x +1 ` ;;
REWRITE_CONV [] `a = b + 1 ==> a = x +1 ` ;;
SIMP_CONV [] `a = b + 1 ==> b + 1 = x +1 ` ;;
SIMP_CONV [] `a = b + 1 ==> a = x +1 ` ;;
SIMP_CONV [] `b + 1 = a ==> b + 1 = x +1 ` ;;
SIMP_CONV [] `b + 1 = a ==> a = x +1 ` ;;


(*



*)


let mypa = Proc.create "Pa" [`A ++ C`;`B ++ (D ** E)`] `C ** (G ++ H)` ;;
let mypb = Proc.create "Pb" [`A`;`B`] `C ++ D` ;;

let myst = Actionstate.create 0;;
let rec add_provs procs st =
    match procs with
      | [] -> st
      | p :: t ->
	let n,prov = Proc.get_atomic_prov p in
	add_provs t (Actionstate.add_prov n prov st);;
let mycomp lbl procs acts =
  let p,_,s = Proc.compose (add_provs procs myst) lbl procs acts in p,s;;

(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

let mypa = Proc.create "Pa" [`X`] `A` ;;
let mypb = Proc.create "Pb" [`A`] `Y` ;;
let myact1 = Action.create "JOIN" "Pa" "" "Pb" "(NEG A)" "R1";;
let myr1 = fst(mycomp "R1" [mypa;mypb] [myact1]);;
let mybod = rhs myr1.Proc.proc;;

print_string(scala_of_pat mybod);;

let mypc = Proc.create "Pc" [`Y`] `Z` ;;
let myact2 = Action.create "JOIN" "R1" "" "Pc" "(NEG Y)" "R2";;
let myr2 = fst(mycomp "R2" [myr1;mypc] [myact2]);;

scala_deploy_print "/" "/home/kane/PapPiLib/" "uk.ac.ed.skiexample" "SkiExample" myr2 [mypa;mypb;mypc;myr1] true true;;

print_string(scala_proc 0 mypa);;
print_string(scala_proc 0 mypb);;
print_string(scala_proc 0 myr1);;
print_string(scala_proc 0 mypc);;
print_string(scala_proc 0 myr2);;

let mypd = Proc.create "Pd" [`X`] `A ++ (B ** G)` ;;
let mype = Proc.create "Pe" [`B ++ A`] `Y` ;;
let myact1 = Action.create "JOIN" "Pd" "rlr" "Pe" "NEG (B ++ A)" "R3";;
let myr3 = fst(mycomp "R3" [mypd;mype] [myact1]);;
let myact1 = Action.create "JOIN" "Pd" "lr" "Pe" "NEG (B ++ A)" "R3b";;
let myr3b = fst(mycomp "R3b" [mypd;mype] [myact1]);;

print_string(scala_proc 0 mypd);;
print_string(scala_proc 0 mype);;
print_string(scala_proc 0 myr3);;
print_string(scala_proc 0 myr3b);;


let selectModel = Proc.create "SelectModel" [`PriceLimit`;`SkillLevel`] `Brand ** Model` ;;
let selectLength = Proc.create "SelectLength" [`HeightCM`;`WeightKG`] `LengthCM` ;;
let cm2Inch = Proc.create "CM2Inch" [`LengthCM`] `LengthInch` ;;
let usd2Nok = Proc.create "USD2NOK" [`PriceUSD`] `PriceNOK` ;;
let selectSki = Proc.create "SelectSki" [`LengthInch`;`Brand`;`Model`] `PriceUSD ++ Exception` ;;

let myact1 = Action.create "JOIN" "SelectLength" "" "CM2Inch" "NEG (LengthCM)" "SLI";;
let myr1 = mycomp "SLI" [selectModel;selectLength;cm2Inch;usd2Nok;selectSki] [myact1];;
let myact2 = Action.create "JOIN" "SLI" "" "SelectSki" "NEG (LengthInch)" "SSI";;
let myr2 = mycomp "SSI" [selectModel;selectLength;cm2Inch;usd2Nok;selectSki] [myact1;myact2];;
let myact3 = Action.create "JOIN" "SelectModel" "lr" "SSI" "NEG (Brand)" "SMI";;
let myr3 = mycomp "SMI" [selectModel;selectLength;cm2Inch;usd2Nok;selectSki] [myact1;myact2;myact3];;
let myact4 = Action.create "JOIN" "SMI" "lr" "USD2NOK" "NEG (PriceUSD)" "GetSki";;
let myr4 = mycomp "GetSki" [selectModel;selectLength;cm2Inch;usd2Nok;selectSki] [myact1;myact2;myact3;myact4];;
let getSki = fst myr4;;

(print_string o snd)(scala_stateful_proc_file "/" "/" "com" "Project" getSki);;


scala_stateful_deploy_print "/" "/home/kane/PapPiLib/" "com.workflowfm.pew.skiexample" "SkiExample" getSki [selectModel;selectLength;cm2Inch;usd2Nok;selectSki] true true;;


let xtbl = make_table (objekt (Json_io.json_of_string xjson));;
let xact = Json_comp.to_action (field xtbl "action");;
let lhs = Json_comp.to_process (field xtbl "lhs");;
let rhs = Json_comp.to_process (field xtbl "rhs");;
let xstate = Json_comp.to_actionstate (field xtbl "state");;

let mypa = Proc.create "Pa" [`N`;`L`] `L ** O` ;;
let mypb = Proc.create "Pb" [`W`] `O ++ N` ;;
let myact1 = Action.create "JOIN" "Pb" "r" "Pa" "(NEG N)" "R1";;
let myr1 = fst(mycomp "R1" [mypa;mypb] [myact1]);;

let mypa = Proc.create "Pa" [`N`;`R`] `(R ** Y) ++ E` ;;
let mypb = Proc.create "Pb" [`W`] `Y ++ N` ;;
let myact1 = Action.create "JOIN" "Pb" "r" "Pa" "(NEG N)" "R1";;
let myr1 = fst(mycomp "R1" [mypa;mypb] [myact1]);;

let mypa = Proc.create "Pa" [`N`] `Y` ;;
let mypb = Proc.create "Pb" [`W`] `Y ++ N` ;;
let myact1 = Action.create "JOIN" "Pb" "r" "Pa" "(NEG N)" "R1";;
let myr1 = fst(mycomp "R1" [mypa;mypb] [myact1]);;

let mypa = Proc.create "Pa" [`N`] `G` ;;
let mypb = Proc.create "Pb" [`W`] `Y ++ N` ;;
let myact1 = Action.create "JOIN" "Pb" "r" "Pa" "(NEG N)" "R1";;
let myr1 = fst(mycomp "R1" [mypa;mypb] [myact1]);;

let mypa = Proc.create "Pa" [`N`] `H ++ G ++ Y` ;;
let mypb = Proc.create "Pb" [`W`] `Y ++ N` ;;
let myact1 = Action.create "JOIN" "Pb" "r" "Pa" "(NEG N)" "R1";;
let myr1 = fst(mycomp "R1" [mypa;mypb] [myact1]);; (* Keep using plus1 and plus2!! *)


let my_hash = Hashtbl.create 50;;
Hashtbl.add my_hash "h" "hello";
Hashtbl.add my_hash "w" "wine";;
Hashtbl.replace my_hash "t" "tralala";;
Hashtbl.length my_hash;;
Hashtbl.fold (fun k v l -> v::l) my_hash [];;
Hashtbl.iter (fun k v -> Hashtbl.replace my_hash k (v^"1")) my_hash;;
Hashtbl.mem my_hash "h";;
Hashtbl.mem my_hash "x";;

Hashtbl.add processes "Pa" mypa;;
Hashtbl.find processes "Px";;


create "Pa" [`N`] `G` ;;
create "Pb" [`W`] `Y ++ N` ;;
compose1 "JOIN" "Pb" "r" "Pa" "(NEG N)";;


module Xrules = Cllrules(Cllpi);;
Xrules.ll_with_self;;
(* ------------------------------------------------------------------------------------*)

(* Web stuff! *)

