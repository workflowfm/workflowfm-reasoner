(* ========================================================================= 
   A series of examples that demonstrate the system and the how the tactics
   work.
        
   Petros Papapanagiotou                  
   Center of Intelligent Systems and their Applications         
   School of Informatics, The University of Edinburgh                         
   2019                                
 ========================================================================= *)

needs (!hol_dir ^ "/workflowfm/src/make.console.ml");;

create "ExampleProcess" [`X`;`Y++Z`] `A ** B ** C` ;;

let democounter = ref 1;;

let demolast () =
  let counter = !democounter - 1 in
  let r = "R"^(string_of_int counter) in
  let proc = get r in
  print_string "Inputs:";
  print_newline();
  ignore(print_tml (map fst proc.inputs));
  print_string "Output:";
  print_newline();
  print_term (fst proc.output);
  print_newline();;

let demonames () =
  let counter = !democounter in
  democounter := counter +1 ;
  fun s -> s^(string_of_int counter);;
  

let joindemo lins lout larg rins rout rarg =
  let [p;q;r] = map (demonames()) ["P";"Q";"R"] in
  reset();
  create p lins lout;
  create q rins rout;
  join p larg q rarg;
  store "_Step0" r;
  reset();
  demolast();;

let withdemo lins lout larg rins rout rarg =
  let [p;q;r] = map (demonames()) ["P";"Q";"R"] in
  reset();
  create p lins lout;
  create q rins rout;
  cwith p larg q rarg;
  store "_Step0" r;
  reset();
  demolast();;



joindemo [`X`] `A` "" [`A`] `Y` "NEG A";;
joindemo [`X`] `A ** B` "lr" [`A`] `Y` "NEG A";;
joindemo [`X`] `A ** B` "lr" [`A`;`B`] `Y` "NEG A";;
joindemo [`X`;`Y`] `A ++ E` "r" [`E`] `R` "NEG E";;
joindemo [`X`;`Y`] `A ++ E` "r" [`E`;`B`] `R` "NEG E";;
joindemo [`X`] `A ++ E` "lr" [`A ++ E`] `R` "NEG (A ++ E)";;
joindemo [`X`] `E ++ A` "lr" [`A ++ E`] `R` "NEG (A ++ E)";;
joindemo [`X`] `A` "" [`A ++ B`] `R` "NEG (A ++ B)";;
joindemo [`X`] `A ++ E` "lr" [`A ++ B`] `R` "NEG (A ++ B)";;
joindemo [`X`] `A ++ E` "lr" [`A ++ B ++ E`] `R` "NEG (A ++ B ++ E)";;
joindemo [`X`] `A ** C` "lr" [`(A ** C) ++ B`] `R` "NEG ((A ** C) ++ B)";;
joindemo [`X`] `A ++ (B ** C)` "lr" [`B ++ A`] `Y` "NEG (B ++ A)";;
joindemo [`X`] `A ++ (B ** C)` "rlr" [`B ++ A`] `Y` "NEG (B ++ A)";;

joindemo [`X`] `(A ++ B) ** (A ++ B)` "lrlr" [`A`;`A`] `Y` "NEG (A)";;

joindemo [`X`] `A` "" [`(A ** B) ++ E`] `Y` "NEG ((A ** B) ++ E)";;
joindemo [`X`] `A ** B` "lr" [`(C ** A) ++ E`] `Y` "NEG ((C ** A) ++ E)";;

withdemo [`X`] `Z` "NEG X" [`Y`] `Z` "NEG Y";;
withdemo [`X`;`A`;`B`] `Z` "NEG X" [`Y`] `Z` "NEG Y";;
withdemo [`X`] `A ** B` "NEG X" [`Y`] `B ** A` "NEG Y";;
withdemo [`X`] `A ++ B` "NEG X" [`Y`] `B ++ A` "NEG Y";;
withdemo [`X`;`A`] `Z` "NEG X" [`Y`;`B`] `W` "NEG Y";;
withdemo [`X`;`A`;`C`] `Z` "NEG X" [`Y`;`B`;`D`] `W` "NEG Y";;
withdemo [`X`;`A`;`C`] `Z` "NEG X" [`Y`;`B`;`C`] `W` "NEG Y";;
withdemo [`X`;`A`;`C`;`C`;`C`] `Z` "NEG X" [`Y`;`B`;`C`;`C`] `W` "NEG Y";;


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


let mypa = Proc.create "Pa" [`W`] `D ** (E ++ A)` ;;
let mypb = Proc.create "Pb" [`A`;`D`;`C`] `G` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG D" "Res";;
let myact1 = Action.create "JOIN" "Pa" "rr" "Pb" "NEG A" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;

let mypa = Proc.create "Pa" [`W`] `A ++ E` ;;
let mypb = Proc.create "Pb" [`E`] `G ++ A` ;;
let myact1 = Action.create "JOIN" "Pa" "r" "Pb" "NEG E" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;



(*
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
*)
(*
let mypa = Proc.create "Pa" [`A ++ C`;`B ++ (D ** E)`] `C ** (G ++ H)` ;;
let mypa = Proc.create "Pa" [`A`;`B`] `C ** D` ;;
let mypb = Proc.create "Pb" [`C`;`E`] `G` ;;
let mypc = Proc.create "Pc" [`D`;`G`] `H` ;;
let myact1 = Action.create "JOIN" "Pa" "l" "Pb" "(NEG C)" "Res";;
let myact2 = Action.create "JOIN" "Res" "r" "Pc" "(NEG D)" "Rez";;
Proc.compose "Res" [mypa;mypb;mypc] [myact1];;
Proc.compose "Rez" [mypa;mypb;mypc] [myact1;myact2];;
*)
(*
let mypa = Proc.create "Pa" [`A`;`B`] `C ** D` ;;
let mypb = Proc.create "Pb" [`C`;`E`] `G` ;;
let mypc = Proc.create "Pc" [`G`] `H` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG C" "Res";;
let myact2 = Action.create "JOIN" "Res" "lr" "Pc" "NEG G" "Rez";;
mycomp "Res" [mypa;mypb;mypc] [myact1];;
mycomp "Rez" [mypa;mypb;mypc] [myact1;myact2];;
*)
(*
let mypa = Proc.create "Pa" [`A`] `C ++ D` ;;
let mypb = Proc.create "Pb" [`C`;`E`;`F`] `G` ;;
let mypc = Proc.create "Pc" [`J`;`K`] `E ** L` ;;
let myact1 = Action.create "JOIN" "Pc" "l" "Pb" "NEG E" "Res";;
let myact2 = Action.create "JOIN" "Pa" "l" "Res" "NEG C" "Rez";;
Proc.compose myst "Res" [mypa;mypb;mypc] [myact1];;
Proc.compose myst "Rez" [mypa;mypb;mypc] [myact1;myact2];;
*)
(*
let mypa = Proc.create "Pa" [`A`] `C ++ D` ;;
let mypb = Proc.create "Pb" [`C`] `G` ;;
let mypc = Proc.create "Pc" [`D`] `H` ;;
let myact1 = Action.create "JOIN" "Pa" "lr" "Pb" "NEG C" "Res";;
let myact2 = Action.create "JOIN" "Res" "r" "Pc" "NEG D" "Rez";;
mycomp "Res" [mypa;mypb;mypc] [myact1];;
mycomp "Rez" [mypa;mypb;mypc] [myact1;myact2];;
*)
(*
let mypa = Proc.create "Pa" [`W`] `(A**B) ++ (C**D)` ;;
let mypb = Proc.create "Pb" [`A`;`B`;`C`] `Z` ;;
let myact1 = Action.create "JOIN" "Pa" "lrlr" "Pb" "NEG A" "Res";;
mycomp "Res" [mypa;mypb] [myact1];;
(* is C ** C ** D actually the best outcome? *)
*)
