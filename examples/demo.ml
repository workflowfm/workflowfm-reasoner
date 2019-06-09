(* ========================================================================= 
   A series of examples that demonstrate the system and the how the tactics
   work.
        
   Petros Papapanagiotou                  
   Center of Intelligent Systems and their Applications         
   School of Informatics, The University of Edinburgh                         
   2019                                
 ========================================================================= *)

needs (!hol_dir ^ "/workflowfm/src/make.console.ml");;


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

let demoname () =
  let counter = !democounter in
  democounter := counter +1 ;
  fun s -> s^(string_of_int counter);;

let demopname () =
  let counter = !democounter - 1 in
  fun s -> s^(string_of_int counter);;
  

let joindemo lins lout larg rins rout rarg =
  let [p;q;r] = map (demoname()) ["P";"Q";"R"] in
  reset();
  create p lins lout;
  create q rins rout;
  join p larg q rarg;
  store "_Step0" r;
  reset();
  demolast();;

let withdemo lins lout larg rins rout rarg =
  let [p;q;r] = map (demoname()) ["P";"Q";"R"] in
  reset();
  create p lins lout;
  create q rins rout;
  cwith p larg q rarg;
  store "_Step0" r;
  reset();
  demolast();;

let tensordemo lins lout rins rout =
  let [p;q;r] = map (demoname()) ["P";"Q";"R"] in
  reset();
  create p lins lout;
  create q rins rout;
  tensor p q;
  store "_Step0" r;
  reset();
  demolast();;

let errordemo ins out = 
  create (demopname () "Error") ins out;;


create "ExampleProcess" [`X`;`Y++Z`] `A ** B ** C` ;;

tensordemo [`X`] `A ** B` [`Y`] `C ** D` ;;

withdemo [`X`] `Z` "NEG X" [`Y`] `W` "NEG Y";;
withdemo [`X`] `Z` "NEG X" [`Y`] `Z` "NEG Y";;
withdemo [`X`] `A ** B` "NEG X" [`Y`] `B ** A` "NEG Y";;

withdemo [`X`;`A`;`B`] `Z` "NEG X" [`Y`] `Z` "NEG Y";;
withdemo [`X`;`A`] `Z` "NEG X" [`Y`;`B`] `W` "NEG Y";;
withdemo [`X`;`A`;`C`] `Z` "NEG X" [`Y`;`B`;`D`] `W` "NEG Y";;
withdemo [`X`;`A`;`C`] `Z` "NEG X" [`Y`;`B`;`C`] `W` "NEG Y";;
withdemo [`X`;`A`;`C`;`C`;`C`] `Z` "NEG X" [`Y`;`B`;`C`;`C`] `W` "NEG Y";;

withdemo [`X`;`A`] `Z ** A` "NEG X" [`Y`] `Z` "NEG Y";;
withdemo [`X`;`A`] `Z ++ (Z ** A)` "NEG X" [`Y`] `Z` "NEG Y";;


joindemo [`X`] `A` "" [`A`] `Y` "NEG A";;

joindemo [`X`] `A ** B` "lr" [`A`] `Y` "NEG A";;
joindemo [`X`] `A ** B` "lr" [`A`;`C`] `Y` "NEG A";;
joindemo [`X`] `A ** B` "lr" [`A`;`B`] `Y` "NEG A";;

joindemo [`X`] `A ++ E` "r" [`E`] `Y` "NEG E";;
joindemo [`X`] `A ++ E` "r" [`E`] `A` "NEG E";;
joindemo [`X`] `A ++ E` "r" [`E`;`B`] `Y` "NEG E";;

joindemo [`X`] `A ++ E` "lr" [`A ++ E`] `Y` "NEG (A ++ E)";;
joindemo [`X`] `E ++ A` "lr" [`A ++ E`] `Y` "NEG (A ++ E)";;

joindemo [`X`] `A` "" [`A ++ B`] `Y` "NEG (A ++ B)";;
joindemo [`X`] `A ++ E` "lr" [`A ++ B`] `Y` "NEG (A ++ B)";;
joindemo [`X`] `A ++ E` "lr" [`A ++ B ++ E`] `Y` "NEG (A ++ B ++ E)";;
joindemo [`X`] `A ** C` "lr" [`(A ** C) ++ B`] `Y` "NEG ((A ** C) ++ B)";;

joindemo [`X`] `A ** (A ++ B)` "lr" [`A`] `Y` "NEG A";;
joindemo [`X`] `A ** (A ++ B)` "rlr" [`A`] `Y` "NEG A";;

joindemo [`X`] `A ++ (B ** C)` "lr" [`B ++ A`] `Y` "NEG (B ++ A)";;
joindemo [`X`] `A ++ (B ** C)` "rlr" [`B ++ A`] `Y` "NEG (B ++ A)";;

joindemo [`X`] `A ++ B` "lr" [`A`;`A ++ B`] `Y` "NEG A";;
joindemo [`X`] `A ++ B` "lr" [`A`;`A ++ B`] `Y` "NEG (A ++ B)";;

joindemo [`X`] `(A ** B) ++ E` "r" [`E`] `A ** B` "NEG E";;
joindemo [`X`] `(A ** B) ++ E` "r" [`E`] `A ** B` "NEG E";;
joindemo [`X`] `(A ** B) ++ E` "r" [`E`] `(A ** B) ++ Y` "NEG E";;


joindemo [`X`] `(A ++ B) ** (A ++ B)` "lrlr" [`A`;`A`] `Y` "NEG (A)";;
joindemo [`X`] `(A ++ B) ** (A ++ B)` "lrlr" [`A ++ B`] `Y` "NEG (A ++ B)";;
joindemo [`X`] `(A ++ B) ** (A ++ B)` "lrlr" [`A ++ B`;`A`] `Y` "NEG (A ++ B)";;
joindemo [`X`] `(A ++ B) ** ((A ** C) ++ B)` "lrlr" [`A ++ B`;`A`;`C`] `Y` "NEG (A ++ B)";;
joindemo [`X`] `(A ++ B) ** ((A ** C) ++ B)` "lrlr" [`A ++ B`;`A`] `Y` "NEG (A ++ B)";;

joindemo [`X`] `(C ++ A ++ B)` "rlr" [`A ++ B`] `Y` "NEG (A ++ B)";;
joindemo [`X`] `(A ++ B ++ C)` "lr" [`A ++ B`] `Y` "NEG (A ++ B)";;
join (demopname () "R") "rlr" (demopname () "Q") "NEG (A ++ B)";;
store "_Step0" (demopname () "S");;

joindemo [`X`] `(A ** B) ++ (C ** D)` "lrlr" [`A`;`B`;`C`] `Y` "NEG A";;


joindemo [`X`] `A ** B` "lr" [`(A ** B) ++ E`] `Y` "NEG ((A ** B) ++ E)";;
joindemo [`X`] `A` "" [`(A ** B) ++ E`] `Y` "NEG ((A ** B) ++ E)";;
errordemo [`X`;`B`] `Y` ;;
joindemo [`X`] `A ** B` "lr" [`(C ** A) ++ E`] `Y` "NEG ((C ** A) ++ E)";;
errordemo [`X`;`C`] `Y ** B` ;;







