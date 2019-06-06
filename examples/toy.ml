loads (!hol_dir ^ "workflowfm/src/make.console.ml");;

create "Pa" [`X`] `A ** B ** C` ;;
create "Pb" [`A`] `D` ;;
create "Pc" [`B`] `E` ;;
create "Pd" [`C`] `F` ;;

join "Pa" "lr" "Pb" "(NEG A)";;
join "_Step0" "lrr" "Pc" "(NEG B)";;
join "_Step1" "r" "Pd" "(NEG C)";;

store "_Step2" "Res";;
