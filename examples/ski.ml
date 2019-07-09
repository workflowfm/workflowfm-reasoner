(* ========================================================================= 
   The Ski example
   Originally by Jinghai Rao
   
   Petros Papapanagiotou                  
   Center of Intelligent Systems and their Applications         
   School of Informatics, The University of Edinburgh                         
   2010-2019                                
 ========================================================================= *)

needs (!hol_dir ^ "/workflowfm/make.console.ml");;

create "SelectModel" [`PriceLimit`; `SkillLevel`] `Brand ** Model` ;;
create "SelectLength" [`HeightCM`; `WeightKG`] `LengthCM` ;;
create "SelectSki" [`LengthInch`; `Brand`; `Model`] `PriceUSD ++ Exception` ;;

create "CM2Inch" [`LengthCM`] `LengthInch` ;;
create "USD2NOK" [`PriceUSD`] `PriceNOK` ;;


join "SelectLength" "" "CM2Inch" "LengthCM";;
join "_Step0" "" "SelectSki" "LengthInch";;
join "SelectModel" "lr" "_Step1" "Brand";;
join "_Step2" "lr" "USD2NOK" "PriceUSD";;

store "_Step3" "GetSki";;
