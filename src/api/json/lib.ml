(* ========================================================================= *)
(* Library loader for json-wheel.                                            *)
(* We are unable to use Yojson at this time because we can't use polymorphic *)
(* variants in HOL Light.                                                    *)
(*                                                                           *)
(*                            Petros Papapanagiotou                          *)
(*                           University of Edinburgh                         *)
(*                                2015 - 2019                                *)
(* ========================================================================= *)


#use "topfind";;
#require "json-wheel";;
open Json_type;;

