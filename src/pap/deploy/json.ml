(* ========================================================================= 
   Deploy commands for the JSON API:
   - PiViz
   - PiLib
   - PEW
   
   Petros Papapanagiotou
   Center of Intelligent Systems and their Applications         
   School of Informatics, University of Edinburgh                         
   2019
 ========================================================================= *)

needs (!serv_dir ^ "api/json/lib.ml");;
needs (!serv_dir ^ "api/json/api.ml");;
needs (!serv_dir ^ "pap/deploy/piviz.ml");;
needs (!serv_dir ^ "pap/deploy/pilib.ml");;
needs (!serv_dir ^ "pap/deploy/pew.ml");;

module Json_deploy_commands (Api : Composer_json_api) =
  struct
    open Json_type.Browse
    open Api
    module Piviz = Piviz_make(Composer)
    module Pilib = Pilib_make(Composer)
    module Pew = Pew_make(Composer)

    let deploy f tbl =
      let proc = Decode.process (field tbl "process")
      and deps = list Decode.process (field tbl "components") in
      let res = f proc deps in
      [ response res ]
      
    let piviz j =
      let tbl = make_table (objekt j) in
      deploy Piviz.deploy tbl

    let pilib j =
      let tbl = make_table (objekt j) in
      let sep = string (field tbl "separator")
      and path = string (field tbl "path")
      and pkg = string (field tbl "pkg")
      and proj = string (field tbl "project")
      and mn = bool (field tbl "main")
      and jv = bool (field tbl "java")
      in
      deploy (Pilib.deploy sep path pkg proj mn jv) tbl
      
    let pew j =
      let tbl = make_table (objekt j) in
      let sep = string (field tbl "separator")
      and path = string (field tbl "path")
      and pkg = string (field tbl "pkg")
      and proj = string (field tbl "project")
      and mn = bool (field tbl "main")
      and jv = bool (field tbl "java")
      in
      deploy (Pew.deploy sep path pkg proj mn jv) tbl
      
    let load () = 
      (ignore o map (uncurry Commands.add)) [
          ("piviz",piviz);
          ("pilib",pilib);
          ("pew",pew)
        ]
  end ;;
