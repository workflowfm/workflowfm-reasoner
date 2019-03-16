needs (!serv_dir ^ "pap/pilib/pilib.ml");;
needs (!serv_dir ^ "json/lib.ml");;

module Json_pilib =
  struct
  include Json_comp
  open Json_type.Browse
	
   let scaldeploy j =
     let tbl = make_table (objekt j) in
     let proc = to_process (field tbl "process")
     and deps = list to_process (field tbl "components")
     and sep = string (field tbl "separator")
     and path = string (field tbl "path")
     and pkg = string (field tbl "pkg")
     and proj = string (field tbl "project")
     and mn = bool (field tbl "main")
     and jv = bool (field tbl "java")
     in
     let ovr,opt = scala_deploy sep path pkg proj proc deps mn jv in
     let mk_res ov (addr,content) =
       Object [
       ("path", String addr);
       ("content", String content);
       ("overwrite", Bool ov)] in
     [Object [
      ("response", String ("PiLibDeploy"));
      ("deployment", Array (map (mk_res true) ovr @ map (mk_res false) opt));
     ]]


   let scaldeploystateful j =
     let tbl = make_table (objekt j) in
     let proc = to_process (field tbl "process")
     and deps = list to_process (field tbl "components")
     and sep = string (field tbl "separator")
     and path = string (field tbl "path")
     and pkg = string (field tbl "pkg")
     and proj = string (field tbl "project")
     and mn = bool (field tbl "main")
     and jv = bool (field tbl "java")
     in
     let ovr,opt = scala_stateful_deploy sep path pkg proj proc deps mn jv in
     let mk_res ov (addr,content) =
       Object [
       ("path", String addr);
       ("content", String content);
       ("overwrite", Bool ov)] in
     [Object [
      ("response", String ("PiLibStatefulDeploy"));
      ("deployment", Array (map (mk_res true) ovr @ map (mk_res false) opt));
     ]]
 end;;
