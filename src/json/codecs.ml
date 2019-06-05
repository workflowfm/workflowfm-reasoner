(* ========================================================================= 
   JSON codecs for          
   
   Petros Papapanagiotou
   Center of Intelligent Systems and their Applications         
   School of Informatics, University of Edinburgh                         
   2019
 ========================================================================= *)

needs (!serv_dir ^ "CLL/CLL.ml");;
needs (!serv_dir ^ "processes/actions.ml");;
needs (!serv_dir ^ "processes/processes.ml");;
needs (!serv_dir ^ "composer.ml");;
needs (!serv_dir ^ "json/lib.ml");;

module Json_cll = 
  struct
  open Json_type.Browse
  module Encode =
    struct
      let rec prop tm =
        let rec mysplitlist dest x = (* Right-associative sequences of an operator are converted to lists *)
          try let l,r = dest x in
	          let res = mysplitlist dest r in
              (l::res)
          with Failure _ -> [x] in

        if (is_var tm or is_const tm) then 
          (Object[
               ("type", String "var");
               ("name", String (string_of_term tm))])
        else
          
          let op,args = strip_comb tm in
          let op_string =
            if (op = `NEG`) then "neg"
            else if (op = `LinTimes`) then "times"
            else if (op = `LinPlus`) then "plus"
            else failwith ("Json_cll.Encode.prop: Unexpected operator - " ^ (string_of_term op))
          in
          let args' = 
            if (op = `NEG`) then args
            else if (op = `LinTimes`) then mysplitlist (dest_binop op) tm
            else if (op = `LinPlus`) then mysplitlist (dest_binop op) tm
            else failwith ("Json_cll.Encode.prop: Unexpected operator - " ^ (string_of_term op))
          in
          
          let jargs = "args",Array (map prop args') in
          Object [ ("type", String op_string) ; jargs ]

      
      let term tm =
        let cll,chan = (rand o rator) tm,rand tm in
        Object [("channel", String (string_of_term chan));
	            ("cll", prop cll)]
             
    end
  module Decode =
    struct
      let rec prop j =
        let tbl = make_table (objekt j) in
        let op_string = String.lowercase (string (field tbl "type")) in
        if (op_string = "var") then mk_var (string (field tbl "name"),`:LinProp`)
        else
          let args = list prop (field tbl "args") in
          match op_string with
	        "neg" -> mk_comb (`NEG`,hd args)
          | "times" -> list_mk_binop `LinTimes` args
          | "plus" -> list_mk_binop `LinPlus` args
          | _ -> failwith ("Json_cll.Decode.prop: Unexpected operator - " ^ op_string)
               	
    
      let term decode_chan j =
        let tbl = make_table (objekt j) in
        let cll = prop (field tbl "cll")
        and channel = (decode_chan o string) (field tbl "channel") in
        mk_icomb (mk_comb (`LL`,cll),channel)
             
    end
  
  end ;;

module Json_act =
  struct
    open Json_type.Browse
    module Encode =
      struct
        let act (act:Action.t) =
          Object [
              ("act", String act.Action.act);
              ("larg", String act.Action.larg);
              ("lsel", String act.Action.lsel);
              ("rarg", String act.Action.rarg);
              ("rsel", String act.Action.rsel);
              ("res", String act.Action.res)]        

        let rec prov pt =
          let dest tp pt =
            match pt with
	        | Provleaf s -> failwith ""
	        | Provnode(op,l,r) -> if (op = tp) then l,r else failwith "" in
          let rec mysplitlist tp x =
            try let l,r = dest tp x in
	            let res = mysplitlist tp r in
                (l::res)
            with Failure _ -> [x] in
          
          match pt with
          | Provleaf s ->
	         (Object[
	              ("type", String "source");
	              ("name", String s)])
          | Provnode(op,l,r) ->
	         let args = mysplitlist op pt in
	         (Object[
	              ("type", String op);
	              ("args", Array (map prov args))])   

        let prov_entry (n,p) =
          Object [
              ("name", String n);
              ("prov", prov p)]

        let iprov_entry (n,p) =
          Object [
              ("term", Json_cll.Encode.prop n);
              ("prov", prov p)]

        let actionstate (st:Actionstate.t) =
          Object [
              ("label", String st.Actionstate.label);
              ("ctr", Int st.Actionstate.ctr);
              ("buffered", Array (map Json_cll.Encode.prop st.Actionstate.buffered));
              ("joined", Array (map Json_cll.Encode.term st.Actionstate.joined));
              ("iprov", Array (map iprov_entry st.Actionstate.iprov));
              ("prov", Array (map prov_entry st.Actionstate.prov))]
      end
      
    module Decode =
      struct
        let act j =
          let tbl = make_table (objekt j) in
          let act = string (field tbl "act")
          and larg = string (field tbl "larg")
          and lsel = string (field tbl "lsel")
          and rarg = string (field tbl "rarg")
          and rsel = string (field tbl "rsel")
          and res = string (field tbl "res") in
          Action.create act larg lsel rarg rsel res        

        let rec prov j =
          let rec list_mk_prov tp h args =
            match args with
	        | [] -> h
	        | ha::t -> Provnode(tp,h,list_mk_prov tp ha t) in
          
          let tbl = make_table (objekt j) in
          let op_string = String.lowercase (string (field tbl "type")) in
          if (op_string = "source") then Provleaf (string (field tbl "name"))
          else
            let args = list prov (field tbl "args") in
            list_mk_prov op_string (hd args) (tl args)
            
        let prov_entry j =
          let tbl = make_table (objekt j) in
          string (field tbl "name"), prov (field tbl "prov")           

        let iprov_entry j =
          let tbl = make_table (objekt j) in
          Json_cll.Decode.prop (field tbl "term"), prov (field tbl "prov")

        let actionstate decode_chan j =
          let tbl = make_table (objekt j) in
          let label = string (field tbl "label")
          and ctr = int (field tbl "ctr")
          and buffered = list Json_cll.Decode.prop (field tbl "buffered") 
          and joined = list (Json_cll.Decode.term decode_chan) (field tbl "joined")
          and iprov = list iprov_entry (field tbl "iprov")
          and prov = list prov_entry (field tbl "prov") in
          ({ Actionstate.label = label ;
             Actionstate.ctr = ctr ;
             Actionstate.metas = [] ;
             Actionstate.buffered = buffered ;
             Actionstate.joined = joined ;
             Actionstate.iprov = iprov ;
             Actionstate.prov = prov}:Actionstate.t)
      end
  end;;


module Json_proc_make (Process:Process_type) =
  struct
    open Json_type.Browse
    module Encode =
      struct
        let agent a = String (string_of_term a) (* TODO: Is that good enough? *)

        let iopair prop,chan =
          Object [("channel", String (string_of_term chan));
	              ("cll", Json_cll.Encode.prop prop)]

        let process (p:Process.t) =
          Object [
              ("name", String p.Process.name);
              ("inputs", Array (map iopair p.Process.inputs));
              ("output", iopair p.Process.output);
              ("proc", agent p.Process.proc);
              ("actions", Array (map Json_act.Encode.act p.Process.actions));
              ("copier", Bool p.Process.copier);
              ("intermediate", Bool p.Process.intermediate)]
          
      end

    module Decode =
      struct
        let term = Json_cll.Decode.term Process.mk_chan 
        let actionstate = Json_act.Decode.actionstate Process.mk_chan
						 
        let agent j = try (
                        let op,arg = (dest_comb o parse_term o string) j in
                        let tm = mk_icomb (op,Process.try_proc_type arg) in
                        let tinst = (map (fun x -> Process.chantp,x) o filter is_vartype o map type_of o frees) tm in
                        inst tinst tm
                      ) with Failure _ -> failwith "Json_composer.to_agent: failed to parse agent definition" 
        
        let iopair j =
          let tbl = make_table (objekt j) in
          let cll = Json_cll.Decode.prop (field tbl "cll")
          and channel:term = (Process.mk_chan o string) (field tbl "channel") in
          cll,channel	        

        let process j =
          let tbl = make_table (objekt j) in
          let name = string (field tbl "name")
          and inputs = list iopair (field tbl "inputs")
          and output = iopair (field tbl "output")
          and proc = agent (field tbl "proc")
          and actions = list Json_act.Decode.act (field tbl "actions")
          and copier = bool (field tbl "copier")
          and intermediate = bool (field tbl "intermediate") in
          ({Process.name = name; 
            Process.inputs = inputs ;
            Process.output = output ;
            Process.proc = proc ;
            Process.actions = actions ;
            Process.copier = copier ;
            Process.intermediate = intermediate ;
           }:Process.t)
      end
  end ;;


module Json_codec (Proc:Process_type) : Codec_type 
       with type proc = Proc.t 
        and type encodet = Json_type.json_type = 
  struct
    type encodet = Json_type.json_type
    type proc = Proc.t
    module Json_proc = Json_proc_make(Proc)
    module Encode =
      struct
        include Json_cll.Encode
        include Json_act.Encode
        include Json_proc.Encode      
      end
    module Decode =
      struct
        include Json_cll.Decode
        include Json_act.Decode
        include Json_proc.Decode      
      end  

  end ;;

