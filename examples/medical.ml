mk_llservice "ServiceASSGRequest" 
  `(' (NEG NOCONTR <> noc_sassg) 
    ^ ' (NEG NOREQ <> nor_sassg) 
    ^ ' (NEG CLIENT <> cl_sassg) 
    ^ ' (NEG SERVICE <> sv_sassg) 
    ^ ' (NEG ASSG <> assg_sassg) 
    ^ ' ((SR ** REQC ** CLIENT ** SERVICE ** ASSG) <> o_sassg))`;;
mk_llservice "ServiceDELEGRequest" 
  `(' (NEG NOCONTR <> noc_sdlg) 
    ^ ' (NEG NOREQ <> nor_sdlg) 
    ^ ' (NEG CLIENT <> cl_sdlg) 
    ^ ' (NEG SERVICE <> sv_sdlg) 
    ^ ' (NEG DELEG <> deleg_sassg) 
    ^ ' ((SR ** REQC ** CLIENT ** SERVICE ** DELEG) <> o_sdlg))`;;
mk_llservice "ContractAwarded" 
  `(' (NEG SR <> sr_ca) 
    ^ ' (NEG ACCC <> con_ca) 
    ^ ' (NEG PROVIDER <> pro_ca) 
    ^ ' ((OPENC ** PROVIDER) <> o_ca))`;;
mk_llservice "CollabDecision" 
  `(' (NEG SR <> sr_cd) 
    ^ ' (NEG REQC <> con_cd) 
    ^ ' (((SR ** ACCC ** PROVIDER) ++ REJECT) <> o_cd))`;;
mk_llservice "ServiceProvide" 
  `(' (NEG OPENC <> con_sp) 
    ^ ' (NEG SERVICE <> sv_sp) 
    ^ ' ((OPENC ** SRVCOMPL) <> o_sp))`;;
mk_llservice "OutcomeCheck" 
  `(' (NEG OPENC <> con_oc) 
    ^ ' (NEG SRVCOMPL <> sv_oc) 
    ^ ' (NEG ACTOR <> ac_oc) 
    ^ ' ((SRVDONE ** NOCONTR ** CLOSEDC) <> o_oc))`;;
mk_llservice "AssgResponsible" 
  `(' (NEG ASSG <> assg_ar) 
    ^ ' (NEG PROVIDER <> cl_ar) 
    ^ ' (ACTOR <> o_ar))`;;
mk_llservice "DelegResponsible" 
  `(' (NEG DELEG <> deleg_dr) 
    ^ ' (NEG CLIENT <> cl_dr) 
    ^ ' (ACTOR <> o_dr))`;;


gs `? G P . |-- G P`;;
e (LABEL_JOIN_TAC "CollabDecision" "ContractAwarded");;
e (LABEL_JOIN_TAC "ServiceASSGRequest" "ContractAwarded");;
e (LABEL_JOIN_TAC "ContractAwarded" "ServiceProvide");;
e (LABEL_JOIN_TAC "ServiceProvide" "AssgResponsible");;
e (LABEL_JOIN_TAC "AssgResponsible" "OutcomeCheck");;
ellma();;
store_service "AssignPattern";;
print_string (piviz_deploy "AssignPattern");;

top_thm();;
instantiate (top_inst()) `P:(num)Agent`;;
instantiate (top_inst ()) `(G:((num)LinTerm)multiset)`;;
let qqterm = it;;


gs `? G P . |-- G P`;;
e (LABEL_JOIN_TAC "CollabDecision" "ContractAwarded");;
e (LABEL_JOIN_TAC "ServiceDELEGRequest" "ContractAwarded");;
e (LABEL_JOIN_TAC "ContractAwarded" "ServiceProvide");;
e (LABEL_JOIN_TAC "ServiceProvide" "DelegResponsible");;
e (LABEL_JOIN_TAC "DelegResponsible" "OutcomeCheck");;
ellma();;
top_thm();;
instantiate ((snd o fst3 o hd o p) ()) `P:(num)Agent`;;
instantiate ((snd o fst3 o hd o p) ()) `(G:((num)LinTerm)multiset)`;;
let qqterm = it;;



(* ASSG *)

(^ z145)(({(^ z100)(({(^ z52)(({(^ z30)(({(ServiceASSGRequest(assg,assg_sassg,cl_sassg,client,noc_sassg,nor_sassg,o_sassg,reqc,service,sr,sv_sassg))}[o_sassg>z30] | {z29(sr_cd, z28).z28(con_cd, buf20).(^ y4, b20)('z20<y4, b20>.((^ z6)(({(CollabDecision(accc,con_cd,o_cd,o_cd_x,o_cd_y,provider,sr,sr_cd))}[o_cd>z6] | {(^ u4, v4)('x4<u4, v4>.(u4(z3).(^ o_ca)(y4(up4, vp4).'up4<o_ca>.z3(sr_ca, z2).z2(con_ca, pro_ca).(ContractAwarded(con_ca,o_ca,openc,pro_ca,provider,sr_ca))) + v4(c4).(^ d4)(y4(uq4, vq4).'vq4<d4>.c4(a5).'d4<a5>.0)))}[x4>z6])) | buf20(x21, y21).(^ x22, y22)('b20<x22, y22>.(x21(a23).'x22<a23>.0 | y21(x24, y24).(^ x25, y25)('y22<x25, y25>.(x24(a26).'x25<a26>.0 | y24(a27).'y25<a27>.0))))))}[z29>z30]))}[z20>z52] | {z51(x36, z50).z50(buf48, z42).(^ b48, z40)('z48<b48, z40>.(buf48(a49).'b48<a49>.0 | z42(sv_sp, buf40).(^ y36, b40)('z40<y36, b40>.((^ u36, v36)('x36<u36, v36>.(u36(z35).(^ z33)(y36(up36, vp36).'up36<z33>.z35(con_sp, buf33).(^ o_sp, b33)('z33<o_sp, b33>.((ServiceProvide(con_sp,o_sp,openc,srvcompl,sv_sp)) | buf33(a34).'b33<a34>.0))) + v36(c36).(^ d36)(y36(uq36, vq36).'vq36<d36>.(^ x37, y37)('d36<x37, y37>.(sv_sp(a38).'x37<a38>.0 | c36(a39).'y37<a39>.0))))) | buf40(a41).'b40<a41>.0))))}[z51>z52]))}[z48>z100] | {z99(buf97, z78).(^ b97, y71)('z97<b97, y71>.(buf97(a98).'b97<a98>.0 | z78(x71, assg_ar).(^ u71, v71)('x71<u71, v71>.(u71(z66).(^ z61)(y71(up71, vp71).'up71<z61>.z66(buf61, cl_ar).(^ b61, o_ar)('z61<b61, o_ar>.(buf61(x62, y62).(^ x63, y63)('b61<x63, y63>.(x62(a64).'x63<a64>.0 | y62(a65).'y63<a65>.0)) | (AssgResponsible(actor,assg_ar,cl_ar,o_ar))))) + v71(c71).(^ d71)(y71(uq71, vq71).'vq71<d71>.(^ x72, y72)('d71<x72, y72>.(assg_ar(a73).'x72<a73>.0 | c71(x74, y74).(^ x75, y75)('y72<x75, y75>.(x74(a76).'x75<a76>.0 | y74(a77).'y75<a77>.0)))))))))}[z99>z100]))}[z97>z145] | {z144(buf142, x116).(^ b142, y116)('z142<b142, y116>.(buf142(a143).'b142<a143>.0 | (^ u116, v116)('x116<u116, v116>.(u116(z104).(^ o_oc)(y116(up116, vp116).'up116<o_oc>.z104(z103, ac_oc).z103(con_oc, sv_oc).(OutcomeCheck(ac_oc,closedc,con_oc,nocontr,o_oc,srvdone,sv_oc))) + v116(c116).(^ d116)(y116(uq116, vq116).'vq116<d116>.c116(x117, y117).(^ x118, y118)('d116<x118, y118>.(x117(a119).'x118<a119>.0 | y117(x120, y120).(^ x121, y121)('y118<x121, y121>.(x120(a122).'x121<a122>.0 | y120(a123).'y121<a123>.0)))))))))}[z144>z145]))






agent Composition () = (^ z145)(((^ z100)(((^ z52)(((^ z30)(((ServiceASSGRequest(assg,assg_sassg,cl_sassg,client,noc_sassg,nor_sassg,z30,reqc,service,sr,sv_sassg)) | z30(sr_cd, z28).z28(con_cd, buf20).(^ y4, b20)('z52<y4, b20>.((^ z6)(((CollabDecision(accc,con_cd,z6,o_cd_x,o_cd_y,provider,sr,sr_cd)) | (^ u4, v4)('z6<u4, v4>.(u4(z3).(^ o_ca)(y4(up4, vp4).'up4<o_ca>.z3(sr_ca, z2).z2(con_ca, pro_ca).(ContractAwarded(con_ca,o_ca,openc,pro_ca,provider,sr_ca))) + v4(c4).(^ d4)(y4(uq4, vq4).'vq4<d4>.c4(a5).'d4<a5>.0))))) | buf20(x21, y21).(^ x22, y22)('b20<x22, y22>.(x21(a23).'x22<a23>.0 | y21(x24, y24).(^ x25, y25)('y22<x25, y25>.(x24(a26).'x25<a26>.0 | y24(a27).'y25<a27>.0)))))))) | z52(x36, z50).z50(buf48, z42).(^ b48, z40)('z100<b48, z40>.(buf48(a49).'b48<a49>.0 | z42(sv_sp, buf40).(^ y36, b40)('z40<y36, b40>.((^ u36, v36)('x36<u36, v36>.(u36(z35).(^ z33)(y36(up36, vp36).'up36<z33>.z35(con_sp, buf33).(^ o_sp, b33)('z33<o_sp, b33>.((ServiceProvide(con_sp,o_sp,openc,srvcompl,sv_sp)) | buf33(a34).'b33<a34>.0))) + v36(c36).(^ d36)(y36(uq36, vq36).'vq36<d36>.(^ x37, y37)('d36<x37, y37>.(sv_sp(a38).'x37<a38>.0 | c36(a39).'y37<a39>.0))))) | buf40(a41).'b40<a41>.0)))))) | z100(buf97, z78).(^ b97, y71)('z145<b97, y71>.(buf97(a98).'b97<a98>.0 | z78(x71, assg_ar).(^ u71, v71)('x71<u71, v71>.(u71(z66).(^ z61)(y71(up71, vp71).'up71<z61>.z66(buf61, cl_ar).(^ b61, o_ar)('z61<b61, o_ar>.(buf61(x62, y62).(^ x63, y63)('b61<x63, y63>.(x62(a64).'x63<a64>.0 | y62(a65).'y63<a65>.0)) | (AssgResponsible(actor,assg_ar,cl_ar,o_ar))))) + v71(c71).(^ d71)(y71(uq71, vq71).'vq71<d71>.(^ x72, y72)('d71<x72, y72>.(assg_ar(a73).'x72<a73>.0 | c71(x74, y74).(^ x75, y75)('y72<x75, y75>.(x74(a76).'x75<a76>.0 | y74(a77).'y75<a77>.0))))))))))) | z145(buf142, x116).(^ b142, y116)('z142<b142, y116>.(buf142(a143).'b142<a143>.0 | (^ u116, v116)('x116<u116, v116>.(u116(z104).(^ o_oc)(y116(up116, vp116).'up116<o_oc>.z104(z103, ac_oc).z103(con_oc, sv_oc).(OutcomeCheck(ac_oc,closedc,con_oc,nocontr,o_oc,srvdone,sv_oc))) + v116(c116).(^ d116)(y116(uq116, vq116).'vq116<d116>.c116(x117, y117).(^ x118, y118)('d116<x118, y118>.(x117(a119).'x118<a119>.0 | y117(x120, y120).(^ x121, y121)('y118<x121, y121>.(x120(a122).'x121<a122>.0 | y120(a123).'y121<a123>.0)))))))))))



agent Request() = 'assg_sassg<assg>.0 | 'cl_sassg<client>.0 | 'noc_sassg<nocontr>.0 | 'nor_sassg<noreq>.0 | 'sv_sassg<service>.0

agent Response() = (^ y100_u, y100_v)('y100<y100_u, y100_v>.(y100_u(y100_x).y100_x(y100_x_a, y100_x_b).(y100_x_a(y100_x_a_a, y100_x_a_b).(y100_x_a_a(srvdone).0 | y100_x_a_b(y100_x_a_b_a, y100_x_a_b_b).(y100_x_a_b_a(nocontr).0 | y100_x_a_b_b(closedc).0)) | y100_x_b(provider).0) + y100_v(y100_y).y100_y(y100_y_a, y100_y_b).(y100_y_a(y100_y_a_a, y100_y_a_b).(y100_y_a_a(srvdone).0 | y100_y_a_b(y100_y_a_b_a, y100_y_a_b_b).(y100_y_a_b_a(nocontr).0 | y100_y_a_b_b(closedc).0)) | y100_y_b(provider).0)))

exec agent Main() = Request() | Composition() | Response()














'y100<y100_u#1, y100_v#2>.(y100_u#1(y100_x).y100_x(y100_x_a, y100_x_b).(y100_x_a(y100_x_a_a, y100_x_a_b).(y100_x_a_a(srvdone).0 | y100_x_a_b(y100_x_a_b_a, y100_x_a_b_b).(y100_x_a_b_a(nocontr).0 | y100_x_a_b_b(closedc).0)) | y100_x_b(provider).0) + y100_v#2(y100_y).y100_y(y100_y_a, y100_y_b).(y100_y_a(y100_y_a_a, y100_y_a_b).(y100_y_a_a(srvdone).0 | y100_y_a_b(y100_y_a_b_a, y100_y_a_b_b).(y100_y_a_b_a(nocontr).0 | y100_y_a_b_b(closedc).0)) | y100_y_b(provider).0))
 |   z145#0(buf142, x116).(^b142, y116) 'z142<b142, y116>.(buf142(a143).'b142<a143>.0 | (^u116, v116) 'x116<u116, v116>.(u116(z104).(^o_oc) y116(up116, vp116).'up116<o_oc>.z104(z103, ac_oc).z103(con_oc, sv_oc).OutcomeCheck(ac_oc, closedc, con_oc, nocontr, o_oc, srvdone, sv_oc) + v116(c116).(^d116) y116(uq116, vq116).'vq116<d116>.c116(x117, y117).(^x118, y118) 'd116<x118, y118>.(x117(a119).'x118<a119>.0 | y117(x120, y120).(^x121, y121) 'y118<x121, y121>.(x120(a122).'x121<a122>.0 | y120(a123).'y121<a123>.0))))
 |   z100#3(buf97, z78).(^b97, y71) 'z145#0<b97, y71>.(buf97(a98).'b97<a98>.0 | z78(x71, assg_ar).(^u71, v71) 'x71<u71, v71>.(u71(z66).(^z61) y71(up71, vp71).'up71<z61>.z66(buf61, cl_ar).(^b61, o_ar) 'z61<b61, o_ar>.(buf61(x62, y62).(^x63, y63) 'b61<x63, y63>.(x62(a64).'x63<a64>.0 | y62(a65).'y63<a65>.0) | AssgResponsible(actor, assg_ar, cl_ar, o_ar)) + v71(c71).(^d71) y71(uq71, vq71).'vq71<d71>.(^x72, y72) 'd71<x72, y72>.(assg_ar(a73).'x72<a73>.0 | c71(x74, y74).(^x75, y75) 'y72<x75, y75>.(x74(a76).'x75<a76>.0 | y74(a77).'y75<a77>.0))))
 |   z52#4(x36, z50).z50(buf48, z42).(^b48, z40) 'z100#3<b48, z40>.(buf48(a49).'b48<a49>.0 | z42(sv_sp, buf40).(^y36, b40) 'z40<y36, b40>.((^u36, v36) 'x36<u36, v36>.(u36(z35).(^z33) y36(up36, vp36).'up36<z33>.z35(con_sp, buf33).(^o_sp, b33) 'z33<o_sp, b33>.(ServiceProvide(con_sp, o_sp, openc, srvcompl, sv_sp) | buf33(a34).'b33<a34>.0) + v36(c36).(^d36) y36(uq36, vq36).'vq36<d36>.(^x37, y37) 'd36<x37, y37>.(sv_sp(a38).'x37<a38>.0 | c36(a39).'y37<a39>.0)) | buf40(a41).'b40<a41>.0))
 |   z30#5(sr_cd, z28).z28(con_cd, buf20).(^y4, b20) 'z52#4<y4, b20>.((^z6) (CollabDecision(accc, con_cd, z6, o_cd_x, o_cd_y, provider, sr, sr_cd) | (^u4, v4) 'z6<u4, v4>.(u4(z3).(^o_ca) y4(up4, vp4).'up4<o_ca>.z3(sr_ca, z2).z2(con_ca, pro_ca).ContractAwarded(con_ca, o_ca, openc, pro_ca, provider, sr_ca) + v4(c4).(^d4) y4(uq4, vq4).'vq4<d4>.c4(a5).'d4<a5>.0)) | buf20(x21, y21).(^x22, y22) 'b20<x22, y22>.(x21(a23).'x22<a23>.0 | y21(x24, y24).(^x25, y25) 'y22<x25, y25>.(x24(a26).'x25<a26>.0 | y24(a27).'y25<a27>.0)))
 |   'z30#5<o_sassg_a#9, o_sassg_b#10>.('o_sassg_a#9<sr>.0 | (^o_sassg_b_a, o_sassg_b_b) 'o_sassg_b#10<o_sassg_b_a, o_sassg_b_b>.('o_sassg_b_a<reqc>.0 | (^o_sassg_b_b_a, o_sassg_b_b_b) 'o_sassg_b_b<o_sassg_b_b_a, o_sassg_b_b_b>.('o_sassg_b_b_a<client>.0 | (^o_sassg_b_b_b_a, o_sassg_b_b_b_b) 'o_sassg_b_b_b<o_sassg_b_b_b_a, o_sassg_b_b_b_b>.('o_sassg_b_b_b_a<service>.0 | 'o_sassg_b_b_b_b<assg>.0))))







'y100<y100_u#1, y100_v#2>.(y100_u#1(y100_x).y100_x(y100_x_a, y100_x_b).(y100_x_a(y100_x_a_a, y100_x_a_b).(y100_x_a_a(srvdone).0 | y100_x_a_b(y100_x_a_b_a, y100_x_a_b_b).(y100_x_a_b_a(nocontr).0 | y100_x_a_b_b(closedc).0)) | y100_x_b(provider).0) + y100_v#2(y100_y).y100_y(y100_y_a, y100_y_b).(y100_y_a(y100_y_a_a, y100_y_a_b).(y100_y_a_a(srvdone).0 | y100_y_a_b(y100_y_a_b_a, y100_y_a_b_b).(y100_y_a_b_a(nocontr).0 | y100_y_a_b_b(closedc).0)) | y100_y_b(provider).0))
 |   'o_sassg_a#9<sr>.0
 |   (u4#19(z3).(^o_ca) y4#13(up4, vp4).'up4<o_ca>.z3(sr_ca, z2).z2(con_ca, pro_ca).ContractAwarded(con_ca, o_ca, openc, pro_ca, provider, sr_ca) + v4#20(c4).(^d4) y4#13(uq4, vq4).'vq4<d4>.c4(a5).'d4<a5>.0)
 |   o_sassg_a#9(sr#18).0
 |   ('o_cd_u#21<o_cd_x>.(^o_cd_x_a, o_cd_x_b) 'o_cd_x<o_cd_x_a, o_cd_x_b>.('o_cd_x_a<sr>.0 | (^o_cd_x_b_a, o_cd_x_b_b) 'o_cd_x_b<o_cd_x_b_a, o_cd_x_b_b>.('o_cd_x_b_a<accc>.0 | 'o_cd_x_b_b<provider>.0)) + 'o_cd_v#22<o_cd_y>.(^o_cd_y_a, o_cd_y_b) 'o_cd_y<o_cd_y_a, o_cd_y_b>.('o_cd_y_a<sr>.0 | (^o_cd_y_b_a, o_cd_y_b_b) 'o_cd_y_b<o_cd_y_b_a, o_cd_y_b_b>.('o_cd_y_b_a<accc>.0 | 'o_cd_y_b_b<provider>.0)))
 |   'o_sassg_b_b_a#15<client>.0
 |   'o_sassg_b_b_b#16<o_sassg_b_b_b_a#25, o_sassg_b_b_b_b#26>.('o_sassg_b_b_b_a#25<service>.0 | 'o_sassg_b_b_b_b#26<assg>.0)
 |   o_sassg_b_b_a#15(a23).'x22#23<a23>.0
 |   o_sassg_b_b_b#16(x24, y24).(^x25, y25) 'y22#24<x25, y25>.(x24(a26).'x25<a26>.0 | y24(a27).'y25<a27>.0)
 |   x22#23(a49).'b48#27<a49>.0
 |   y22#24(sv_sp, buf40).(^y36, b40) 'z40#28<y36, b40>.((^u36, v36) 'y4#13<u36, v36>.(u36(z35).(^z33) y36(up36, vp36).'up36<z33>.z35(con_sp, buf33).(^o_sp, b33) 'z33<o_sp, b33>.(ServiceProvide(con_sp, o_sp, openc, srvcompl, sv_sp) | buf33(a34).'b33<a34>.0) + v36(c36).(^d36) y36(uq36, vq36).'vq36<d36>.(^x37, y37) 'd36<x37, y37>.(sv_sp(a38).'x37<a38>.0 | c36(a39).'y37<a39>.0)) | buf40(a41).'b40<a41>.0)
 |   b48#27(a98).'b97#29<a98>.0
 |   z40#28(x71, assg_ar).(^u71, v71) 'x71<u71, v71>.(u71(z66).(^z61) y71#30(up71, vp71).'up71<z61>.z66(buf61, cl_ar).(^b61, o_ar) 'z61<b61, o_ar>.(buf61(x62, y62).(^x63, y63) 'b61<x63, y63>.(x62(a64).'x63<a64>.0 | y62(a65).'y63<a65>.0) | AssgResponsible(actor, assg_ar, cl_ar, o_ar)) + v71(c71).(^d71) y71#30(uq71, vq71).'vq71<d71>.(^x72, y72) 'd71<x72, y72>.(assg_ar(a73).'x72<a73>.0 | c71(x74, y74).(^x75, y75) 'y72<x75, y75>.(x74(a76).'x75<a76>.0 | y74(a77).'y75<a77>.0)))
 |   'z142<b142#31, y116#32>.(b97#29(a143).'b142#31<a143>.0 | (^u116, v116) 'y71#30<u116, v116>.(u116(z104).(^o_oc) y116#32(up116, vp116).'up116<o_oc>.z104(z103, ac_oc).z103(con_oc, sv_oc).OutcomeCheck(ac_oc, closedc, con_oc, nocontr, o_oc, srvdone, sv_oc) + v116(c116).(^d116) y116#32(uq116, vq116).'vq116<d116>.c116(x117, y117).(^x118, y118) 'd116<x118, y118>.(x117(a119).'x118<a119>.0 | y117(x120, y120).(^x121, y121) 'y118<x121, y121>.(x120(a122).'x121<a122>.0 | y120(a123).'y121<a123>.0))))




(u4#17(z3).(^o_ca) y4#11(up4, vp4).'up4<o_ca>.z3(sr_ca, z2).z2(con_ca, pro_ca).ContractAwarded(con_ca, o_ca, openc, pro_ca, provider, sr_ca) + v4#18(c4).(^d4) y4#11(uq4, vq4).'vq4<d4>.c4(a5).'d4<a5>.0)
 |   ('o_cd_u#19<o_cd_x>.(^o_cd_x_a, o_cd_x_b) 'o_cd_x<o_cd_x_a, o_cd_x_b>.('o_cd_x_a<sr>.0 | (^o_cd_x_b_a, o_cd_x_b_b) 'o_cd_x_b<o_cd_x_b_a, o_cd_x_b_b>.('o_cd_x_b_a<accc>.0 | 'o_cd_x_b_b<provider>.0)) + 'o_cd_v#20<o_cd_y>.(^o_cd_y_a, o_cd_y_b) 'o_cd_y<o_cd_y_a, o_cd_y_b>.('o_cd_y_a<sr>.0 | (^o_cd_y_b_a, o_cd_y_b_b) 'o_cd_y_b<o_cd_y_b_a, o_cd_y_b_b>.('o_cd_y_b_a<accc>.0 | 'o_cd_y_b_b<provider>.0)))
 |   'y71#28<u116#31, v116#32>.(u116#31(z104).(^o_oc) y116#30(up116, vp116).'up116<o_oc>.z104(z103, ac_oc).z103(con_oc, sv_oc).OutcomeCheck(ac_oc, closedc, con_oc, nocontr, o_oc, srvdone, sv_oc) + v116#32(c116).(^d116) y116#30(uq116, vq116).'vq116<d116>.c116(x117, y117).(^x118, y118) 'd116<x118, y118>.(x117(a119).'x118<a119>.0 | y117(x120, y120).(^x121, y121) 'y118<x121, y121>.(x120(a122).'x121<a122>.0 | y120(a123).'y121<a123>.0)))
 |   'y116#30<z142_b_u#33, z142_b_v#34>.(z142_b_u#33(z142_b_x).z142_b_x(z142_b_x_a, z142_b_x_b).(z142_b_x_a(srvdone).0 | z142_b_x_b(z142_b_x_b_a, z142_b_x_b_b).(z142_b_x_b_a(nocontr).0 | z142_b_x_b_b(closedc).0)) + z142_b_v#34(z142_b_y).z142_b_y(z142_b_y_a, z142_b_y_b).(z142_b_y_a(srvdone).0 | z142_b_y_b(z142_b_y_b_a, z142_b_y_b_b).(z142_b_y_b_a(nocontr).0 | z142_b_y_b_b(closedc).0)))
 |   'y36#37<u71#39, v71#40>.(u71#39(z66).(^z61) y71#28(up71, vp71).'up71<z61>.z66(buf61, cl_ar).(^b61, o_ar) 'z61<b61, o_ar>.(buf61(x62, y62).(^x63, y63) 'b61<x63, y63>.(x62(a64).'x63<a64>.0 | y62(a65).'y63<a65>.0) | AssgResponsible(actor, b40#38, cl_ar, o_ar)) + v71#40(c71).(^d71) y71#28(uq71, vq71).'vq71<d71>.(^x72, y72) 'd71<x72, y72>.(b40#38(a73).'x72<a73>.0 | c71(x74, y74).(^x75, y75) 'y72<x75, y75>.(x74(a76).'x75<a76>.0 | y74(a77).'y75<a77>.0)))
 |   'y4#11<u36#41, v36#42>.(u36#41(z35).(^z33) y36#37(up36, vp36).'up36<z33>.z35(con_sp, buf33).(^o_sp, b33) 'z33<o_sp, b33>.(ServiceProvide(con_sp, o_sp, openc, srvcompl, x25#35) | buf33(a34).'b33<a34>.0) + v36#42(c36).(^d36) y36#37(uq36, vq36).'vq36<d36>.(^x37, y37) 'd36<x37, y37>.(x25#35(a38).'x37<a38>.0 | c36(a39).'y37<a39>.0))
 |   'b40#38<assg>.0
 |   'x25#35<service>.0






z142(z142_a, z142_b).(z142_a(client).0 | (^z142_b_u, z142_b_v) 'z142_b<z142_b_u, z142_b_v>.(z142_b_u(z142_b_x).z142_b_x(z142_b_x_a, z142_b_x_b).(z142_b_x_a(srvdone).0 | z142_b_x_b(z142_b_x_b_a, z142_b_x_b_b).(z142_b_x_b_a(nocontr).0 | z142_b_x_b_b(closedc).0)) + z142_b_v(z142_b_y).z142_b_y(z142_b_y_a, z142_b_y_b).(z142_b_y_a(srvdone).0 | z142_b_y_b(z142_b_y_b_a, z142_b_y_b_b).(z142_b_y_b_a(nocontr).0 | z142_b_y_b_b(closedc).0))))
 |   'assg_sassg<assg>.0
 |   'cl_sassg<client>.0
 |   'noc_sassg<nocontr>.0
 |   'nor_sassg<noreq>.0
 |   'sv_sassg<service>.0
 |   z145#0(buf142, x116).(^b142, y116) 'z142<b142, y116>.(buf142(a143).'b142<a143>.0 | (^u116, v116) 'x116<u116, v116>.(u116(z104).(^o_oc) y116(up116, vp116).'up116<o_oc>.z104(z103, ac_oc).z103(con_oc, sv_oc).OutcomeCheck(ac_oc, closedc, con_oc, nocontr, o_oc, srvdone, sv_oc) + v116(c116).(^d116) y116(uq116, vq116).'vq116<d116>.c116(x117, y117).(^x118, y118) 'd116<x118, y118>.(x117(a119).'x118<a119>.0 | y117(x120, y120).(^x121, y121) 'y118<x121, y121>.(x120(a122).'x121<a122>.0 | y120(a123).'y121<a123>.0))))
 |   z100#1(buf97, z78).(^b97, y71) 'z145#0<b97, y71>.(buf97(a98).'b97<a98>.0 | z78(x71, assg_ar).(^u71, v71) 'x71<u71, v71>.(u71(z66).(^z61) y71(up71, vp71).'up71<z61>.z66(buf61, cl_ar).(^b61, o_ar) 'z61<b61, o_ar>.(buf61(x62, y62).(^x63, y63) 'b61<x63, y63>.(x62(a64).'x63<a64>.0 | y62(a65).'y63<a65>.0) | AssgResponsible(actor, assg_ar, cl_ar, o_ar)) + v71(c71).(^d71) y71(uq71, vq71).'vq71<d71>.(^x72, y72) 'd71<x72, y72>.(assg_ar(a73).'x72<a73>.0 | c71(x74, y74).(^x75, y75) 'y72<x75, y75>.(x74(a76).'x75<a76>.0 | y74(a77).'y75<a77>.0))))
 |   noc_sassg(nocontr).0
 |   nor_sassg(noreq).0
 |   cl_sassg(client#4).0
 |   sv_sassg(service#5).0
 |   assg_sassg(assg#6).0
 |   'o_sassg_a#7<sr>.0
 |   'o_sassg_b_a#9<reqc>.0
 |   'o_sassg_b_b#10<o_sassg_b_b_a#13, o_sassg_b_b_b#14>.('o_sassg_b_b_a#13<client>.0 | (^o_sassg_b_b_b_a, o_sassg_b_b_b_b) 'o_sassg_b_b_b#14<o_sassg_b_b_b_a, o_sassg_b_b_b_b>.('o_sassg_b_b_b_a<service>.0 | 'o_sassg_b_b_b_b<assg>.0))
 |   b20#12(buf48, z42).(^b48, z40) 'z100#1<b48, z40>.(buf48(a49).'b48<a49>.0 | z42(sv_sp, buf40).(^y36, b40) 'z40<y36, b40>.((^u36, v36) 'y4#11<u36, v36>.(u36(z35).(^z33) y36(up36, vp36).'up36<z33>.z35(con_sp, buf33).(^o_sp, b33) 'z33<o_sp, b33>.(ServiceProvide(con_sp, o_sp, openc, srvcompl, sv_sp) | buf33(a34).'b33<a34>.0) + v36(c36).(^d36) y36(uq36, vq36).'vq36<d36>.(^x37, y37) 'd36<x37, y37>.(sv_sp(a38).'x37<a38>.0 | c36(a39).'y37<a39>.0)) | buf40(a41).'b40<a41>.0))
 |   o_sassg_b_b#10(x21, y21).(^x22, y22) 'b20#12<x22, y22>.(x21(a23).'x22<a23>.0 | y21(x24, y24).(^x25, y25) 'y22<x25, y25>.(x24(a26).'x25<a26>.0 | y24(a27).'y25<a27>.0))
 |   'z6#15<u4#17, v4#18>.(u4#17(z3).(^o_ca) y4#11(up4, vp4).'up4<o_ca>.z3(sr_ca, z2).z2(con_ca, pro_ca).ContractAwarded(con_ca, o_ca, openc, pro_ca, provider, sr_ca) + v4#18(c4).(^d4) y4#11(uq4, vq4).'vq4<d4>.c4(a5).'d4<a5>.0)
 |   o_sassg_a#7(sr#16).0
 |   o_sassg_b_a#9(reqc).0
 |   z6#15(o_cd_u, o_cd_v).('o_cd_u#19<o_cd_x>.(^o_cd_x_a, o_cd_x_b) 'o_cd_x<o_cd_x_a, o_cd_x_b>.('o_cd_x_a<sr>.0 | (^o_cd_x_b_a, o_cd_x_b_b) 'o_cd_x_b<o_cd_x_b_a, o_cd_x_b_b>.('o_cd_x_b_a<accc>.0 | 'o_cd_x_b_b<provider>.0)) + 'o_cd_v#20<o_cd_y>.(^o_cd_y_a, o_cd_y_b) 'o_cd_y<o_cd_y_a, o_cd_y_b>.('o_cd_y_a<sr>.0 | (^o_cd_y_b_a, o_cd_y_b_b) 'o_cd_y_b<o_cd_y_b_a, o_cd_y_b_b>.('o_cd_y_b_a<accc>.0 | 'o_cd_y_b_b<provider>.0)))





z142(z142_a, z142_b).(z142_a(client).0 | (^z142_b_u, z142_b_v) 'z142_b<z142_b_u, z142_b_v>.(z142_b_u(z142_b_x).z142_b_x(z142_b_x_a, z142_b_x_b).(z142_b_x_a(srvdone).0 | z142_b_x_b(z142_b_x_b_a, z142_b_x_b_b).(z142_b_x_b_a(nocontr).0 | z142_b_x_b_b(closedc).0)) + z142_b_v(z142_b_y).z142_b_y(z142_b_y_a, z142_b_y_b).(z142_b_y_a(srvdone).0 | z142_b_y_b(z142_b_y_b_a, z142_b_y_b_b).(z142_b_y_b_a(nocontr).0 | z142_b_y_b_b(closedc).0))))
 |   z145#0(buf142, x116).(^b142, y116) 'z142<b142, y116>.(buf142(a143).'b142<a143>.0 | (^u116, v116) 'x116<u116, v116>.(u116(z104).(^o_oc) y116(up116, vp116).'up116<o_oc>.z104(z103, ac_oc).z103(con_oc, sv_oc).OutcomeCheck(ac_oc, closedc, con_oc, nocontr, o_oc, srvdone, sv_oc) + v116(c116).(^d116) y116(uq116, vq116).'vq116<d116>.c116(x117, y117).(^x118, y118) 'd116<x118, y118>.(x117(a119).'x118<a119>.0 | y117(x120, y120).(^x121, y121) 'y118<x121, y121>.(x120(a122).'x121<a122>.0 | y120(a123).'y121<a123>.0))))
 |   z100#1(buf97, z78).(^b97, y71) 'z145#0<b97, y71>.(buf97(a98).'b97<a98>.0 | z78(x71, assg_ar).(^u71, v71) 'x71<u71, v71>.(u71(z66).(^z61) y71(up71, vp71).'up71<z61>.z66(buf61, cl_ar).(^b61, o_ar) 'z61<b61, o_ar>.(buf61(x62, y62).(^x63, y63) 'b61<x63, y63>.(x62(a64).'x63<a64>.0 | y62(a65).'y63<a65>.0) | AssgResponsible(actor, assg_ar, cl_ar, o_ar)) + v71(c71).(^d71) y71(uq71, vq71).'vq71<d71>.(^x72, y72) 'd71<x72, y72>.(assg_ar(a73).'x72<a73>.0 | c71(x74, y74).(^x75, y75) 'y72<x75, y75>.(x74(a76).'x75<a76>.0 | y74(a77).'y75<a77>.0))))
 |   'o_sassg_b_b#10<o_sassg_b_b_a#13, o_sassg_b_b_b#14>.('o_sassg_b_b_a#13<client>.0 | (^o_sassg_b_b_b_a, o_sassg_b_b_b_b) 'o_sassg_b_b_b#14<o_sassg_b_b_b_a, o_sassg_b_b_b_b>.('o_sassg_b_b_b_a<service>.0 | 'o_sassg_b_b_b_b<assg>.0))
 |   b20#12(buf48, z42).(^b48, z40) 'z100#1<b48, z40>.(buf48(a49).'b48<a49>.0 | z42(sv_sp, buf40).(^y36, b40) 'z40<y36, b40>.((^u36, v36) 'y4#11<u36, v36>.(u36(z35).(^z33) y36(up36, vp36).'up36<z33>.z35(con_sp, buf33).(^o_sp, b33) 'z33<o_sp, b33>.(ServiceProvide(con_sp, o_sp, openc, srvcompl, sv_sp) | buf33(a34).'b33<a34>.0) + v36(c36).(^d36) y36(uq36, vq36).'vq36<d36>.(^x37, y37) 'd36<x37, y37>.(sv_sp(a38).'x37<a38>.0 | c36(a39).'y37<a39>.0)) | buf40(a41).'b40<a41>.0))
 |   o_sassg_b_b#10(x21, y21).(^x22, y22) 'b20#12<x22, y22>.(x21(a23).'x22<a23>.0 | y21(x24, y24).(^x25, y25) 'y22<x25, y25>.(x24(a26).'x25<a26>.0 | y24(a27).'y25<a27>.0))
 |   'z6#15<u4#17, v4#18>.(u4#17(z3).(^o_ca) y4#11(up4, vp4).'up4<o_ca>.z3(sr_ca, z2).z2(con_ca, pro_ca).ContractAwarded(con_ca, o_ca, openc, pro_ca, provider, sr_ca) + v4#18(c4).(^d4) y4#11(uq4, vq4).'vq4<d4>.c4(a5).'d4<a5>.0)
 |   z6#15(o_cd_u, o_cd_v).('o_cd_u#19<o_cd_x>.(^o_cd_x_a, o_cd_x_b) 'o_cd_x<o_cd_x_a, o_cd_x_b>.('o_cd_x_a<sr>.0 | (^o_cd_x_b_a, o_cd_x_b_b) 'o_cd_x_b<o_cd_x_b_a, o_cd_x_b_b>.('o_cd_x_b_a<accc>.0 | 'o_cd_x_b_b<provider>.0)) + 'o_cd_v#20<o_cd_y>.(^o_cd_y_a, o_cd_y_b) 'o_cd_y<o_cd_y_a, o_cd_y_b>.('o_cd_y_a<sr>.0 | (^o_cd_y_b_a, o_cd_y_b_b) 'o_cd_y_b<o_cd_y_b_a, o_cd_y_b_b>.('o_cd_y_b_a<accc>.0 | 'o_cd_y_b_b<provider>.0)))



z142(z142_a, z142_b).(z142_a(client).0 | (^z142_b_u, z142_b_v) 'z142_b<z142_b_u, z142_b_v>.(z142_b_u(z142_b_x).z142_b_x(z142_b_x_a, z142_b_x_b).(z142_b_x_a(srvdone).0 | z142_b_x_b(z142_b_x_b_a, z142_b_x_b_b).(z142_b_x_b_a(nocontr).0 | z142_b_x_b_b(closedc).0)) + z142_b_v(z142_b_y).z142_b_y(z142_b_y_a, z142_b_y_b).(z142_b_y_a(srvdone).0 | z142_b_y_b(z142_b_y_b_a, z142_b_y_b_b).(z142_b_y_b_a(nocontr).0 | z142_b_y_b_b(closedc).0))))
 |   z145#0(buf142, x116).(^b142, y116) 'z142<b142, y116>.(buf142(a143).'b142<a143>.0 | (^u116, v116) 'x116<u116, v116>.(u116(z104).(^o_oc) y116(up116, vp116).'up116<o_oc>.z104(z103, ac_oc).z103(con_oc, sv_oc).OutcomeCheck(ac_oc, closedc, con_oc, nocontr, o_oc, srvdone, sv_oc) + v116(c116).(^d116) y116(uq116, vq116).'vq116<d116>.c116(x117, y117).(^x118, y118) 'd116<x118, y118>.(x117(a119).'x118<a119>.0 | y117(x120, y120).(^x121, y121) 'y118<x121, y121>.(x120(a122).'x121<a122>.0 | y120(a123).'y121<a123>.0))))
 |   z100#1(buf97, z78).(^b97, y71) 'z145#0<b97, y71>.(buf97(a98).'b97<a98>.0 | z78(x71, assg_ar).(^u71, v71) 'x71<u71, v71>.(u71(z66).(^z61) y71(up71, vp71).'up71<z61>.z66(buf61, cl_ar).(^b61, o_ar) 'z61<b61, o_ar>.(buf61(x62, y62).(^x63, y63) 'b61<x63, y63>.(x62(a64).'x63<a64>.0 | y62(a65).'y63<a65>.0) | AssgResponsible(actor, assg_ar, cl_ar, o_ar)) + v71(c71).(^d71) y71(uq71, vq71).'vq71<d71>.(^x72, y72) 'd71<x72, y72>.(assg_ar(a73).'x72<a73>.0 | c71(x74, y74).(^x75, y75) 'y72<x75, y75>.(x74(a76).'x75<a76>.0 | y74(a77).'y75<a77>.0))))
 |   'o_sassg_b_b#10<o_sassg_b_b_a#13, o_sassg_b_b_b#14>.('o_sassg_b_b_a#13<client>.0 | (^o_sassg_b_b_b_a, o_sassg_b_b_b_b) 'o_sassg_b_b_b#14<o_sassg_b_b_b_a, o_sassg_b_b_b_b>.('o_sassg_b_b_b_a<service>.0 | 'o_sassg_b_b_b_b<assg>.0))
 |   b20#12(buf48, z42).(^b48, z40) 'z100#1<b48, z40>.(buf48(a49).'b48<a49>.0 | z42(sv_sp, buf40).(^y36, b40) 'z40<y36, b40>.((^u36, v36) 'y4#11<u36, v36>.(u36(z35).(^z33) y36(up36, vp36).'up36<z33>.z35(con_sp, buf33).(^o_sp, b33) 'z33<o_sp, b33>.(ServiceProvide(con_sp, o_sp, openc, srvcompl, sv_sp) | buf33(a34).'b33<a34>.0) + v36(c36).(^d36) y36(uq36, vq36).'vq36<d36>.(^x37, y37) 'd36<x37, y37>.(sv_sp(a38).'x37<a38>.0 | c36(a39).'y37<a39>.0)) | buf40(a41).'b40<a41>.0))
 |   o_sassg_b_b#10(x21, y21).(^x22, y22) 'b20#12<x22, y22>.(x21(a23).'x22<a23>.0 | y21(x24, y24).(^x25, y25) 'y22<x25, y25>.(x24(a26).'x25<a26>.0 | y24(a27).'y25<a27>.0))
 |   'z6#15<u4#21, v4#22>.(u4#21(z3).(^o_ca) y4#11(up4, vp4).'up4<o_ca>.z3(sr_ca, z2).z2(con_ca, pro_ca).ContractAwarded(con_ca, o_ca, openc, pro_ca, provider, sr_ca) + v4#22(c4).(^d4) y4#11(uq4, vq4).'vq4<d4>.c4(a5).'d4<a5>.0)
 |   z6#15(o_cd_x#19, o_cd_y#20).('o_cd_x<o_cd_x#23>.(^o_cd_x_a, o_cd_x_b) 'o_cd_x#23<o_cd_x_a, o_cd_x_b>.('o_cd_x_a<sr>.0 | (^o_cd_x_b_a, o_cd_x_b_b) 'o_cd_x_b<o_cd_x_b_a, o_cd_x_b_b>.('o_cd_x_b_a<accc>.0 | 'o_cd_x_b_b<provider>.0)) + 'o_cd_y<o_cd_y#24>.(^o_cd_y_a, o_cd_y_b) 'o_cd_y#24<o_cd_y_a, o_cd_y_b>.('o_cd_y_a<sr>.0 | (^o_cd_y_b_a, o_cd_y_b_b) 'o_cd_y_b<o_cd_y_b_a, o_cd_y_b_b>.('o_cd_y_b_a<accc>.0 | 'o_cd_y_b_b<provider>.0)))









(piviz_string o linterm_to_pi o rhs o concl o (REWRITE_CONV [NEG_CLAUSES])) `(NEG 


let linnegterm_to_pi tm =
  let oper = `(<>):(LinProp->num->(num)LinTerm)` in
    try
      let (linprop,chan) = dest_binop oper tm in
	linprop_to_pi chan (mk_llneg linprop)
    with Failure _ -> failwith ("linterm_to_pi: " ^ string_of_term(tm));;
