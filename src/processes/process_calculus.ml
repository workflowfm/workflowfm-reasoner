(* ========================================================================= *)
(* General module for a process calculus.                                    *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                           University of Edinburgh                         *)
(*                                    2013                                   *)
(* ========================================================================= *)

(* type cllversion = Mall | Cll | Foll;; *)
(*   val cllversion : cllversion   (* Version of CLL that can be used.          *) *)

module type Process_calculus =
sig
  val chantp : hol_type         (* The type of process calculus channels.    *)
  val tp : hol_type             (* The type of process calculus terms.       *)
  val fn : term                 (* A function for free names.                *)
  val bn : term                 (* A function for bound names.               *)
  val names : term              (* A function for all names.                 *)
  val fn_conv : conv            (* Conversions to reduce (evaluate) the      *)
  val bn_conv : conv            (* above three functions.                    *)
  val names_conv : conv
  val sub_conv : term list->conv (* Conversion to evaluate substitutions.    *)
                           (* The argument is a list of process definitions. *) 
  val sub_reduce : term -> term (* Reduction to evaluate substitutions       *)
                           (* informally but efficiently. *) 

  (* CLL correspondence: *)
  (* Identity: llid A x y m <-> |- x:A^, y:A for message m                   *)
  val llid : term->term->term->term->term
  (* Times: lltimes A B z x y P Q                                            *)
  val lltimes : term->term->term->term->term->term->term->term
  (* Par: llpar A B z x y P                                                  *)
  val llpar : term->term->term->term->term->term->term
  (* With : llwith A B z x y u v P Q                                         *)
  val llwith : term->term->term->term->term->term->term->term->term->term
  (* PlusL : llplusL A B z x u v P                                           *)
  val llplusL : term->term->term->term->term->term->term->term
  (* PlusR : llplusL A B z y u v Q                                           *)
  val llplusR : term->term->term->term->term->term->term->term
  (* Cut: llcut C z x y P Q                                                  *)
  val llcut : term->term->term->term->term->term->term

  val cll_to_proc : (term->string)->term->term
                                (* A converter from a CLL specification      *)
                                (* (multiset of CLL terms) to a corresponding*)
                                (* process calculus term.                    *)
  (*val fake_subs : term -> term  (* A method to calculate substitutions in a  *)
                                (* term efficiently using OCaml.             *)
  val prove_subs : term list->term->thm (* A method to prove the correctness *)
                                (* of the above calculation, given the defs  *)
   (* of any component agents.                  *)*)
end;;

 
