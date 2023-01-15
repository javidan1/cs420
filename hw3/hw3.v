(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)

Set Default Goal Selector "!".

Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
From Turing Require Import Lang.
From Turing Require Import Util.
Import LangNotations.
Import ListNotations.
Import Lang.Examples.
Open Scope lang_scope.
Open Scope char_scope.

(* ---------------------------------------------------------------------------*)




(**

Show that any word that is in L4 is either empty or starts with "a".

 *)
Theorem ex1:
  forall w, L4 w -> w = [] \/ exists w', w = "a" :: w'.
Proof.
  unfold L4.
  intros.
  destruct H.
  apply app_in_inv in H.
  destruct H as (w1, (w2, (h1, (h2, h3)))).
  induction x.

  - left.
    apply pow_zero_rw in h2.
    apply nil_in_inv in h2.
    apply pow_zero_rw in h3.
    apply nil_in_inv in h3.
    subst.
    reflexivity.

  - right.
    apply pow_char_cons_inv in h2.
    destruct h2.
    destruct H.
    apply pow_char_cons_inv in h3.
    destruct h3.
    destruct H1.
    subst.
    simpl.
    exists (x0 ++ "b" :: x1).
    reflexivity.
Qed.


(**

Show that the following word is accepted by the given language.

 *)
Theorem ex2:
  In ["a"; "b"; "b"; "a"] ("a" >> "b" * >> "a").
Proof.
  apply app_in with (w1:=["a"; "b"; "b"]) (w2:=["a"]).
  - apply app_in with (w1:=["a"]) (w2:=["b"; "b"]).
    * reflexivity.
    * apply pow_to_star with (n:=2).
      unfold In.
      apply pow_char_in.
    * reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(**

Show that the following word is rejected by the given language.

 *)
Theorem ex3:
  ~ In ["b"; "b"] ("a" >> "b" * >> "a").
Proof.
  intros H.
  apply app_in_inv in H.
  destruct H as (w1, (w2, (H1, (H2, H3)))).
  - apply char_in_inv in H3.
    subst.
    destruct w1.
    * inversion H1.
    * apply app_in_inv in H2.
      destruct H2 as (w2, (w3, (Hs, (Ha, Hb)))).
        ** apply char_in_inv in Ha.
           subst.
           inversion Hs.
           subst.
           inversion H1.
Qed.


(**

Show that the following language is empty.

 *)
Theorem ex4:
  "0" * >> {} == {}.
Proof.

Admitted.


(**

Rearrange the following terms. Hint use the distribution and absorption laws.

 *)
Theorem ex5:
  ("0" U Nil) >> ( "1" * ) == ( "0" >> "1" * ) U ( "1" * ).
Proof.
  rewrite <- app_union_distr_l.
  rewrite <- star_union_nil_rw.
  rewrite -> app_l_nil_rw.
  reflexivity.
Qed.

(**

Show that the following langue only accepts two words.

 *)
Theorem ex6:
  ("0" >> "1" U "1" >> "0") == fun w => (w = ["0"; "1"] \/ w = ["1"; "0"]).
Proof.
  split.
Admitted.

Theorem ex7:
  "b" >> ("a" U "b" U Nil) * >> Nil == "b" >> ("b" U "a") *.
Proof.
  rewrite -> app_r_nil_rw.
  rewrite -> union_sym_rw.
  rewrite -> star_union_nil_rw.
  rewrite -> union_sym_rw.
  reflexivity.
Qed.


Theorem ex8:
  (("b" >> ("a" U {}) ) U (Nil >> {} >> "c")* ) * == ("b" >> "a") *.
Proof.
  rewrite -> union_r_void_rw.
  rewrite -> app_l_nil_rw.
  rewrite -> app_l_void_rw.
  rewrite -> union_sym_rw.
  rewrite -> star_void_rw.
  rewrite -> star_union_nil_rw.
  reflexivity.
Qed.



