(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Turing.Util.
Require Import Coq.Lists.List.
Import ListNotations.

(* ---------------------------------------------------------------------------*)




(**

Study the definition of [Turing.Util.pow] and [Turing.Util.pow1]
and then show that [Turing.Util.pow1] can be formulated in terms of
[Turing.Util.pow].
Material: https://gitlab.com/umb-svl/turing/blob/main/src/Util.v


 *)
Theorem ex1:
  forall (A:Type) (x:A) n, Util.pow [x] n = Util.pow1 x n.
Proof.
  intros.
  induction n as [|n' IH].
  - simpl. reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

(**

Study recursive definition of [List.In] and the inductive definition of
[List.Exists]. Then show that [List.In] can be formulated in terms
of [List.Exists].

Material: https://coq.inria.fr/library/Coq.Lists.List.html


 *)
Theorem ex2:
  forall (A:Type) (x:A) l, List.Exists (eq x) l <-> List.In x l.
Proof.
  intros.
  split.
  
  * intros.
    induction l.
    - simpl.
      inversion H.
    - inversion H.
      simpl.
      left.
      subst.
      reflexivity.
      simpl.
      right.
      apply IHl in H1.
      assumption.
  * intros H.
    induction l as [|y l' IH].
    - inversion H.
    - simpl.
      destruct H as [H|H].
      subst.
      left.
      reflexivity.
      right.
      apply IH.
      assumption.
Qed.

(**

Create an inductive relation that holds if, and only if, element 'x'
appears before element 'y' in the given list.
We can define `succ` inductively as follows:

                                (x, y) succ l
-----------------------R1     ------------------R2
(x, y) succ x :: y :: l       (x, y) succ z :: l

Rule R1 says that x succeeds y in the list that starts with [x, y].

Rule R2 says that if x succeeds y in list l then x succeeds y in a list
the list that results from adding z to list l.


 *)

Inductive succ {X : Type} (x : X) (y : X) : list X -> Prop :=
  | r1 : forall (l: list X), succ x y (x :: y :: l)
  | r2 : forall (z: X) (l: list X), succ x y l -> succ x y (z :: l).


Theorem succ1:
    (* Only one of the following propositions is provable.
       Replace 'False' by the only provable proposition and then prove it:
     1) succ 2 3 [1;2;3;4]
     2) ~ succ 2 3 [1;2;3;4]
     *)
    succ 2 3 [1;2;3;4].
Proof.
  apply r2.
  apply r1.
Qed.

Theorem succ2:
    (* Only one of the following propositions is provable.
       Replace 'False' by the only provable proposition and then prove it:
     1) succ 2 3 []
     2) ~ succ 2 3 []
     *)
    ~ succ 2 3 [].
Proof.
  intros h1.
  inversion h1.
Qed.


Theorem succ3:
    (* Only one of the following propositions is provable.
       Replace 'False' by the only provable proposition and then prove it:
     1) succ 2 4 [1;2;3;4]
     2) ~ succ 2 4 [1;2;3;4]
     *)
    ~ succ 2 4 [1;2;3;4].
Proof.
  intros h1.
  inversion h1.
  inversion H0.
  inversion H3.
  inversion H6.
  inversion H9.
Qed.


Theorem succ4:
  forall (X:Type) (x y : Type), succ x y [x;y].
Proof.
  intros.
  apply r1.
Qed.


Theorem ex3:
  forall (X:Type) (l1 l2:list X) (x y:X), succ x y (l1 ++ (x :: y :: l2)).
Proof.
  intros.
  induction l1, l2.
  - simpl.
    apply r1.
  - simpl.
    apply r1.
  - simpl.
    inversion IHl1.
    apply r2.
    apply r1.
    apply r2.
    apply r2.
    assumption.
  - simpl.
    inversion IHl1.
    apply r2.
    apply r1.
    apply r2.
    apply r2.
    assumption.
Qed.


Theorem ex4:
  forall (X:Type) (x y:X) (l:list X), succ x y l -> exists l1 l2, l1 ++ (x:: y:: l2) = l.
Proof.

Admitted.



