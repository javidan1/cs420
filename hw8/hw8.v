 (*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)

Set Default Goal Selector "!".

Require Import Turing.Turing.
Require Import Turing.LangRed.
Require Import Turing.LangDec.
Require Import Turing.Problems.
Require Import Coq.Logic.FunctionalExtensionality.

(* ---------------------------------------------------------------------------*)

(* ------------------------ BEGIN UTILITY RESULTS ---------------------- *)
Ltac invc H := inversion H; subst; clear H.

Lemma a_tm_rw:
  forall M i,
  A_tm <[ M, i ]> <->
  Run (Call M i) true.
Proof.
  unfold A_tm.
  intros.
  run_simpl_all.
  reflexivity.
Qed.

(* -------------------------- END OF UTILITY RESULTS ---------------------- *)



(**

=== Background information on map-reducibility ===

First recall the definition of <=m .

  Notation "<=m".

outputs:

  Notation "x <=m y" := (Reducible x y) (default interpretation)

So, what is reducible:

  Print Reducible.
  
Which says:

  Reducible = 
  fun A B : lang => exists f : input -> input, Reduction f A B
      : lang -> lang -> Prop

  Arguments Reducible A B

The important bit here is

    exists f, Reduction f A B

After `Print Reduction.` we recall that a reduction relates any input i
in A whenever f(i) is in B.

    forall w, A w <-> B (f w)

=== Actual proof ===

We will follow the proof of Theorem 5.28 (which redirects to
the proof of 5.22).

This kind of result needs to be proved directly (without the
aid of any theorem, so let us open up both definitions: 

    unfold Reducible, Reduction in *.

At this point, our proof state is as follows:

  H : exists f, forall w : input, A w <-> B (f w)
  H0 : Recognizable B
  ______________________________________(1/1)
  Recognizable A

Let us access the function that maps from A to B with `destruct H as (f, H)`,
and the program that recognizes B `destruct H0 as (M, H0)`.

The pen & paper proof says the following:

  On input w:
  1. Compute f(w).
  2. Run M on input f(w) and output whatever M outputs    

Our next tactics must be as follows to state that `(fun w => M (f w))`
recognizes A.

  exists (fun w => M (f w)).

In Coq, the high-level description can be state as `(fun w => M (f w))`,
since `M` is a program parameterized by an input and
"running M on input f(w)" amounts to calling `M` with argument `f(w)`,
written as `M (f w)`.

Now we apply the theorem `recognizes_def` to show that our program
recognizes language `A`. Following we introduce the input as `i`.

Our goal is now to show:

  Run (M (f i)) true <-> A i

Recall that `M` recognizes `B` (assumption `H0`) and
since `M (f i)` returns `true`, then we have `B (f i)`;
using `rewrite (recognizes_rw H0)` to obtain that fact in the goal
--- if we use `recognizes_rw` without a parameter Coq will complain
that it requires more information.

Finally, we can get rid of `A i` on the right-hand side of the equivalence
by using our map-reducibly assumption, with `rewrite H`.


 *)
Theorem red1:
  forall A B,
  A <=m B ->
  Recognizable B ->
  Recognizable A.
Proof.
  intros.
  unfold Reducible, Reduction in H.
  destruct H as (j, H).
  destruct H0 as (a, H0).
  exists (fun w => a (j w)).

  intros i.
  rewrite (recognizes_rw H0 (j i)).
  rewrite H.
  reflexivity.
Qed.

(**

We will follow the proof of Theorem 5.22.

First, we simplify `Decidable B` as in HW7 and we simplify our
remaining assumptions as suggested in `red1` until we get the following
proof state:

  H : forall w, A w <-> B (f w)
  H0 : Recognizes M B
  H1 : Decider M
  ______________________________________(1/1)
  Decidable A

We use the same program to decide `A` than we do in exercise `red1`.
Our proof state is now as follows

  Decides (fun w : input => M (f w)) A

We use theorem `decides_def` to continue. The first sub-goal proceeds
exactly like in exercise `red1`.

The second sub-goal we have the following relevant proof state:


  H1: Decider M
  ______________________________________(1/1)
  Decider (fun w : input => M (f w))

Recall that a decider halts for all inputs, `f w` is an arbitrary
input, thus `M` halts for `f w`. To conclude this goal,
write `unfold Decider in *` and use `H1` to conclude.


 *)
Theorem red2:
  forall A B,
  A <=m B ->
  Decidable B ->
  Decidable A.
Proof.
  unfold Decidable.
  intros.
  destruct H.
  destruct H0.
  exists (fun a => x0 (x a)).
  unfold Decides in *.
  destruct H0.
  split.

  - intro.
    rewrite (H i).
    rewrite (H0 (x i)).
    reflexivity.

  - intro.
    exact (H1 (x i)).
Qed.

(**

We will follow Prof. Peter Fejer's proof of problem 5.22:

  https://www.cs.umb.edu/~fejer/cs420/hw11s.pdf

Since our goal is an equivalence, we should start with

  split; intros.

Prof. Fejer's proof starts with:

1. "Let M be a Turing machine that recognizes A."

The first goal, first obtain the parameterized program `p` and
assumption `H` from `H: Recognizable A`.

We can convert a parametric program, such as `p`, into an abstract
Turing machine with

    destruct (code_of p) as (M, Hp).

This tactics yields an abstract Turing machine `M` and an
assumption `Hp : CodeOf p M` which establishes the equivalence
between the parametric function `p` and the abstract Turing machine `M`.

We now have all of the ingredient's to continue Prof. Fejer's proof:

2. "The function f defined by f (w) =〈M, w〉is a reduction from A to A_tm"

We can state that with the tactics:

  apply reducible_iff with (f:=fun i => <[ M, i ]>).

Finally, the last step of Prof. Fejer's proof is as follows:

3. "because it is obviously computable and we have"

    "w ∈ A iff M accepts w iff〈M, w〉 ∈ A_tm iff f (w) ∈ A_tm"
We can show that "〈M, w〉 ∈ A_tm iff M accepts w" with rewriting
with `a_tm_rw`, since "M accepts w" is represented in
Coq by `Run (Call M w) true`.

We know that `M` represents function `p`; we replace `Run (Call M w) true`
by `Run (p w) true` by rewriting with `(code_of_run_rw Hp)`.

Finally, since `p` recognizes `A` we can replace `Run (p w) true` by
`A w` using `(recognizes_rw H)`.

The second case is trivial knowing what we proved so far, if you recall
that `A_tm` is recognizable, given by a_tm_recognizable. Read Prof. Fejer's
proof to get the remaining details.


 *)
Theorem red3:
  forall A, Recognizable A <-> A <=m A_tm.
Proof.
  intro.
  split; intro.
  - destruct H.
    destruct (code_of x)  as (Z, Hp).
    set (a j := <[ Z, j]>).
    exists a.

    Check reducible_iff.
    split; intro.
    * unfold A_tm.
      compute.
      run_simpl_all.
      rewrite <- (H w) in H0.
      exact H0.
    * compute in H0.
      run_simpl_all.
      rewrite (H w) in H0.
      exact H0.

  - Check a_tm_recognizable.
    Search _ (Recognizable ?a).
    apply (reducible_recognizable A A_tm H).
    exact a_tm_recognizable.
Qed.

(**

Prove Corollary 5.29.

 *)
Theorem red4:
  forall A B,
  A <=m B ->
  ~ Recognizable A ->
  ~ Recognizable B.
Proof.
  intros.
  intro.
  apply H0.
  Check red1.
  apply (red1 A B H H1).
Qed.

(**

Let us solve Exercise 5.6 (solution in pp 242).

First, we simplify our assumptions to obtain.

  Hab : Reduction f A B
  Hbc : Reduction g B C
  ______________________________________(1/1)
  A <=m C

Now apply reducible_iff and with function `fun w => g (f w))`.

Next, we `unfold Reduction in *`.

The remainder should be trivial.


 *)
Theorem red5:
  forall A B C,
  A <=m B ->
  B <=m C ->
  A <=m C.
Proof.
  intros.
  destruct H0.
  destruct H.
  exists (fun z => x (x0 z)).

  intro.
  rewrite (H w).
  rewrite (H0 (x0 w)).
  reflexivity.
Qed.

(**

Use theorem `co_red_co_1`, which states

  If A <=m B, then compl A <=m compl B.

and what we have learned so far to prove the following statement.


 *)
Theorem red6:
  forall A B,
  A <=m B ->
  Recognizable (compl B) ->
  Recognizable (compl A).
Proof.
  unfold compl.
  intros.
  destruct H0.
  destruct H.
  exists (fun z => x (x0 z)).
  intro.
  destruct (H0 (x0 i)).
  split.
  - intro. intro.
    apply (H1 H3).
    apply H.
    exact H4.
  - intro.
    apply H2.
    intro.
    Check (H i).
    apply H3.
    rewrite (H i).
    exact H4.
Qed.

(**

Use the theorem `co_red_2`, which states:

  If A <=m compl B, then compl A <=m B

and what we have learned so far to prove the following statement.


 *)
Theorem red7:
  forall A B C,
  A <=m compl B ->
  compl B <=m C ->
  compl A <=m compl C.
Proof.

Admitted.

(**

Use theorem dec_rec_co_rec which we learned in class and two other
theorems we established in this assignment to conclude this proof.


 *)
Theorem red8:
  forall A,
  Decidable A ->
  A <=m compl A_tm.
Proof.
  intros.
  Check dec_rec_co_rec.
  destruct (dec_rec_co_rec A).
  destruct (H0 H).
  Search _ (Recognizable ?a).
  set (C := red3 (compl A)).
  Search _ (?b <=m compl ?a).
  apply co_red_1.
  rewrite <- C.
  exact H3.
Qed.

(**

Recall that A_tm is not recognizable (co_a_tm_not_recognizable).
Show that if A_tm is map-reducible to A, then the complement of A is not
recognizable. Hint use: co_red_co_1.


 *)
Theorem red9:
  forall A,
  A_tm <=m A ->
  ~ Recognizable (compl A).
Proof.
  intros.
  Check reducible_unrecognizable.
  apply (reducible_unrecognizable (compl A_tm) (compl A)).
  - Search _ (compl ?a <=m compl ?b).
    apply co_red_co_1.
    exact H.

  - Search _ (~ Recognizable ?a).
    exact co_a_tm_not_recognizable.
Qed.
(**

Show A_tm is *not* map-reducible to decidable languages.

Start the proof by assuming that A_tm <= A and then reach a contradiction,
which is obtained because we can show that compl A is recognizable and
compl A is unrecognizable.

1. We can prove that compl A is recognizable from A decidable.
2. We can prove that compl A is unrecognizable as follows:
   We have `compl A_tm <=m compl A_tm` and that `compl A_tm` is unrecognizable,
   so `compl A` is unrecognizable (which is one of the exercises prove here).
   The proof is similar to red9. 


 *)
Theorem red10:
  forall A,
  Decidable A ->
  ~ (A_tm <=m A).
Proof.
  intros.
  destruct (dec_rec_co_rec A).
  destruct (H0 H).
  intro.
  exact (red9 A H4 H3).
Qed.

(**

Show the following trivial statement.


 *)
Theorem red11:
  forall A,
  Decidable A ->
  A <=m A_tm.
Proof.
  intros.
  Check dec_rec_co_rec.
  destruct (dec_rec_co_rec A).
  destruct (H0 H).
  Search _ (Recognizable ?a).
  set (C := red3 A).
  rewrite <- C.
  exact H2.
Qed.


Theorem red12:
  forall A B,
  Recognizable A ->
  A_tm <=m B ->
  A <=m B.
Proof.

Admitted.

(**

Which language satisfies the following statement?
Ask for a hint if you are unsure. 


 *)
Theorem red13:
  exists A, (A_tm <=m A) /\ Recognizable A.
Proof.

Admitted.

(**

Solve Exercise 5.7 of the book. The solution given in pp 242 is as follows:

1. Suppose that A <=m compl A. Then compl A <=m A via co_red_2.
2. Because A is Turing-recognizable, red3 implies that compl A is
   Turing-recognizable, and then dec_rec_co_rec implies that A is decidable.


 *)
Theorem red14:
  forall A,
  Recognizable A ->
  A <=m compl A ->
  Decidable A.
Proof.

Admitted.



