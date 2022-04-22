Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import language.
Require Import state.
Require Import util.
Require Import semantic.
Require Import Unicode.Utf8.


Definition assertion := state -> Prop.

Definition emp : assertion :=
  fun st: state => snd st = emp_heap.

Definition point_to (e1 e2: aexp): assertion :=
  fun st: state =>
  match st with
  | (s,h) => h = h_update emp_heap (aeval s e1) (aeval s e2)
  end.
Notation "e1 '|->' e2" := (point_to e1 e2) (at level 60).


Definition sep_conj (p q : assertion) : assertion :=
    fun st: state =>
      match st with
      | (s, h) =>
        ∃ h1, ∃ h2,
          disjoint h1 h2 /\ h_union h1 h2 = h /\ p (s, h1) /\ q (s, h2)
      end.
Notation "p '**' q" := (sep_conj p q) (at level 70).

Definition sep_disj (p q: assertion) : assertion :=
  fun (st : state) =>
    match st with
    | (s, h) =>
      ∀ h', disjoint h' h -> p (s, h') -> q (s, h_union h h')
    end.
Notation "p '--*' q" := (sep_disj p q) (at level 80).

Definition s_conj (p q: assertion) : assertion :=
  fun (s: state) => p s /\ q s.
Notation "p '//\\' q" := (s_conj p q) (at level 75).

Definition s_disj (p q: assertion) : assertion :=
  fun (s: state) => p s \/ q s.
Notation "p '\\//' q" := (s_disj p q) (at level 78).

Definition s_imp (p q: assertion) : assertion :=
  fun (s: state) => p s -> q s.
Notation "p '-->' q" := (s_imp p q) (at level 85).



Definition strongerThan (p q: assertion) : Prop :=
  ∀ s: state, s_imp p q s.
Notation "p '==>' q" := (strongerThan p q) (at level 90).

Definition spEquiv (p q: assertion) : Prop :=
  (p ==> q) /\ (q ==> p).
Notation "p '<==>' q" := (spEquiv p q) (at level 90).





(* theorems of assertion *)
Lemma disj_star_distr: ∀ (p q r: assertion),
  (p \\// q) ** r <==> (p ** r) \\// (q ** r).
Proof.
  intros.
  unfold spEquiv. split.
  -unfold strongerThan, s_imp. intros.
   destruct s. destruct H. destruct H. destruct H. destruct H0.
   destruct H1. unfold s_disj in *. destruct H1.
   +left. unfold sep_conj. ∃ x. ∃ x0. auto.
   +right. unfold sep_conj. ∃ x. ∃ x0. auto.
  -unfold strongerThan, s_imp. intros.
   destruct s. unfold s_disj in *. destruct H.
   +simpl. repeat destruct H. destruct H0. destruct H1.
    ∃ x. ∃ x0. auto.
   +simpl. repeat destruct H. destruct H0. destruct H1.
    ∃ x. ∃ x0. auto.
Qed.


Lemma conj2disj : ∀ p1 p2 p3,
  p1 ** p2 ==> p3 ->
  p1 ==> p2 --* p3.
Proof.
  unfold strongerThan, s_imp. intros. destruct s.
  unfold sep_disj. intros. unfold sep_conj in *.
  apply H. ∃ h. ∃ h'. split.
  -apply disjoint_comm. assumption.
  -split. +reflexivity. +split; assumption.
Qed.