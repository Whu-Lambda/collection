Require Import util.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Unicode.Utf8.

Definition store := id -> nat.

Definition heap := nat -> option nat.

Axiom finite_heap : ∀ h: heap, ∃ n: nat,
  ∀ n' v: nat, h n' = Some v -> n' < n.

Definition emp_heap : heap :=
  fun (n: nat) => None.


Definition in_dom (l: nat) (h: heap) : Prop :=
  ∃ n, h l = Some n.

Definition not_in_dom (l: nat) (h: heap) : Prop :=
  h l = None.
  
Theorem in_not_in_dec :
  ∀ l h, {in_dom l h} + {not_in_dom l h}.
Proof.
  intros l h. unfold in_dom. unfold not_in_dom.
  destruct (h l).
  left. ∃ n. auto.
  right. auto.
Qed.



Definition disjoint (h1 h2: heap) : Prop :=
  ∀ l, not_in_dom l h1 \/ not_in_dom l h2.

Definition h_union (h1 h2: heap) : heap :=
  fun l =>
    if (in_not_in_dec l h1) then h1 l else h2 l.


(* h1 is a subset of h2 *)
Definition h_subset (h1 h2: heap) : Prop :=
  ∀ l n, h1 l = Some n -> h2 l = Some n.



(* store update *)
Definition st_update (s: store) (x: id) (n: nat) : store :=
  fun x' => if beq_id x x' then n else s x'.


(* heap update *)
Definition h_update (h: heap) (l: nat) (n: nat) : heap :=
  fun l' => if beq_nat l l' then Some n else h l'.






Definition state : Type := (store * heap).

(* since program may abort, we extend our state
   definition to add a special state Abt *)
Inductive ext_state : Type :=
|  St:  state -> ext_state    (* normal state *)
| Abt: ext_state.             (* abort *)




(* Lemma *)
Lemma h_update_equal : ∀ x h l n,
  in_dom x h ->
  h l = None ->
  h x = (h_update h l n) x.
Proof.
  intros.
  unfold h_update, in_dom in *.
  destruct (l =? x) eqn:Ha.
  -apply beq_nat_true in Ha. subst. destruct H.
   rewrite H in H0. inversion H0.
  -reflexivity.
Qed.


Lemma disjoint_comm : ∀ h1 h2,
  disjoint h1 h2 <-> disjoint h2 h1.
Proof.
  intros. unfold disjoint. split.
  -intros. destruct H with l.
   +right. assumption.
   +left. assumption.
  -intros. destruct H with l.
   +right. assumption.
   +left. assumption.
Qed.


Lemma disjoint_elim_union_a : ∀ h1 h2 h3,
  disjoint h1 (h_union h2 h3) ->
  disjoint h1 h2.
Proof.
  intros. unfold disjoint in *.
  intros. destruct H with l.
  -left. assumption.
  -right. unfold h_union, not_in_dom in *.
   destruct (in_not_in_dec l h2).
   +assumption.
   +unfold not_in_dom in *. assumption.
Qed.


Lemma disjoint_elim_union_b : ∀ h1 h2 h3,
  disjoint h1 (h_union h2 h3) ->
  disjoint h1 h3.
Proof.
  intros. unfold disjoint in *.
  intros. destruct H with l.
  -left. assumption.
  -right. unfold h_union, not_in_dom in *.
   destruct (in_not_in_dec l h2).
   +unfold in_dom in *. destruct i. rewrite H1 in H0.
    inversion H0.
   +assumption.
Qed.


Lemma h_union_emp_heap : ∀ h,
  h_union emp_heap h = h.
Proof.
  intros. unfold h_union.
  apply functional_extensionality. intros.
  destruct (in_not_in_dec x emp_heap).
  -unfold in_dom in *. destruct i. unfold emp_heap in *.
   inversion H.
  -reflexivity.
Qed.

