Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import language.
Require Import state.
Require Import util.
Require Import semantic.
Require Import assertion.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Unicode.Utf8.
Import ListNotations.


Definition triple
           (P: assertion) (c:command) (Q:assertion) : Prop :=
  ∀ st opst,
     c / st \\ opst ->
     P st ->
     match opst with
     | St st => Q st
     | Abt => False
     end.

Notation "{{ P }} c {{ Q }}" :=
  (triple P c Q) (at level 90, c at next level).



Definition assn_sub (X: id) (a: aexp) P : assertion :=
  fun st => P ((st_update (fst st) X (aeval (fst st) a)), (snd st)).
Notation "P [ X \ a ]" := (assn_sub X a P) (at level 10).






(* proof rules & soundness *)

(* assign *)
Theorem rule_asgn : ∀ Q X a,
  {{Q [X \ a]}} (CAss X a) {{Q}}.
Proof.
  intros.
  unfold triple.
  intros. unfold assn_sub in *.
  inversion H. subst. assumption.
Qed.


(* consquence *)
Theorem rule_consequence_pre : ∀ (P P' Q : assertion) c,
  {{P'}} c {{Q}} ->
  P ==> P' ->
  {{P}} c {{Q}}.
Proof.
  intros.
  unfold triple in *.
  unfold strongerThan in *.
  intros.
  apply H0 in H2.
  apply H in H1.
  -apply H1. -apply H2.
Qed.

Theorem rule_consequence_post : ∀ (P Q Q' : assertion) c,
  {{P}} c {{Q'}} ->
  Q' ==> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold triple in *.
  unfold strongerThan in *.
  intros. unfold s_imp in *.
  assert (c / st \\ opst /\ P st). -auto.
  -apply H in H1.
   +destruct opst. 
    *apply H0. assumption.
    *inversion H1.
   +apply H2.
Qed.

Theorem rule_consequence : ∀ (P P' Q Q' : assertion) c,
  {{P'}} c {{Q'}} ->
  P ==> P' ->
  Q' ==> Q ->
  {{P}} c {{Q}}.
Proof.
  intros.
  apply rule_consequence_pre with P'.
  -apply rule_consequence_post with Q'.
   +assumption.
   +assumption.
  -assumption.
Qed.


Theorem rule_skip : ∀ P,
     {{P}} CSkip {{P}}.
Proof.
  unfold triple. intros.
  inversion H. subst. assumption.
Qed.


(* Sequencing *)
Theorem rule_seq : ∀ P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} (CSeq c1 c2) {{R}}.
Proof.
  unfold triple.
  intros.
  inversion H1. subst.
  apply H0 in H5. apply H in H8.
  -assumption. -assumption. -assumption. 
  -subst. apply H0 in H7.
   +inversion H7. +apply H2.
Qed.



(* Conditionals *)
(*
      {{P ∧  b}} c1 {{Q}}
      {{P ∧ ~b}} c2 {{Q}}
------------------------------------
{{P}} IFB b THEN c1 ELSE c2 FI {{Q}}
*)
Definition bassn b : assertion :=
  fun st => (beval (fst st) b = true).

Lemma bexp_eval_true : ∀ b st,
  beval (fst st) b = true -> (bassn b) st.
Proof.
  intros.
  unfold bassn. assumption.
Qed.

Lemma bexp_eval_false : ∀ b st,
  beval (fst st) b = false -> not ((bassn b) st).
Proof.
  unfold bassn, not.
  intros. rewrite H in H0. inversion H0.
Qed.


Theorem rule_if : ∀ P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (CIf b c1 c2) {{Q}}.
Proof.
  unfold triple, bassn, not.
  intros. inversion H1. subst.
  -apply H in H9. assumption.
   +split. ++apply H2. ++apply H8.
  -subst. apply H0 in H9.
   +apply H9. 
   +split.
    ++apply H2.
    ++intros. simpl in H3. 
      rewrite H8 in H3. inversion H3.
Qed.



(* loops *)
Theorem rule_while : ∀ P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} (CWhile b c) {{fun st => P st /\ not (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (CWhile b c) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileEnd *)
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileLoop *)
    apply IHHe2. reflexivity. unfold triple in *.
    apply (Hhoare (sto, h) (St st)). assumption.
    split. assumption. apply bexp_eval_true. assumption.
  - unfold triple in *.
    apply (Hhoare (sto, h) Abt).
    +assumption. +split. *assumption.
     *apply bexp_eval_true. simpl. assumption.
Qed.



(* allocation *)
Theorem rule_alloc : ∀ P X a,
  {{fun st => ∀ loc, (((ANum loc) |-> a) --* P [X \ (ANum loc)]) st}}
  (CCons X a)
  {{P}}.
Proof.
  intros. unfold triple. intros.
  unfold sep_disj, assn_sub, point_to in *.
  inversion H. subst.
  simpl in *. 
  remember (h_update emp_heap l (aeval sto a)) as h'.
  assert ((h_union h h') = (h_update h l (aeval sto a))).
  -unfold h_union, h_update. apply functional_extensionality.
   intros. destruct (in_not_in_dec x h) eqn:Hx.
   +destruct (l =? x) eqn:Hxx.
    *apply beq_nat_true in Hxx. unfold in_dom in i.
     destruct i. subst. rewrite e in H6. inversion H6.
    *reflexivity.
   +destruct (l =? x) eqn:Hxx.
    *apply beq_nat_true in Hxx. unfold not_in_dom in n.
     subst. unfold h_update. destruct (x =? x) eqn:Fk.
     ++reflexivity.
     ++apply beq_nat_false in Fk. destruct Fk. reflexivity.
    *apply beq_nat_false in Hxx. subst. unfold not_in_dom in n.
     unfold h_update. destruct (l =? x) eqn:Fkk.
     ++apply beq_nat_true in Fkk. subst. destruct Hxx. reflexivity.
     ++unfold emp_heap. rewrite n. reflexivity.
  -rewrite <- H1. apply H0.
   +unfold disjoint. intros. destruct (l =? l0) eqn:Hx.
    *apply beq_nat_true in Hx.
     right. unfold not_in_dom. subst. assumption.
    *left. unfold not_in_dom. subst. unfold h_update. rewrite Hx.
     unfold emp_heap. reflexivity.
   +subst. reflexivity.
Qed.







(* mutation *)
Theorem rule_mutate : ∀ P a1 a2,
  {{fun st => ∃ loc, ((aeval (fst st) a1) = loc) /\
              ∃ val, ((snd st) loc) = Some val /\
              P ((fst st), (h_update (snd st) loc (aeval (fst st) a2))) }}
  (CMutat a1 a2)
  {{P}}.
Proof.
  intros. unfold triple. intros. inversion H. subst.
  -inversion H0. simpl in *. destruct H1. destruct H2.
   destruct H2. rewrite H1. assumption.
  -subst. destruct H0. destruct H0. destruct H1. destruct H1.
   simpl in *. rewrite <- H0 in H1. rewrite H1 in H6.
   inversion H6.
Qed.






(* look up *)
Theorem rule_lookup : ∀ P a x,
  {{fun st => ∃ loc, ((aeval (fst st) a) = loc) /\
              ∃ val, ((snd st) loc) = Some val /\
              P ((st_update (fst st) x val), (snd st))
  }}
  (CLookup x a)
  {{P}}.
Proof.
  intros. unfold triple. intros. inversion H. subst.
  -destruct H0. destruct H0. destruct H1. destruct H1.
   simpl in *. rewrite <- H0 in H1. rewrite H1 in H6.
   inversion H6. subst. assumption.
  -subst. destruct H0. destruct H0. destruct H1. 
   destruct H1. simpl in *. rewrite H0 in H6.
   rewrite H1 in H6. inversion H6.
Qed.





(* dispose *)
Theorem rule_dispose : ∀ P a,
  {{fun st => ∃ loc, ((aeval (fst st) a) = loc) /\
              ∃ val, ((snd st) loc) = Some val /\
              P ((fst st), 
                 (fun l => if (eq_nat_dec l loc) then None else (snd st) l))
  }}
  (CDispose a)
  {{P}}.
Proof.
  intros. unfold triple. intros. inversion H. subst.
  -destruct H0. destruct H0. destruct H1. destruct H1.
   simpl in *. rewrite H0. assumption.
  -subst. destruct H0. destruct H0. destruct H1. destruct H1.
   simpl in *. rewrite <- H0 in H1. rewrite H1 in H3. inversion H3.
Qed.
