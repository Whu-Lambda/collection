Require Import seplogic.
Require Import Unicode.Utf8.


Example alloc_test1 :
  {{ emp }}
  (CCons X (ANum 1))
  {{(AId X) |-> (ANum 1)}}.
Proof.
  eapply rule_consequence_pre.
  -apply rule_alloc.
  -unfold strongerThan. intros. destruct s.
   unfold s_imp. intros. simpl. intros.
   unfold assn_sub, point_to. simpl.
   unfold st_update. simpl.
   subst. inversion H. simpl in *. subst.
   rewrite h_union_emp_heap.
   reflexivity.
Qed.

Example alloc_test2 :
  {{ emp }}
  (CSeq (CCons X (ANum 1))
        (CCons Y (ANum 2)))
  {{(AId X) |-> (ANum 1)**(AId Y)|->(ANum 2)}}.
Proof.
  apply rule_seq with ((AId X) |-> (ANum 1)).
  -eapply rule_consequence_pre.
   apply rule_alloc.
   +unfold strongerThan. intros. unfold s_imp.
    destruct s. intros. simpl in *. intros.
    unfold assn_sub. simpl. unfold st_update. simpl.
    ∃ h. ∃ h'. split.
    *apply disjoint_comm. assumption.
    *split. ++reflexivity. ++split; assumption.
  -eapply rule_consequence_pre.
   +apply rule_alloc.
   +unfold strongerThan. intros. destruct s.
   unfold s_imp. intros. simpl. intros.
   unfold assn_sub, point_to. simpl.
   unfold st_update. simpl.
   subst. inversion H. simpl in *. subst.
   rewrite h_union_emp_heap.
   reflexivity.
Qed.
