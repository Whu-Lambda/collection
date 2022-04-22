Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import language.
Require Import state.
Require Import util.
Require Import Unicode.Utf8.

Fixpoint aeval (sto: store) (a: aexp): nat :=
match a with
| ANum n => n
| AId name => sto name
| APlus a1 a2 => (aeval sto a1) + (aeval sto a2)
| AMult a1 a2 => (aeval sto a1) * (aeval sto a2)
end.


Fixpoint beval (sto: store) (b: bexp): bool :=
match b with
| BTrue     => true
| BFalse    => false
| BEq a1 a2 => beq_nat (aeval sto a1) (aeval sto a2)
| BLe a1 a2 => leb (aeval sto a1) (aeval sto a2)
| BNot b1   => negb (beval sto b1)
| BAnd b1 b2 => andb (beval sto b1) (beval sto b2)
end.



Inductive big_step: command -> state -> ext_state -> Prop :=
| E_Skip  : ∀ stat,
              big_step CSkip stat (St stat)
| E_Ass   : ∀ sto h x a n, (aeval sto a) = n ->
              big_step (CAss x a) (sto,h) (St ((st_update sto x n),h))
| E_Seq   : ∀ c1 c2 st0 st1 opst,
              big_step c1 st0 (St st1) ->
              big_step c2 st1 opst ->
              big_step (CSeq c1 c2) st0 opst
| E_Seq_Ab: ∀ c1 c2 st0,
              big_step c1 st0 Abt ->
              big_step (CSeq c1 c2) st0 Abt
| E_IfTure: ∀ sto h opst b c1 c2,
              beval sto b = true ->
              big_step c1 (sto,h) opst ->
              big_step (CIf b c1 c2) (sto,h) opst
| E_IfFalse:∀ b sto c1 c2 h opst,
              beval sto b = false ->
              big_step c2 (sto,h) opst ->
              big_step (CIf b c1 c2) (sto,h) opst
| E_WhileEnd : ∀ b sto h c,
                 beval sto b = false ->
                 big_step (CWhile b c) (sto, h) (St (sto, h))
| E_WhileLoop : ∀ sto h opst b c st,
                  beval sto b = true ->
                  big_step c (sto, h) (St st) ->
                  big_step (CWhile b c) st opst ->
                  big_step (CWhile b c) (sto, h) opst
| E_WhileLoop_Ab : ∀ sto h b c,
                  beval sto b = true ->
                  big_step c (sto, h) Abt ->
                  big_step (CWhile b c) (sto, h) Abt
| E_Cons : ∀ sto h a n x l,
              aeval sto a = n ->
              h l = None ->
              big_step (CCons x a) (sto, h)
                       (St (st_update sto x l,
                            h_update h l n))
| E_Lookup : ∀ sto h x a1 n1 n2,
                aeval sto a1 = n1 ->
                h n1 = Some n2 ->
                big_step (CLookup x a1) (sto, h) (St (st_update sto x n2, h))
| E_Lookup_Ab : ∀ sto a1 n1 h x,
                   aeval sto a1 = n1 ->
                   h n1 = None ->
                   big_step (CLookup x a1) (sto, h) Abt
| E_Mutat : ∀ sto h a1 a2 n1 n2,
                  aeval sto a1 = n1 ->
                  aeval sto a2 = n2 ->
                  in_dom n1 h ->
                  big_step (CMutat a1 a2) (sto, h) (St (sto, h_update h n1 n2))
| E_Mutat_Ab : ∀ sto h a1 a2 n1,
                     aeval sto a1 = n1 ->
                     h n1 = None ->
                     big_step (CMutat a1 a2) (sto, h) Abt
| E_Dispose : ∀ sto h a1 n1,
                 aeval sto a1 = n1 ->
                 in_dom n1 h ->
                 big_step
                   (CDispose a1) (sto, h)
                   (St (sto, fun x => if eq_nat_dec x n1 then None else h x))
| E_Dispose_Ab : ∀ sto h a1 n1,
                    aeval sto a1 = n1 ->
                    h n1 = None ->
                    big_step (CDispose a1) (sto, h) Abt.

Notation "c1 '/' st '\\' opst" := (big_step c1 st opst) (at level 40, st at level 39).
