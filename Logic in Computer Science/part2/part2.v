From Coq Require Import ssreflect ssrfun ssrbool.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Coq.Program.Equality.
Require Import Coq.Init.Datatypes.
Require Export Bool.
Require Import Unicode.Utf8.

Inductive TermType := | Value | Type_ | rule_jugd .

Inductive Symbol (x : TermType) := 
  | initial : Symbol x
  | next : Symbol x -> Symbol x.

Inductive TypeDef := 
  | SimplyT : Symbol Type_ -> TypeDef
  | Arrow : TypeDef -> TypeDef -> TypeDef
  | Udnf : TypeDef.

Inductive Expression :=
  |Var : Symbol Value -> TypeDef -> Expression
  |Abs : Expression -> Expression -> TypeDef -> Expression
  |App : Expression -> Expression -> TypeDef -> Expression.

Definition type_of_T (e' : Expression) :=
  match e' return TypeDef with
    |Var _ t => t
    |Abs _ _ t => t
    |App _ _ t => t
  end.

Inductive Enviroment := 
  |empty : Enviroment
  |bind : ∀ T {H : T <> Udnf}, Expression -> Enviroment -> Enviroment.

Notation "T*" := Enviroment.

Notation "{}" := empty.

Inductive Judgment env (P : Enviroment -> Prop) :=
  |Assume : P env -> Judgment env P.

Fixpoint same_symbol {F} (x : Symbol F) (y : Symbol F) :=
  match (x, y) with
    |(next _ k, next _ k') => same_symbol k k'
    |(initial _, initial _) => true
    |_ => false
  end.

Fixpoint same_type (x : TypeDef) (y : TypeDef) := 
  match (x, y) with
    | (SimplyT k, SimplyT k') => same_symbol k k'
    | (Arrow k k', Arrow u u') => (same_type k u) && (same_type k' u')
    | (Udnf, Udnf) => true
    | _ => false
  end.

Fixpoint has_type (x : TypeDef) (env : Enviroment) : bool :=
  match env with
    |empty => false
    |bind T LT es => match T with
                          |Udnf => (has_type x es)
                          |_ => if (same_type x T) then true else (has_type x es)
                        end
  end.

Fixpoint same_expression (x : Expression) (y : Expression) : bool :=
  match (x, y) with
    | (Var x t, Var y t') => same_type t t' && same_symbol x y
    | (Abs s x t, Abs s' x' t') => same_type t t' && same_expression s s' && (same_expression x x')
    | (App x y t, App x' y' t') => same_type t t'&& same_expression x x' && same_expression y y'
    | _ => false
  end.

Fixpoint varType (x : Expression) (env : Enviroment) : TypeDef :=
  match env with
    |empty => Udnf
    |bind T LT es => if (same_expression x LT) then T else varType x es
  end.


Notation "x |- y" := (Judgment x (fun p => (has_type (varType y x) x) = true)) (at level 202, right associativity).
Notation "x |- { y ::: T }" := (Judgment x (fun p => (has_type (varType y x) x) = true /\ (varType y x) = T)) (at level 201, right associativity).
Notation "x ∈ y" := (varType x y <> Udnf) (at level 50, left associativity, only parsing).

Definition ArrowIsDef : ∀ T1 T2, Arrow T1 T2 <> Udnf. by []. Defined.

Inductive typed_rules : T* -> Symbol Value -> Expression -> Type :=
  |Tvar : ∀ (env : Enviroment) (s : Symbol _) T {H' : T <> Udnf}, (env |- {(Var s T) ::: T}) -> typed_rules env s (Var s T)
  |TAbs : ∀ (env : Enviroment) (k : Symbol Value) x T2 {H' : T2 <> Udnf} s,
    typed_rules env k x -> (env |- {(Var s T2) ::: T2}) -> 
      (fun t => 
        typed_rules (@bind (Arrow T2 (type_of_T x)) (ArrowIsDef _ _) t env) (next _ k) t) (Abs (Var s T2) x (Arrow T2 (type_of_T x)))
  |TApp : ∀ (env : Enviroment) (k : Symbol Value) (x : Expression) T T' T1 T2 {H : T2 <> Udnf},
    typed_rules env k x -> (env |- {T ::: Arrow T1 T2}) -> (env |- {T' ::: T1}) -> 
      (fun t => (typed_rules (@bind T2 H t env) k t)) (App T T' T2).

Theorem well_typed_context_has_type : ∀ {K} (env : Enviroment) (s : Symbol _) (H : typed_rules env s K), (env |- K) -> K ∈ env.
intros.
destruct H0;destruct (varType K env); cbv.
discriminate.
discriminate.
have : ∀ env, has_type Udnf env = false.
move => H'; elim : H'; trivial.
intros.
rewrite <- H1.
destruct T.
auto.
auto.
simpl; trivial.
assert (∀ x, x = false -> x <> true).
move => H'.
destruct H'; move => SH.
discriminate.
discriminate.
move => l;contradiction (H0 _ (l env)).
Qed.

Lemma H0_symbol : ∀ {T} (s : Symbol T), same_symbol s s = true. 
move => f; elim; trivial.
Defined.

Hint Resolve H0_symbol.

Lemma H1_expression : ∀ e, same_expression e e = true.

have : ∀ s', same_type s' s' = true.
elim.
move => //=.
move => Eq k k' H.
move => /=.
rewrite k H.
done.
done.

move => H.
elim.
move => /= s t.
rewrite -> (H t).
move => //=.
move => s e t H' t0 /=.
rewrite e H' (H t0); move => /=; intuition.
move => e e0 t H' t0 //=.
rewrite e0 H'; intuition.
Defined.

Lemma H3_type : ∀ e, same_type e e = true.
elim.
move => q /=; by [].
move => q k' v H' /=.
rewrite k' //.
done.
Defined.

Ltac type_eq_solver := 
  let rewrite_type_axioms := 
    try (do ! (rewrite -> (H0_symbol _)));
    try (do ! (rewrite -> (H1_expression _)));
    try (do ! (rewrite -> (H3_type _))) in
  let rewrite_type_axioms_H H := 
    try (do ! (rewrite (H0_symbol _)) in H);
    try (do ! (rewrite (H1_expression _)) in H);
    try (do ! (rewrite -> (H3_type _)) in H) in
    do ! (simpl; rewrite_type_axioms); match goal with
    |  [ H : _ |- _ ] => generalize H; do ! (simpl; rewrite_type_axioms_H H); clear H; type_eq_solver; intro H
    |  [ |- _ ] => match goal with
            | [ H : _ |- _ ] => fail 1
            | [ |- _ ] => simpl
            end
  end. 

Theorem type_context_abs : 
  ∀ (env : Enviroment) (s : Symbol _) T k y (H : typed_rules env s (Abs k y T)), (env |- {(Abs k y T) ::: T}).
intros.

have : 
  has_type (varType (Abs k y T) env) env = true /\ varType (Abs k y T) env = T -> Judgment env (fun _ : T* => has_type (varType (Abs k y T) env) env = true /\ varType (Abs k y T) env = T).
move => D; constructor; trivial.
apply.

remember (Abs k y T).
destruct H.
discriminate Heqe.
constructor.
- simpl; destruct j; type_eq_solver; reflexivity.
- destruct j.
  generalize (Abs (Var s T2) x (Arrow T2 (type_of_T x))).
  case;simpl.
  move => s' t';type_eq_solver.
  injection Heqe; trivial.
  intros;type_eq_solver.
  simpl;injection Heqe; intros; assumption.
  intros;type_eq_solver;simpl;injection Heqe; intros; assumption.
- inversion Heqe.
Qed.

Theorem Types_of_terms_are_well_defined : ∀ T x s env, typed_rules env s x -> varType x env = T -> T <> Udnf.
intros.
destruct H.
do 2 destruct j as [j].
rewrite -> H in H0;rewrite H0 in H'.
exact H'.
do 2 destruct j as [j].
subst;type_eq_solver.
apply : ArrowIsDef.
do 2 destruct j as [j];do 2 destruct j0 as [j0].
subst;simpl;type_eq_solver;assumption.
Qed.

Lemma conservation_of_types : ∀ T x s env, typed_rules env s x -> varType x env = T -> type_of_T x = T.
intros.
set H' := (@Types_of_terms_are_well_defined _ _ _ _ H H0).
induction env.
simpl in H0;cbv in H'.
destruct (H' (eq_sym H0)).
destruct H.
do 2 destruct j as [j];simpl in *;clear H';rewrite -> e0 in H0.
assumption.
do 2 destruct j as [j].
simpl in *;subst;type_eq_solver; reflexivity.
do 2 destruct j as [j].
do 2 destruct j0 as [j0].
subst.
simpl.
type_eq_solver.
trivial.
Qed.

Theorem type_context : 
  ∀ (env : Enviroment) (s : Symbol _) T K (H : typed_rules env s K), type_of_T K = T -> (env |- {K ::: T}).
intros.

have : has_type (varType K env) env = true /\ varType K env = T -> Judgment env
  (fun _ : T* => has_type (varType K env) env = true /\ varType K env = T).
move => H'.
destruct H'.
constructor.
constructor.
assumption.
assumption.
apply.

constructor.
destruct H.
do 2 destruct j as [j].
assumption.
simpl;type_eq_solver;trivial;subst.
do 2 destruct j as [j].
do 2 destruct j0 as [j0].
type_eq_solver;destruct T2.
trivial.
trivial.
contradiction H;trivial.
destruct H.
do 2 destruct j as [j].
simpl in H0.
rewrite <- H0.
assumption.
do 2 destruct j as [j].
subst;simpl;type_eq_solver;trivial.
do 2 destruct j as [j];do 2 destruct j0 as [j0].
subst;type_eq_solver; trivial.
Qed.


Lemma eq_symb : ∀ {T} (x : Symbol T) y, same_symbol x y = true -> x = y.
intros.
(*try to proof this normally induction is bit hard cause' the x and y are evaluated in same time so the
  induction have to reason about two mutually, so a new mutual scheme was set*)
set mutually_symbol := fun (x : TermType) (P : Symbol x -> Symbol x -> Prop)
        (f_2initial : P (initial x) (initial x))
        (f_2next : forall s s' : Symbol x,
                    P s s' -> P (next x s) (next x s'))
        (f_contr0' : forall s s' : Symbol x,
                      P s s' -> P (initial x) (next x s'))
        (f_contr1' : forall s s' : Symbol x,
                      P s s' -> P (next x s) (initial x)) =>
        fix Ffix (x0 : Symbol x) : forall x1 : Symbol x, P x0 x1 :=
        match x0 as c return (forall x1 : Symbol x, P c x1) with
          | initial _ =>
            fix Ffix0 (x1 : Symbol x) : P (initial x) x1 :=
              match x1 as c return (P (initial x) c) with
                | initial _ => f_2initial
                | next _ x2 => f_contr0' (initial x) x2 (Ffix0 x2)
              end
          | next _ x1 =>
              fun x2 : Symbol x =>
              match x2 as c return (P (next x x1) c) with
                | initial _ => f_contr1' x1 (initial x) (Ffix x1 (initial x))
                | next _ x3 => f_2next x1 x3 (Ffix x1 x3)
              end
        end.
move : H.
elim/mutually_symbol : x/y.
done.
move => /= s s' H q.
set f := (H q).
rewrite -> f.
done.
done.
done.
Qed.

(*A specialized ssreflect based tatic for working induction in equal types*)
Ltac induction_eqType k y:=
  move => k; move => y; 
  set type_mutual_induction := (fun (P : TypeDef -> TypeDef -> Prop)
        (f_2SimplyT : forall k k' : Symbol Type_, P (SimplyT k) (SimplyT k'))
        (f_2Udnf : P Udnf Udnf)
        (f_Simply_Arrow : forall (k : Symbol Type_) (s s' : TypeDef),
                          P (SimplyT k) (Arrow s s'))
        (f_Arrow_Simply : forall (k : Symbol Type_) (s s' : TypeDef),
                          P (Arrow s s') (SimplyT k))
        (f_Simply_Udnf : forall k : Symbol Type_, P (SimplyT k) Udnf)
        (f_Udnf_Simply : forall k : Symbol Type_, P Udnf (SimplyT k))
        (f_2Arrow : forall s s' q q' : TypeDef,
                    P s q -> P s' q' -> P (Arrow s s') (Arrow q q'))
        (f_Arrow_Udnf : forall s s' : TypeDef, P (Arrow s s') Udnf)
        (f_Udnf_Arrow : forall s s' : TypeDef, P Udnf (Arrow s s')) =>
          fix Ffix (x : TypeDef) : forall x0 : TypeDef, P x x0 :=
            match x as c return (forall x0 : TypeDef, P c x0) with
              | SimplyT x0 =>
                fun x1 : TypeDef =>
                  match x1 as c return (P (SimplyT x0) c) with
                    | SimplyT x2 => f_2SimplyT x0 x2
                    | Arrow x2 x3 => f_Simply_Arrow x0 x2 x3
                    | Udnf => f_Simply_Udnf x0
                  end
              | Arrow x0 x1 =>
                fix Ffix0 (x2 : TypeDef) : P (Arrow x0 x1) x2 :=
                  match x2 as c return (P (Arrow x0 x1) c) with
                    | SimplyT x3 => f_Arrow_Simply x3 x0 x1
                    | Arrow x3 x4 =>
                      f_2Arrow x0 x1 x3 x4 (Ffix x0 x3) (Ffix x1 x4)
                    | Udnf => f_Arrow_Udnf x0 x1
                  end
              | Udnf =>
                fun x0 : TypeDef =>
                  match x0 as c return (P Udnf c) with
                    | SimplyT x1 => f_Udnf_Simply x1
                    | Arrow x1 x2 => f_Udnf_Arrow x1 x2
                    | Udnf => f_2Udnf
                  end
            end);
  elim/type_mutual_induction : k/y; clear.

Lemma eq_type : ∀ k y, same_type k y = true-> k = y.
induction_eqType k y.
intros.
unfold same_type in H.
rewrite -> (eq_symb _ _ H).
trivial.
trivial.
intros;inversion H.
intros;inversion H.
intros;inversion H.
intros;inversion H.
intros.
simpl in H1.
apply andb_true_iff in H1.
destruct H1.
apply H in H1.
apply H0 in H2.
rewrite H1 H2.
trivial.
intros; inversion H.
intros; inversion H.
Qed.


(*False injection was the more easy way to prove somes check that the typed_rules do is wrong, 
  fortunately the "bind" construct a false injection equality*)

Lemma False_injection_nextC : ∀ (t : TypeDef) t0, t = Arrow t0 t -> False.
induction t.
intros.
discriminate.
move => H H1.
injection H1.
intros.
rewrite -> H2 in H1.
injection H1.
intros.
apply IHt2 in H3.
trivial.
discriminate.
Qed.

Theorem lambda_type_return : 
  ∀ (env : Enviroment) (s : Symbol _) k y T1 T2 x (H : typed_rules env s x), x = (Abs k y (Arrow T1 T2)) ->
    (env |- {(Abs k y (Arrow T1 T2)) ::: Arrow T1 T2}) -> (env |- {y ::: T2}). 
intros.
remember s; destruct H.
inversion H0.
constructor.
simpl in *; injection H0; intros; destruct H1.
destruct y; simpl in *.
constructor.
subst; do 2 destruct j as [j].
type_eq_solver.
destruct (same_type (varType (Var s0 t) env) (Arrow T1 t)); trivial.
assert(type_of_T (Var s0 t) = t).
trivial.
pose(type_context _ _ _ _ H H2).
do 2 destruct j0 as [j0].
destruct (same_type (varType (Var s1 t) env) (Arrow T1 t)).
trivial.
assumption.
destruct (same_type (varType (Var s1 t) env) (Arrow T1 t)).
trivial.
assert(type_of_T (Var s1 t) = t).
trivial.
pose (type_context _ _ _ _ H H2).
do 2 destruct j0 as [j0].
assumption.
destruct a.
destruct j.
destruct a.
injection H0; intros.
rewrite <- H4; rewrite <- H2.
pose(type_context _ _ _ _ H H9).
do 2 destruct j as [j].
subst; assumption.
constructor.
do 2 destruct j as [j].
subst; type_eq_solver.
case : (same_type t (Arrow T1 t) && same_expression y1 (Var s0 T1) && 
  same_expression y2 (Abs y1 y2 t)).
type_eq_solver; trivial.
destruct (same_type (varType (Abs y1 y2 t) env) (Arrow T1 t)).
trivial.
assert(type_of_T (Abs y1 y2 t) = t).
trivial.
pose(type_context _ _ _ _ H H2).
do 2 destruct j0 as [j0].
trivial.

do 2 destruct j as [j].
simpl in *; subst; type_eq_solver.
remember (if
  same_type t (Arrow T1 t) && same_expression y1 (Var s0 T1) &&
  same_expression y2 (Abs y1 y2 t)
    then Arrow T1 t
    else varType (Abs y1 y2 t) env).
remember (same_type t (Arrow T1 t)).
remember (same_expression y1 (Var s0 T1) && same_expression y2 (Abs y1 y2 t)).
destruct b.
symmetry in Heqb; apply eq_type in Heqb; destruct (False_injection_nextC _ _ Heqb).
simpl in Heqt0; rewrite -> Heqt0.
assert(type_of_T (Abs y1 y2 t) = t).
trivial.
pose (type_context _ _ _ _ H H2).
do 2 destruct j0 as [j0].
assumption.

subst; type_eq_solver; constructor.
destruct (same_type (varType (App y1 y2 t) env) (Arrow T1 t)).
trivial.
destruct H. 
do 2 destruct j0 as [j0]; exact j0.
type_eq_solver; trivial.
simpl in *; type_eq_solver; destruct T2; trivial.
trivial.
contradiction H; apply : eq_refl.
remember (App y1 y2 t); destruct H.
do 2 destruct j0 as [j0].
inversion Heqe.
simpl in *; type_eq_solver.
inversion Heqe.
simpl in *; type_eq_solver; injection Heqe; intros; assumption.
inversion H0.
Qed.

(*this lemma is a counter implication of conservation_of_types so, we able to construct a strong <-> relation between enviroment and their types*) 
Lemma strong_enviroment_conservation : ∀ T2 env y, same_type (varType y env) T2 = true -> varType y env = T2.
move => t2 d; elim.
move => y g Heq.
induction y.
destruct d.
destruct t2; simpl in Heq.
inversion Heq.
inversion Heq.
trivial; simpl; simpl in Heq.
move : Heq; generalize (if
  match e with
  | Var y t' =>
      same_type g t' &&
      match y with
      | initial _ => true
      | next _ _ => false
      end
  | _ => false
  end
    then T
    else varType (Var (initial Value) g) d).
move => t0; apply : eq_type.
destruct d; simpl in *.
apply IHy in Heq; assumption.
apply eq_type in Heq; trivial.
intros; apply eq_type in H1; trivial.
intros;apply eq_type in H1;trivial.
Qed.