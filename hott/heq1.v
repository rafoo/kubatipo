Set Universe Polymorphism.

Definition id (A : Type) (a : A) := a.
Definition comp {A B C} (f : A -> B) (g : B -> C) : A -> C :=
  fun x => g (f x).

Inductive heq1 : forall {A B : Type} (f : A -> B) (a : A) (b : B), Type :=
| refl {A} a : heq1 (id A) a a.

Definition eq {A} (a b : A) := heq1 (id A) a b.

Definition sim {A B} (f g : A -> B) := forall x : A, eq (f x) (g x).
Definition pinv {A B} (f : A -> B) (g : B -> A) := sim (comp f g) (id A).
Definition qinv {A B} (f : A -> B) := {g : B -> A & (pinv f g * pinv g f)%type}.

Definition isProp A := forall x y : A, eq x y.


(* We axiomatize the isEqv property; it should be loosely equivalent
to qinv and it should be a mere proposition. *)
Variable isEqv : forall {A B}, (A -> B) -> Type.
Hypothesis eqv_intro : forall {A B} {f : A -> B}, qinv f -> isEqv f.
Hypothesis eqv_elim : forall {A B} (f : A -> B), isEqv f -> qinv f.
Hypothesis eqv_prop : forall {A B} (f : A -> B), isProp (isEqv f).

Definition eqv (A B : Type) := {f : A -> B & isEqv f}.
Definition eqv_fun A B (e : eqv A B) : A -> B :=
  let (f, _) := e in f.
Coercion eqv_fun : eqv >-> Funclass.


Lemma isEqv_id A : isEqv (id A).
Proof.
  apply eqv_intro.
  exists (id A).
  split; intro; apply refl.
Defined.

Lemma eqv_refl A : eqv A A.
Proof.
  exists (id A).
  apply isEqv_id.
Defined.

Lemma heq_eqv {A B} {f : A -> B} {a b} : heq1 f a b -> isEqv f.
Proof.
  intro e.
  destruct e.
  apply isEqv_id.
Defined.

Lemma inv {A B} (f : eqv A B) : eqv B A.
Proof.
  destruct f as (f, Hf).
  apply eqv_elim in Hf.
  destruct Hf as (g, (Hg1, Hg2)).
  exists g.
  apply eqv_intro.
  exists f.
  split; assumption.
Defined.

Lemma heq_inv {A B} {f : A -> B} {a b} : heq1 f a b -> B -> A.
Proof.
  intro e.
  destruct e.
  apply id.
Defined.

Lemma sym {A B} {f : A -> B} {a b} : forall h : heq1 f a b, heq1 (heq_inv h) b a.
Proof.
  intro e.
  destruct e.
  simpl.
  apply refl.
Defined.

Lemma trans {A B C} {f : A -> B} {g : B -> C} {a b c} :
  heq1 f a b ->
  heq1 g b c ->
  heq1 (comp f g) a c.
Proof.
  intro e.
  destruct e.
  intro e.
  destruct e.
  apply refl.
Defined.

Lemma refl_trans {A B} {a : A} {b : B} {f : A -> B} (p : heq1 f a b) :
  eq (trans (refl a) p) p.
Proof.
  destruct p.
  apply refl.
Defined.

Lemma trans_refl {A B} {a : A} {b : B} {f : A -> B} (p : heq1 f a b) :
  eq (trans p (refl b)) p.
Proof.
  destruct p.
  apply refl.
Defined.

Lemma sym_refl {A} {a : A} : eq (sym (refl a)) (refl a).
Proof.
  apply refl.
Defined.

Lemma eq_f {A B} {x y} {f : A -> B} : heq1 f x y -> eq (f x) y.
Proof.
  intro e.
  destruct e.
  apply refl.
Defined.

Definition EQ {A} (x y : A) := {e : eq x y & eq_f e = e}.

Lemma EQ_refl {A} (x : A) : EQ x x.
Proof.
  exists (refl x).
  reflexivity.
Defined.

Lemma EQ_f {A B} {x y} {f : A -> B} : heq1 f x y -> EQ (f x) y.
Proof.
  intro e.
  destruct e.
  apply EQ_refl.
Defined.

Definition EQ_f_id {A} {x y : A} (e : EQ x y) : EQ x y := let (h, _) := e in EQ_f h.

Lemma heq_subst {A B} {f : A -> B} {a b} (P : B -> Type) : heq1 f a b -> P (f a) -> P b.
Proof.
  intro e.
  destruct e.
  unfold id.
  apply id.
Defined.

Lemma heq_subst_rev {A B} {f : A -> B} {a b} (P : B -> Type) : heq1 f a b -> P b -> P (f a).
Proof.
  intro e.
  destruct e.
  unfold id.
  apply id.
Defined.

Lemma eq_subst {A} {x y : A} (P : A -> Type) : eq x y -> P x -> P y.
Proof.
  apply (@heq_subst A A (id A)).
Defined.

Lemma EQ_subst {A} {x y : A} (P : A -> Type) : EQ x y -> P x -> P y.
Proof.
  intros (e, He).
  apply eq_subst.
  assumption.
Defined.

Inductive isEqv2 : forall {A B} (f : A -> B), Type :=
| isEqv2_id : forall A, isEqv2 (id A).

(* In this definition, we cannot replace = by eq because we need J. *)
Definition heq5 {A B} (f : A -> B) (a : A) (b : B) :=
  ((f a = b) * isEqv2 f)%type.

Lemma heq_heq5 {A B : Type} {f : A -> B} {a b} : heq1 f a b -> heq5 f a b.
Proof.
  intro h.
  destruct h.
  split.
  - reflexivity.
  - apply isEqv2_id.
Defined.

Lemma heq5_heq {A B : Type} {f : A -> B} {a b} : heq5 f a b -> heq1 f a b.
Proof.
  intros (e, Hf).
  destruct Hf.
  destruct e.
  apply refl.
Defined.

Lemma eqv_heq_heq5 {A B} (f : A -> B) a b : eqv (heq1 f a b) (heq5 f a b).
Proof.
  exists (@heq_heq5 A B f a b).
  apply eqv_intro.
  exists (@heq5_heq A B f a b).
  split.
  - intros [].
    apply refl.
  - intros (e, Hf).
    destruct Hf.
    destruct e.
    apply refl.
Defined.

Lemma EQ_to_equal {A} {a b : A} : EQ a b -> a = b.
Proof.
  intros (e, He).
  apply (eq_subst _ e).
  reflexivity.
Defined.

Lemma equal_to_EQ {A} {a b : A} : a = b -> EQ a b.
Proof.
  intros [].
  apply EQ_refl.
Defined.

Lemma eq_trans {A} {a b c : A} : eq a b -> eq b c -> eq a c.
Proof.
  intro e.
  apply (eq_subst (fun b => eq b c -> eq a c) e).
  apply id.
Defined.

Lemma EQ_trans {A} {a b c : A} : EQ a b -> EQ b c -> EQ a c.
Proof.
  intro e.
  apply (EQ_subst (fun b => EQ b c -> EQ a c) e).
  apply id.
Defined.

Lemma eq_sym {A} {a b : A} : eq a b -> eq b a.
Proof.
  intro e.
  apply (eq_subst (fun b => eq b a) e).
  apply refl.
Defined.

Lemma EQ_sym {A} {a b : A} : EQ a b -> EQ b a.
Proof.
  intro e.
  apply (EQ_subst (fun b => EQ b a) e).
  apply EQ_refl.
Defined.

Lemma f_eq {A B} {x y : A} (f : A -> B) : eq x y -> eq (f x) (f y).
Proof.
  intro e.
  apply (eq_subst (fun y => eq (f x) (f y)) e).
  apply refl.
Defined.

Lemma f_EQ {A B} {x y : A} (f : A -> B) : EQ x y -> EQ (f x) (f y).
Proof.
  intro e.
  apply (EQ_subst (fun y => EQ (f x) (f y)) e).
  apply EQ_refl.
Defined.

(* Heterogeneous version of J *)
Lemma hJ {A B} {x y} {f : A -> B} (e : heq1 f x y) {P : forall B f (y : B), heq1 f x y -> Type} :
  P A (id _) x (refl x) -> P B f y e.
Proof.
  destruct e.
  apply id.
Defined.

Lemma f_eq_dep {A A' B} {x y} (f : forall x : A', B x) {i : A -> A'} :
  forall e : heq1 i x y, heq1 (heq_subst B e) (f (i x)) (f y).
Proof.
  intro e.
  destruct e.
  apply refl.
Defined.


Definition eq_f_id {A} {x y : A} (e : eq x y) : eq x y := eq_f e.

Lemma J' {A} {x y} {f : A -> A} (e : heq1 f x y) {P : forall (x y : A), eq x y -> Type} :
  P y y (refl y) -> P (f x) y (eq_f e).
Proof.
  unfold eq_f.
  destruct e.
  apply id.
Defined.

Lemma J'_id {A} {x y} (e : eq x y) {P : forall (x y : A), eq x y -> Type} :
  P y y (refl y) -> P x y (eq_f_id e).
Proof.
  unfold eq_f_id, eq_f.
  destruct e.
  apply id.
Defined.

Lemma J'_id2 {A} {x y} (e : eq x y) {P : forall (x y : A), eq x y -> Type} :
  P x x (refl x) -> P x y (eq_f_id e).
Proof.
  intro p.
  apply J'_id.
  apply (eq_subst (fun x => P x x (refl x)) e).
  exact p.
Defined.

Lemma J'_EQ {A} {x y} (e : EQ x y) {P : forall (x y : A), EQ x y -> Type} :
  P y y (EQ_refl y) -> P x y (EQ_f_id e).
Proof.
  destruct e as (e, He).
  unfold EQ_f_id, EQ_f.
  intro p.
  destruct He.
  destruct e.
  exact p.
Defined.

Lemma eq_finv {A B} {x y a b} {f : A -> B} : heq1 f a b -> eq (f x) y -> heq1 f x y.
Proof.
  intros e1 e2.
  destruct e1.
  exact e2.
Defined.

Definition eq_finv_id {A} {x y a b : A} (e1 : eq a b) (e2 : eq x y) : eq x y :=
  eq_finv e1 e2.

Lemma eq_f_finv {A B} {x y} {f : A -> B} (e : heq1 f x y) :
  eq (eq_finv e (eq_f e)) e.
Proof.
  destruct e.
  apply refl.
Defined.

Lemma hJ2 {A B B'} {x y y'} {f : A -> B} {f' : A -> B'} (e1 : heq1 f x y) (e2 : heq1 f' x y') {P : forall B f (y : B), heq1 f x y -> Type} :
  P B' f' y' e2 -> P B f y e1.
Proof.
  destruct e1.
  destruct e2.
  apply id.
Defined.

Lemma heq_eq_inv {A B} {f : A -> B} {a b} : forall e : heq1 f a b, eq a (heq_inv e b).
Proof.
  intro e.
  destruct e.
  simpl.
  apply refl.
Defined.

Lemma heq_f_is_id_fun {A B} {f : A -> B} {a b} : heq1 f a b -> (A -> B) -> (A -> A).
Proof.
  intro e.
  destruct e.
  exact (id (A -> A)).
Defined.

Lemma heq_f_is_id {A B} {f : A -> B} {a b} :
  forall h : heq1 f a b, heq1 (heq_f_is_id_fun h) f (id A).
Proof.
  intro e.
  destruct e.
  apply refl.
Defined.

(* Homogeneous version of J *)
Definition J_statement :=
  forall A (x y : A) (e : eq x y)
         (P : forall (x y : A), eq x y -> Type), P y y (refl y) -> P x y e.

(* J is equivalent to (forall e, eq (eq_f e) e) *)

Lemma eq_f_id_is_id : J_statement -> forall A (x y : A) (e : eq x y), eq (eq_f e) e.
Proof.
  intros j A x y e.
  apply (j A x y e).
  apply refl.
Defined.

Lemma eq_f_id_is_id_rev :
  (forall A (x y : A) (e : eq x y), eq (eq_f e) e) -> J_statement.
Proof.
  intros H A x y e P.
  apply (eq_subst (fun e => P y y (refl y) -> P x y e) (H A x y e)).
  destruct e.
  apply id.
Defined.

Lemma eq_f_eq_f {A} {x y : A} (e : eq x y) : eq (eq_f (eq_f e)) (eq_f e).
Proof.
  destruct e.
  apply refl.
Defined.

(* Lemma J : J_statement. *)
(* Proof. *)
(*   intros A x y1 y2 e1 e2 P. *)
(*   destruct e1. *)
(* I do not know if J_statement is provable. *)

(* But it implies that eq and = are equivalent. *)
Lemma eq_to_equal {A} {x y : A} : eq x y -> x = y.
Proof.
  intro e.
  apply (eq_subst _ e).
  reflexivity.
Defined.

Lemma equal_to_eq {A} {x y : A} : x = y -> eq x y.
Proof.
  intros [].
  apply refl.
Defined.

Definition leq {A : Type} (a b : A) : Type :=
  forall P, P a -> P b.

Lemma eq_to_leq {A} {a b : A} : eq a b -> leq a b.
Proof.
  intros e P.
  exact (eq_subst P e).
Defined.

Lemma leq_to_eq {A} {a b : A} : leq a b -> eq a b.
Proof.
  intro e.
  apply e.
  apply refl.
Defined.

Lemma leq_to_equal {A} {a b : A} : leq a b -> a = b.
Proof.
  intro H.
  apply H.
  reflexivity.
Defined.

Lemma equal_to_leq {A} {a b : A} : a = b -> leq a b.
Proof.
  intros [] P p.
  exact p.
Defined.

Lemma eq_eqv_equal : J_statement -> (forall {A} {x y : A}, eqv (eq x y) (x = y)).
Proof.
  intro J.
  intros A x y.
  exists eq_to_equal.
  apply eqv_intro.
  exists equal_to_eq.
  split.
  - intro e.
    apply (J A x y e).
    apply refl.
  - intros [].
    apply refl.
Defined.

Lemma eqv_eq_eq2 {A} {x y : A} : eqv (eq x y) ((x = y) * isEqv2 (id A)).
Proof.
  apply eqv_heq_heq5.
Defined.

(* It is not true in general that eqv A (A * B) implies eqv B unit, even when A is inhabited. For example, we can prove that eqv nat (nat * bool). *)

Fixpoint half (n : nat) :=
  match n with
  | 0 => 0
  | S (0) => 0
  | S (S (n)) => S (half n)
  end.

Fixpoint twice (n : nat) :=
  match n with
  | 0 => 0
  | S n => S (S (twice n))
  end.

Fixpoint even (n : nat) : bool :=
  match n with
  | 0 => true
  | S n => negb (even n)
  end.

Definition half_even (n : nat) : nat * bool := (half n, even n).
Definition half_even_inv (nb : nat * bool) : nat :=
  let (n, b) := nb in
  if b then twice n else S (twice n).

Lemma induction_scheme_step2 n P :
  P 0 -> P 1 -> (forall n, P n -> P (S (S n))) -> P n.
Proof.
  intros p0 p1 pSS.
  assert (P n * P (S n)) as H.
  - induction n.
    + split; assumption.
    + destruct IHn as (IHn, IHSn).
      specialize (pSS n IHn).
      split; assumption.
  - destruct H; assumption.
Defined.

Lemma negb_negb b : eq (negb (negb b)) b.
Proof.
  destruct b; apply refl.
Defined.

Definition S_fst (x : nat * bool) :=
  let (a, b) := x in (S a, b).

Lemma eqv_nat_2nat : eqv nat (nat * bool).
Proof.
  exists half_even.
  apply eqv_intro.
  exists half_even_inv.
  split.
  - intro n.
    apply (induction_scheme_step2 n).
    + apply refl.
    + apply refl.
    + unfold comp, id.
      simpl.
      intro m.
      case (even m).
      * simpl.
        intro H.
        apply (f_eq (fun n => S (S n))).
        assumption.
      * simpl.
        intro H.
        apply (f_eq (fun n => S (S n))).
        assumption.
  - intros (n, b).
    unfold comp, id.
    simpl.
    unfold half_even.
    induction n.
    + destruct b; apply refl.
    + simpl.
      destruct b.
      * simpl.
        apply (eq_subst (fun x => eq (S (half (twice n)), x) (S n, true)) (eq_sym (negb_negb (even (twice n))))).
        change (eq (S_fst (half (twice n), even (twice n))) (S_fst (n, true))).
        apply (f_eq S_fst).
        assumption.
      * change (eq (S_fst (half (S (twice n)), negb (negb (even (S (twice n)))))) (S_fst (n, false))).
        apply (f_eq S_fst).
        apply (eq_subst (fun x => eq (half (S (twice n)), x) (n, false)) (eq_sym (negb_negb (even (S (twice n)))))).
        assumption.
Defined.
