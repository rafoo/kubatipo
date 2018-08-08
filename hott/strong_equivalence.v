Set Universe Polymorphism.
Require Import eqv.
Require Setoid.

(* This file studies the properties of the following inductive type: *)
Inductive isStrongEqv : forall {A B} (f : A -> B), Type :=
| isStrongEqv_id : forall A, isStrongEqv (id A).

(* The main result is Univalence <-> (forall f, eqv (isEqv f) (isStrongEqv f))
                                 <-> (forall f, qinv f -> isStrongEqv f) *)

Definition seqv (A B : Type) := {f : A -> B & isStrongEqv f}.
Definition seqv_fun A B (e : seqv A B) : A -> B :=
  let (f, _) := e in f.
Coercion seqv_fun : seqv >-> Funclass.

Lemma seqv_refl A : seqv A A.
Proof.
  exists (id A).
  apply isStrongEqv_id.
Defined.

Lemma seqv_inv_fun {A B} (f : seqv A B) : B -> A.
Proof.
  destruct f as (f, Hf).
  destruct Hf.
  apply id.
Defined.

Lemma seqv_sym {A B} (f : seqv A B) : seqv B A.
Proof.
  exists (seqv_inv_fun f).
  destruct f as (f, Hf).
  destruct Hf.
  apply isStrongEqv_id.
Defined.

Lemma seqv_sym_refl A : seqv_sym (seqv_refl A) = seqv_refl A.
Proof.
  reflexivity.
Defined.

Lemma seqv_sym_sym {A B} (f : seqv A B) : seqv_sym (seqv_sym f) = f.
Proof.
  destruct f as (f, Hf).
  destruct Hf.
  reflexivity.
Defined.

Lemma seqv_trans {A B C} : seqv A B -> seqv B C -> seqv A C.
Proof.
  intros (f, Hf) (g, Hg).
  exists (comp f g).
  destruct Hf.
  destruct Hg.
  apply isStrongEqv_id.
Defined.

Lemma seqv_refl_trans {A B} (e : seqv A B) : seqv_trans (seqv_refl A) e = e.
Proof.
  destruct e as (f, Hf).
  destruct Hf.
  reflexivity.
Defined.

Lemma seqv_trans_refl {A B} (e : seqv A B) : seqv_trans e (seqv_refl B) = e.
Proof.
  destruct e as (f, Hf).
  destruct Hf.
  reflexivity.
Defined.

Lemma seqv_sym_trans {A B C} (e1 : seqv A B) (e2 : seqv B C) :
  seqv_sym (seqv_trans e1 e2) = seqv_trans (seqv_sym e2) (seqv_sym e1).
Proof.
  destruct e1 as (f, Hf).
  destruct e2 as (g, Hg).
  destruct Hf.
  destruct Hg.
  reflexivity.
Defined.

Lemma seqv_to_eq {A B} : seqv A B -> A = B.
Proof.
  intro f.
  destruct f as (f, Hf).
  destruct Hf.
  reflexivity.
Defined.

Lemma eq_to_seqv {A B} : A = B -> seqv A B.
Proof.
  intros [].
  apply seqv_refl.
Defined.

Lemma seqv_to_eqv {A B} : seqv A B -> eqv A B.
Proof.
  intros (f, Hf).
  exists f.
  apply (isEqv_intro (seqv_inv_fun (existT _ f Hf))).
  - intro.
    destruct Hf.
    reflexivity.
  - intro.
    destruct Hf.
    reflexivity.
Defined.

Lemma seqv_eqv_eq {A B} : eqv (seqv A B) (A = B).
Proof.
  exists seqv_to_eq.
  apply (isEqv_intro eq_to_seqv).
  - intros [].
    reflexivity.
  - intros (f, Hf).
    destruct Hf.
    reflexivity.
Defined.

Definition heq2 {A B} (f : A -> B) (a : A) (b : B) :=
  ((f a = b) * isStrongEqv f)%type.

Inductive heq : forall {A B : Type} (f : A -> B) (a : A) (b : B), Type :=
| refl {A} a : heq (id A) a a.

Lemma heq_heq2 {A B : Type} {f : A -> B} {a b} : heq f a b -> heq2 f a b.
Proof.
  intro h.
  destruct h.
  split.
  - reflexivity.
  - apply isStrongEqv_id.
Defined.

Lemma heq2_heq {A B : Type} {f : A -> B} {a b} : heq2 f a b -> heq f a b.
Proof.
  intros (e, Hf).
  destruct Hf.
  destruct e.
  apply refl.
Defined.

Lemma eqv_heq_heq2 {A B} {f : A -> B} {a b} : eqv (heq f a b) (heq2 f a b).
Proof.
  exists heq_heq2.
  apply (isEqv_intro heq2_heq).
  - intros (e, Hf).
    destruct Hf.
    destruct e.
    reflexivity.
  - intros [].
    reflexivity.
Defined.

Section with_univalence.

  Hypothesis univalence : forall A B, eqv (eqv A B) (A = B).

  Hypothesis funext : forall A B (f g : forall x : A, B x),
      (forall x, f x = g x) -> (fun x => f x) = (fun x => g x).

  Lemma eqv_is_eq : eqv = eq.
  Proof.
    apply funext.
    intro A.
    apply funext.
    intro B.
    apply univalence.
    apply univalence.
  Defined.

  (* From this equality, we can transport the induction principle for
     equality to equivalence. More precisely, we transfer the
     following variant of "based path induction" that avoids
     mentionning reflexivity. *)

  Definition has_eqind (eq : Type -> Type -> Type) :=
    forall (A : Type) (P : (forall B : Type, eq A B -> Type)) B e,
      {f : forall B' e', P B e -> P B' e' &
              f B e = id (P B e)}.

  (* @eq Type satisfies has_eqind *)
  Lemma eqind : forall (A : Type) (P : (forall B : Type, A = B -> Type)) B e B' e',
      P B e -> P B' e'.
  Proof.
    intros A P B e B' e'.
    destruct e.
    destruct e'.
    apply id.
  Defined.

  Lemma has_eqind_eq : has_eqind (@eq Type).
  Proof.
    intros A P B e.
    exists (eqind A P B e).
    destruct e.
    reflexivity.
  Defined.

  (* Hence eqv satisfies it. *)
  Lemma has_eqind_eqv : has_eqind eqv.
  Proof.
    rewrite eqv_is_eq.
    apply has_eqind_eq.
  Defined.

  Lemma eqv_eqind {A} (P : (forall B : Type, eqv A B -> Type)) B e B' e' :
    P B e -> P B' e'.
  Proof.
    apply has_eqind_eqv.
  Defined.

  Lemma eqv_eqind_id {A} {P : forall B, eqv A B -> Type} {B e} {p : P B e} :
    eqv_eqind P B e B e p = p.
  Proof.
    unfold eqv_eqind.
    destruct (has_eqind_eqv A P B e) as (f, H).
    rewrite H.
    reflexivity.
  Defined.

  Lemma eqv_to_isStrongEqv {A B} (f : eqv A B) : isStrongEqv f.
  Proof.
    apply (eqv_eqind (fun B f => isStrongEqv f) A (eqv_refl A) B f).
    apply isStrongEqv_id.
  Defined.

  Lemma eqv_to_isStrongEqv_refl A :
    eqv_to_isStrongEqv (eqv_refl A) = isStrongEqv_id A.
  Proof.
    unfold eqv_to_isStrongEqv.
    rewrite eqv_eqind_id.
    reflexivity.
  Defined.

  Lemma isEqv_to_isStrongEqv {A B} (f : A -> B) : isEqv f -> isStrongEqv f.
  Proof.
    intro H.
    pose (g := (existT _ f H : eqv A B)).
    exact (eqv_to_isStrongEqv g).
  Defined.

  Lemma isStrongEqv_to_isEqv {A B} (f : A -> B) : isStrongEqv f -> isEqv f.
  Proof.
    intros [].
    apply isEqv_id.
  Defined.

  Theorem eqv_eqv_seqv {A B} (f : A -> B) : eqv (isEqv f) (isStrongEqv f).
  Proof.
    exists (isEqv_to_isStrongEqv f).
    apply (isEqv_intro (isStrongEqv_to_isEqv f)).
    - intros [].
      simpl.
      unfold isEqv_to_isStrongEqv.
      exact (eqv_to_isStrongEqv_refl A0).
    - intro Hf.
      apply isProp_isEqv.
      exact funext.
  Defined.

  (* Corrolaries: forall f, isProp (isStrongEqv f) *)

  Corollary isProp_isStrongEqv {A B} {f : A -> B} : isProp (isStrongEqv f).
  Proof.
    refine (isProp_eqv _ (eqv_eqv_seqv f)).
    apply isProp_isEqv.
    exact funext.
  Defined.

  Corollary heq_eqv_eq {A B} (f : seqv A B) {a b} : eqv (heq f a b) (f a = b).
  Proof.
    apply (eqv_trans eqv_heq_heq2).
    apply (@eqv_trans _ ((f a = b) * unit)%type).
    - unfold heq2.
      apply eqv_prod.
      + apply eqv_refl.
      + apply isContr_unit.
        apply isProp_to_isContr.
        * destruct f.
          assumption.
        * apply isProp_isStrongEqv.
    - apply eqv_prod_unit.
  Defined.

  Corollary heq_id_eqv_eq {A} {a b} : eqv (heq (id A) a b) (a = b).
  Proof.
    exact (@heq_eqv_eq A A (seqv_refl A) a b).
  Defined.

  Lemma ua2 {A B} : eqv (eqv A B) (A = B).
  Proof.
    apply (@eqv_trans _ (seqv A B)).
    - apply sigT_eqv.
      exact eqv_eqv_seqv.
    - exact seqv_eqv_eq.
  Defined.

  Lemma ua2_refl {A} : ua2 (eqv_refl A) = eq_refl A.
  Proof.
    unfold ua2, eqv_trans.
    simpl.
    unfold comp.
    simpl.
    assert (isEqv_to_isStrongEqv (id A) (isEqv_id A) = isStrongEqv_id A).
    + apply isProp_isStrongEqv.
    + rewrite H.
      reflexivity.
  Defined.

  Lemma strong_univalence A B : isEqv (@id_to_eqv A B).
  Proof.
    assert (@id_to_eqv A B = eqv_sym (@ua2 A B)).
    + apply funext.
      intros [].
      change (eqv_refl A = (eqv_sym ua2) eq_refl).
      transitivity ((eqv_sym ua2) (ua2 (eqv_refl A))).
      * destruct ua2 as (ua2, Hu).
        simpl.
        symmetry.
        apply isEqv_inv_eta.
      * f_equal.
        apply ua2_refl.
    + rewrite H.
      destruct (eqv_sym (ua2)).
      assumption.
  Defined.

End with_univalence.


Section with_qinv_to_seqv.
  Hypothesis iseqv_to_seqv : forall A B (f : A -> B), isEqv f -> isStrongEqv f.

  Theorem seq_exponential : forall {A B} (s : seqv A B) C, seqv (C -> A) (C -> B).
  Proof.
    intros A B (s, H) C.
    exists (fun h => comp h s).
    destruct H.
    apply isStrongEqv_id.
  Defined.

  Definition path_pred A := fun xy : A * A => fst xy = snd xy.

  Definition path_space A := sigT (path_pred A).

  Definition src A : seqv (path_space A) A.
  Proof.
    exists (fun p => fst (projT1 p)).
    apply iseqv_to_seqv.
    intros x.
    eexists (existT _ (existT (fun (xy : A * A) => fst xy = snd xy) (x, x) (eq_refl x)) _).
    intros [[[u v] p] q].
    unfold path_pred in p.
    simpl in * |- *.
    destruct q.
    destruct p.
    reflexivity.
  Defined.

  Definition trg A : seqv (path_space A) A.
  Proof.
    exists (fun p => snd (projT1 p)).
    apply iseqv_to_seqv.
    intros x.
    eexists (existT _ (existT (fun (xy : A * A) => fst xy = snd xy) (x, x) (eq_refl x)) _).
    intros [[[u v] p] q].
    unfold path_pred in p.
    simpl in * |- *.
    destruct q.
    destruct p.
    reflexivity.
  Defined.

  Lemma seq_injective U V : forall (s : seqv U V) x y, s x = s y -> x = y.
  Proof.
    intros (s, H) x y p.
    destruct H.
    exact p.
  Qed.

  Theorem extensionality {A B : Type} (f g : A -> B) : (forall x, f x = g x) -> f = g.
  Proof.
    intro p.
    pose (d := fun x : A => existT (path_pred B) (f x, f x) (eq_refl (f x))).
    pose (e := fun x : A => existT (path_pred B) (f x, g x) (p x)).
    pose (src_compose := seq_exponential (src B) A).
    pose (trg_compose := seq_exponential (trg B) A).
    transitivity (projT1 trg_compose e); try auto.
    transitivity (projT1 trg_compose d); try auto.
    f_equal.
    apply seq_injective with (s := src_compose).
    reflexivity.
  Qed.

End with_qinv_to_seqv.


Section with_qinv_to_seqv_and_funext.

  Hypothesis iseqv_to_seqv : forall A B (f : A -> B), isEqv f -> isStrongEqv f.
  Hypothesis funext :
    forall A B (f g : forall x : A, B x), (forall x, f x = g x) -> f = g.

  Lemma eqv_to_seqv {A B} : eqv A B -> seqv A B.
  Proof.
    intros (f, Hf).
    exists f.
    apply iseqv_to_seqv.
    exact Hf.
  Defined.

  Lemma seqv_ind A (P : forall B, seqv A B -> Type) B e B' e' :
    P B e -> P B' e'.
  Proof.
    destruct e' as (f', H').
    destruct H'.
    destruct e as (f, H).
    destruct H.
    apply id.
  Defined.

  Lemma seqv_ind_id A P B e : seqv_ind A P B e B e = id (P B e).
  Proof.
    destruct e as (f, H).
    destruct H.
    reflexivity.
  Defined.

  Lemma seqv_to_eqv_to_seqv A B (e : eqv A B) : e = seqv_to_eqv (eqv_to_seqv e).
  Proof.
    destruct e as (f, H).
    simpl.
    f_equal.
    apply isProp_isEqv.
    exact funext.
  Defined.

  Lemma eqv_ind A (P : forall B, eqv A B -> Type) B e B' e' :
    P B e -> P B' e'.
  Proof.
    intro p.
    rewrite seqv_to_eqv_to_seqv.
    pose (P' := fun B e => P B (seqv_to_eqv e)).
    apply (seqv_ind _ P' B (eqv_to_seqv e) B' (eqv_to_seqv e')).
    unfold P'.
    rewrite <- seqv_to_eqv_to_seqv.
    exact p.
  Defined.

  Lemma eqv_ind_id A P B e : eqv_ind A P B e B e = id (P B e).
  Proof.
    unfold eqv_ind.
    rewrite seqv_ind_id.
    unfold id.
    generalize (seqv_to_eqv_to_seqv A B e).
    intro H.
    destruct H.
    reflexivity.
  Defined.

  Lemma new_eqv_to_seqv {A B} : eqv A B -> seqv A B.
  Proof.
    intro e.
    apply (eqv_ind A (fun B e => seqv A B) A (eqv_refl A) B e).
    apply seqv_refl.
  Defined.

  Lemma new_seqv_to_eqv {A B} : seqv A B -> eqv A B.
  Proof.
    intro e.
    apply (seqv_ind A (fun B e => eqv A B) A (seqv_refl A) B e).
    apply eqv_refl.
  Defined.

  Lemma new_eqv_eqv_seqv {A B} : eqv (eqv A B) (seqv A B).
  Proof.
    exists new_eqv_to_seqv.
    apply (isEqv_intro new_seqv_to_eqv).
    - intros (f, Hf).
      destruct Hf.
      simpl.
      unfold new_eqv_to_seqv, new_seqv_to_eqv.
      rewrite eqv_ind_id.
      reflexivity.
    - intros (f, Hf).
      unfold new_eqv_to_seqv, new_seqv_to_eqv.
      assert (Hf2 : isStrongEqv f).
      + apply iseqv_to_seqv.
        assumption.
      + destruct Hf2.
        rewrite (isProp_isEqv funext (id A) Hf (isEqv_id A)).
        rewrite eqv_ind_id.
        rewrite seqv_ind_id.
        reflexivity.
  Defined.

  Lemma univalence {A B} : eqv (eqv A B) (A = B).
  Proof.
    apply (eqv_trans new_eqv_eqv_seqv seqv_eqv_eq).
  Defined.

  Lemma univalence_refl A : univalence (eqv_refl A) = eq_refl.
  Proof.
    unfold univalence.
    simpl.
    unfold comp.
    unfold new_eqv_to_seqv.
    rewrite eqv_ind_id.
    reflexivity.
  Defined.

  Lemma univalence_sym_refl A : eqv_sym univalence (eq_refl A) = eqv_refl A.
  Proof.
    rewrite <- univalence_refl.
    apply eqv_sym_eta.
  Defined.

  Lemma isEqv_id_to_eqv {A B} : isEqv (@id_to_eqv A B).
  Proof.
    apply (isEqv_homotopy (eqv_sym (@univalence A B))).
    - destruct (eqv_sym (@univalence A B)) as (e, He).
      exact He.
    - intros [].
      apply univalence_sym_refl.
  Defined.

End with_qinv_to_seqv_and_funext.
