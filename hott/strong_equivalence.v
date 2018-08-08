Set Universe Polymorphism.
Require Export eqv.

(* This file studies the properties of the following inductive type: *)
Inductive isStrongEqv : forall {A B} (f : A -> B), Type :=
| isStrongEqv_id : forall A, isStrongEqv (id A).

(* The main result is Univalence <-> (forall f, eqv (isEqv f) (isStrongEqv f))
                                 <-> (forall f, qinv f -> isStrongEqv f) *)

Definition seqv (A B : Type) := {f : A -> B & isStrongEqv f}.
Notation "A ≡ B" := (seqv A B) (at level 70).

Definition seqv_fun A B (e : A ≡ B) : A -> B :=
  let (f, _) := e in f.
Coercion seqv_fun : seqv >-> Funclass.

Lemma seqv_refl A : A ≡ A.
Proof.
  exists (id A).
  apply isStrongEqv_id.
Defined.

Lemma seqv_inv_fun {A B} (f : A ≡ B) : B -> A.
Proof.
  destruct f as (f, Hf).
  destruct Hf.
  apply id.
Defined.

Lemma seqv_sym {A B} (f : A ≡ B) : B ≡ A.
Proof.
  exists (seqv_inv_fun f).
  destruct f as (f, Hf).
  destruct Hf.
  apply isStrongEqv_id.
Defined.

Lemma seqv_sym_refl A : seqv_sym (seqv_refl A) == seqv_refl A.
Proof.
  reflexivity.
Defined.

Lemma seqv_sym_sym {A B} (f : A ≡ B) : seqv_sym (seqv_sym f) == f.
Proof.
  destruct f as (f, Hf).
  destruct Hf.
  reflexivity.
Defined.

Lemma seqv_trans {A B C} : A ≡ B -> B ≡ C -> A ≡ C.
Proof.
  intros (f, Hf) (g, Hg).
  exists (comp f g).
  destruct Hf.
  destruct Hg.
  apply isStrongEqv_id.
Defined.

Lemma seqv_refl_trans {A B} (e : A ≡ B) : seqv_trans (seqv_refl A) e = e.
Proof.
  destruct e as (f, Hf).
  destruct Hf.
  reflexivity.
Defined.

Lemma seqv_trans_refl {A B} (e : A ≡ B) : seqv_trans e (seqv_refl B) = e.
Proof.
  destruct e as (f, Hf).
  destruct Hf.
  reflexivity.
Defined.

Lemma seqv_sym_trans {A B C} (e1 : A ≡ B) (e2 : B ≡ C) :
  seqv_sym (seqv_trans e1 e2) = seqv_trans (seqv_sym e2) (seqv_sym e1).
Proof.
  destruct e1 as (f, Hf).
  destruct e2 as (g, Hg).
  destruct Hf.
  destruct Hg.
  reflexivity.
Defined.

Lemma seqv_to_eq {A B} : A ≡ B -> A == B.
Proof.
  intro f.
  destruct f as (f, Hf).
  destruct Hf.
  reflexivity.
Defined.

Lemma eq_to_seqv {A B} : A == B -> A ≡ B.
Proof.
  intros [].
  apply seqv_refl.
Defined.

Lemma is_seqv_to_eqv {A B} {f : A -> B} : isStrongEqv f -> isEqv f.
Proof.
  intro Hf.
  apply (isEqv_intro (seqv_inv_fun (existT _ f Hf))).
  - intro.
    destruct Hf.
    reflexivity.
  - intro.
    destruct Hf.
    reflexivity.
Defined.

Lemma seqv_to_eqv {A B} : A ≡ B -> A ≃ B.
Proof.
  intros (f, Hf).
  exists f.
  apply is_seqv_to_eqv.
  exact Hf.
Defined.

Lemma seqv_eqv_eq {A B} : (A ≡ B) ≃ (A == B).
Proof.
  exists seqv_to_eq.
  apply (isEqv_intro eq_to_seqv).
  - intros [].
    reflexivity.
  - intros (f, Hf).
    destruct Hf.
    reflexivity.
Defined.

Theorem seq_exponential : forall {A B} (s : A ≡ B) C, (C -> A) ≡ (C -> B).
Proof.
  intros A B (s, H) C.
  exists (fun h => comp h s).
  destruct H.
  apply isStrongEqv_id.
Defined.

Definition heq2 {A B} (f : A -> B) (a : A) (b : B) :=
  ((f a == b) * isStrongEqv f)%type.

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

Lemma eqv_heq_heq2 {A B} {f : A -> B} {a b} : heq f a b ≃ heq2 f a b.
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


(*
   We finally show that the following statements are equivalent:
   1. strong univalence : id_to_eqv is an equivalence
   2. funext + (A ≃ B) ≃ (A == B)
   3. eqv_induction (without beta)
   4. isEqv f -> isStrongEqv f
   5. eqv_induction (with beta)
   6. isEqv f ≃ isStrongEqv f
 *)

(*
   1->2 is folklore
 *)

Section from_weak_univ_and_funext_to_eqv_induction.

  Hypothesis funext : funext_statement.
  Hypothesis weak_univalence : forall A B, (A ≃ B) ≃ (A == B).

  Lemma eqv_is_eq : eqv == eq.
  Proof.
    apply funext.
    intro A.
    apply funext.
    intro B.
    apply weak_univalence.
    apply weak_univalence.
  Qed.

  (* From this equality, we can transport the induction principle for
     equality to equivalence. More precisely, we transfer the
     following variant of "based path induction" that avoids
     mentionning reflexivity. *)

  Definition has_eqind (eq : Type -> Type -> Type) :=
    forall (A : Type) (P : (forall B : Type, eq A B -> Type)) B e,
      {f : forall B' e', P B e -> P B' e' &
              f B e == id (P B e)}.

  (* @eq Type satisfies has_eqind *)
  Lemma eqind : forall (A : Type) (P : (forall B : Type, A == B -> Type)) B e B' e',
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

  Lemma eqv_eqind {A} (P : (forall B : Type, A ≃ B -> Type)) B e B' e' :
    P B e -> P B' e'.
  Proof.
    apply has_eqind_eqv.
  Defined.

  Lemma eqv_eqind_id {A} {P : forall B, A ≃ B -> Type} B e :
    eqv_eqind P B e B e == id (P B e).
  Proof.
    unfold eqv_eqind.
    destruct (has_eqind_eqv A P B e) as (F, H).
    exact H.
  Defined.

  Definition eqv_induction {A} (P : forall B, A ≃ B -> Type) B e :
    P A (eqv_refl A) -> P B e :=
    eqv_eqind P A (eqv_refl A) B e.

  Definition eqv_induction_beta {A} (P : forall B, A ≃ B -> Type) :
    eqv_induction P A (eqv_refl A) == id _ :=
    eqv_eqind_id A (eqv_refl A).

End from_weak_univ_and_funext_to_eqv_induction.

Section from_eqv_induction_and_isEqv_to_isStrongEqv.

  Variable eqv_induction : forall A (P : forall B, A ≃ B -> Type) B e,
    P A (eqv_refl A) -> P B e.

  Lemma eqv_to_isStrongEqv {A B} (f : A ≃ B) : isStrongEqv f.
  Proof.
    apply (eqv_induction A (fun B f => isStrongEqv f) B f).
    apply isStrongEqv_id.
  Defined.

  Lemma isEqv_to_isStrongEqv {A B} (f : A -> B) : isEqv f -> isStrongEqv f.
  Proof.
    intro H.
    pose (g := (existT _ f H : A ≃ B)).
    exact (eqv_to_isStrongEqv g).
  Defined.

End from_eqv_induction_and_isEqv_to_isStrongEqv.

Section from_eqvtoseqv_to_eqv_induction.

  Hypothesis iseqv_to_seqv : forall A B (f : A -> B), isEqv f -> isStrongEqv f.

  (* We first derive funext. This proof is taken from the HoTT book *)
  Section contractible_family.
    Variable A : Type.
    Variable P : A -> Type.
    Hypothesis C : forall x : A, isContr (P x).

    Lemma alpha : seqv (A -> {x : A & P x}) (A -> A).
    Proof.
      apply seq_exponential.
      exists (@projT1 A P).
      apply iseqv_to_seqv.
      intro x.
      exists (existT (fun w => projT1 w == x) (existT P x (projT1 (C x))) (eq_refl x)).
      intros ((x', p), Hx'x).
      simpl in Hx'x.
      destruct Hx'x.
      apply (f_equal (fun p => existT (fun x0 : {x : A & P x} => projT1 x0 == x') (existT P x' p) (eq_refl x'))).
      exact (projT2 (C x') p).
    Defined.

    Definition phi (f : forall x : A, P x) : fiber alpha (fun x : A => x) :=
      existT _ (fun x => existT P x (f x)) (eq_refl _).

    Definition psi (gp : fiber alpha (fun x : A => x)) (x : A) : P x.
      destruct gp as (g, p).
      unfold alpha in p.
      simpl in p.
      apply (transport (fun f => P (f x)) p).
      exact (projT2 (g x)).
    Defined.

    Lemma weak_extensionality : isContr (forall x, P x).
    Proof.
      apply (isContr_retract psi phi).
      - intro x.
        reflexivity.
      - destruct alpha as (alpha, Ha).
        simpl.
        apply is_seqv_to_eqv in Ha.
        apply Ha.
    Defined.
  End contractible_family.

  Definition funext :
    forall A B (f g : forall x : A, B x), (forall x, f x == g x) -> f == g :=
    eqv.funext weak_extensionality.

  Lemma eqv_to_seqv {A B} : A ≃ B -> A ≡ B.
  Proof.
    intros (f, Hf).
    exists f.
    apply iseqv_to_seqv.
    exact Hf.
  Defined.

  Lemma seqv_ind A (P : forall B, A ≡ B -> Type) B e B' e' :
    P B e -> P B' e'.
  Proof.
    destruct e' as (f', H').
    destruct H'.
    destruct e as (f, H).
    destruct H.
    apply id.
  Defined.

  Lemma seqv_ind_id A P B e : seqv_ind A P B e B e == id (P B e).
  Proof.
    destruct e as (f, H).
    destruct H.
    reflexivity.
  Defined.

  Lemma seqv_to_eqv_to_seqv A B (e : A ≃ B) : e == seqv_to_eqv (eqv_to_seqv e).
  Proof.
    destruct e as (f, H).
    simpl.
    apply f_equal.
    apply isProp_isEqv.
    exact funext.
  Defined.

  Lemma eqv_ind A (P : forall B, A ≃ B -> Type) B e B' e' :
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

  Lemma eqv_ind_id {A P} B e : eqv_ind A P B e B e == id (P B e).
  Proof.
    unfold eqv_ind.
    rewrite seqv_ind_id.
    unfold id.
    generalize (seqv_to_eqv_to_seqv A B e).
    intro H.
    destruct H.
    reflexivity.
  Defined.

  Definition eqv_induction' {A} (P : forall B, A ≃ B -> Type) B e :
    P A (eqv_refl A) -> P B e :=
    eqv_ind A P A (eqv_refl A) B e.

  Definition eqv_induction_beta' {A} (P : forall B, A ≃ B -> Type) :
    eqv_induction' P A (eqv_refl A) == id _ :=
    eqv_ind_id A (eqv_refl A).

End from_eqvtoseqv_to_eqv_induction.

Section from_eqv_induction_to_eqv_equivalence.

  Variable eqv_induction : forall A (P : forall B, A ≃ B -> Type) B e,
    P A (eqv_refl A) -> P B e.

  Hypothesis eqv_induction_beta : forall A (P : forall B, A ≃ B -> Type),
      eqv_induction A P A (eqv_refl A) == id _.

  Lemma iseqv_to_seqv {A B} (f : A -> B) : isEqv f -> isStrongEqv f.
  Proof.
    intro Hf.
    apply (eqv_induction A (fun B f => isStrongEqv f) B (existT _ f Hf)).
    apply isStrongEqv_id.
  Defined.

  Lemma isStrongEqv_to_isEqv {A B} (f : A -> B) : isStrongEqv f -> isEqv f.
  Proof.
    intros [].
    apply isEqv_id.
  Defined.

  Theorem eqv_eqv_seqv {A B} (f : A -> B) : eqv (isEqv f) (isStrongEqv f).
  Proof.
    exists (iseqv_to_seqv f).
    apply (isEqv_intro (isStrongEqv_to_isEqv f)).
    - intros [].
      simpl.
      unfold iseqv_to_seqv.
      rewrite eqv_induction_beta.
      reflexivity.
    - intro Hf.
      apply isProp_isEqv.
      exact (funext (@iseqv_to_seqv)).
  Defined.
End from_eqv_induction_to_eqv_equivalence.

Section from_eqv_equivalence_to_univalence.
  Hypothesis iseqv_eqv_isseqv : forall A B (f : A -> B), eqv (isEqv f) (isStrongEqv f).

  Lemma eqv_to_seqv' {A B} : A ≃ B -> A ≡ B.
  Proof.
    intros (f, e).
    exists f.
    apply iseqv_eqv_isseqv.
    exact e.
  Defined.

  Lemma seqv_to_eqv' {A B} : A ≡ B -> A ≃ B.
  Proof.
    intros (f, e).
    destruct e.
    apply eqv_refl.
  Defined.

  Lemma isProp_isEqv' {A B} {f : A -> B} : isProp (isEqv f).
  Proof.
    apply isProp_isEqv.
    exact (funext (@iseqv_eqv_isseqv)).
  Qed.

  Lemma isProp_isStrongEqv {A B} {f : A -> B} : isProp (isStrongEqv f).
  Proof.
    refine (isProp_eqv _ (iseqv_eqv_isseqv _ _ f)).
    apply isProp_isEqv'.
  Defined.

  Lemma eqv_eqv_seqv' {A B} : eqv (A ≃ B) (A ≡ B).
  Proof.
    exists eqv_to_seqv'.
    apply (isEqv_intro seqv_to_eqv').
    - intros (f, Hf).
      destruct Hf.
      simpl.
      destruct (iseqv_eqv_isseqv A A (id A)).
      apply f_equal.
      apply isProp_isStrongEqv.
    - intros (f, Hf).
      simpl.
      destruct (iseqv_eqv_isseqv A B f) as (g, Hg).
      destruct (g Hf).
      unfold eqv_refl.
      apply f_equal.
      apply isProp_isEqv'.
  Defined.

  Lemma ua {A B} : eqv (A ≃ B) (A == B).
  Proof.
    apply (eqv_trans eqv_eqv_seqv' seqv_eqv_eq).
  Defined.

  Lemma ua_refl A : ua (eqv_refl A) == eq_refl A.
  Proof.
    unfold ua.
    simpl.
    unfold comp.
    unfold eqv_to_seqv'.
    simpl.
    destruct (iseqv_eqv_isseqv A A (id A)) as (f, Hf).
    assert (f (isEqv_id A) == isStrongEqv_id A).
    - apply isProp_isStrongEqv.
    - rewrite X.
      reflexivity.
  Defined.

  Lemma ua_sym_refl A : eqv_sym ua (eq_refl A) == eqv_refl A.
  Proof.
    rewrite <- ua_refl.
    apply eqv_sym_eta.
  Defined.

  Lemma isEqv_id_to_eqv {A B} : isEqv (@id_to_eqv A B).
  Proof.
    apply (isEqv_homotopy (eqv_sym (@ua A B))).
    - destruct (eqv_sym (@ua A B)) as (e, He).
      exact He.
    - intros [].
      apply ua_sym_refl.
  Defined.

End from_eqv_equivalence_to_univalence.

Section corollaries.

  Hypothesis iseqv_eqv_isseqv : forall A B (f : A -> B), isEqv f ≃ isStrongEqv f.

  Corollary heq_eqv_eq {A B} (f : A ≡ B) {a b} : heq f a b ≃ (f a == b).
  Proof.
    apply (eqv_trans eqv_heq_heq2).
    apply (@eqv_trans _ ((f a == b) * unit)%type).
    - unfold heq2.
      apply eqv_prod.
      + apply eqv_refl.
      + apply isContr_unit.
        apply isProp_to_isContr.
        * destruct f.
          assumption.
        * apply isProp_isStrongEqv.
          apply iseqv_eqv_isseqv.
    - apply eqv_prod_unit.
  Defined.

  Corollary heq_id_eqv_eq {A} {a b} : heq (id A) a b ≃ (a == b).
  Proof.
    exact (@heq_eqv_eq A A (seqv_refl A) a b).
  Defined.

End corollaries.
