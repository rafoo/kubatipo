Definition idfun (A : Type) := fun x : A => x.

Inductive id {A : Type} (a : A) : A -> Type :=
| refl : id a a.

Notation "a == b" := (id a b) (at level 70).

Definition pinv {A B} (f : A -> B) (g : B -> A) := forall x : B, f (g x) == x.

Definition isEqv {A B} f :=
  ({ g : B -> A & pinv g f} * { g : B -> A & pinv f g})%type.

Definition eqv A B := sigT (@isEqv A B).

Notation "A ≃ B" := (eqv A B) (at level 70).

Definition eqv_fun {A B} (e : eqv A B) : A -> B :=
  let (f, _) := e in f.

Coercion eqv_fun : eqv >-> Funclass.

Lemma isEqv_intro {A B} {f : A -> B} g : pinv f g -> pinv g f -> isEqv f.
Proof.
  intros Hf Hg.
  split; exists g; assumption.
Defined.

Lemma eqv_refl A : A ≃ A.
Proof.
  exists (idfun A).
  apply (isEqv_intro (idfun A)); intro; reflexivity.
Defined.

Lemma id_to_eqv {A B} : A == B -> A ≃ B.
Proof.
  intros [].
  apply eqv_refl.
Defined.

Section with_univalence.

  (* We show that the following weak statements of univalence and
     functional extensionality imply the usual (strong) univalence
     axiom (forall A B : Type, isEqv (id_to_eqv A B)). *)

  Hypothesis weak_univalence : forall A B, (A ≃ B) ≃ (A == B).

  Hypothesis funext : forall A B (f g : A -> B),
      (forall x, f x == g x) -> f == g.

  (* From the two axioms, we derive eqv = eq. The axioms are not used
     afterwards. *)
  Lemma eqv_is_eq : eqv == id.
  Proof.
    apply funext; intro A.
    apply funext; intro B.
    apply weak_univalence.
    apply weak_univalence.
  Defined.

  (* From this equality, we can transport the induction principle for
     equality to equivalence. More precisely, we transfer the
     following variant of "based path induction" that avoids
     mentionning reflexivity. *)
  Definition has_eqind (eq : Type -> Type -> Type) :=
    forall (A : Type) (P : (forall B : Type, eq A B -> Type)) B e,
      {f : forall B' e', P B e -> P B' e' &
              f B e == idfun (P B e)}.

  (* equality satisfies has_eqind *)
  Lemma eqind : forall (A : Type) (P : (forall B : Type, A == B -> Type)) B e B' e',
      P B e -> P B' e'.
  Proof.
    intros A P B [] B' []. apply idfun.
  Defined.

  Lemma has_eqind_id : has_eqind id.
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
    apply has_eqind_id.
  Defined.

  Lemma eqv_eqind {A} (P : (forall B : Type, eqv A B -> Type)) B e B' e' :
    P B e -> P B' e'.
  Proof.
    apply has_eqind_eqv.
  Defined.

  Lemma eqv_eqind_idfun {A} (P : forall B, eqv A B -> Type) {B e} :
    eqv_eqind P B e B e == idfun (P B e).
  Proof.
    unfold eqv_eqind.
    destruct (has_eqind_eqv A P B e) as (f, H).
    exact H.
  Defined.

  (* By specializing to (B := A) and (e := eqv_refl A), we recover the
     usual based-path induction principle. *)
  Lemma eqv_eqind_refl {A} (P : (forall B : Type, eqv A B -> Type)) B e :
    P A (eqv_refl A) -> P B e.
  Proof.
    apply eqv_eqind.
  Defined.

  Lemma eqv_eqind_refl_idfun {A} (P : (forall B : Type, eqv A B -> Type)) :
    eqv_eqind_refl P _ _ == idfun (P A (eqv_refl A)).
  Proof.
    apply (eqv_eqind_idfun P).
  Defined.

  Lemma eqv_to_id {A B} : A ≃ B -> A == B.
  Proof.
    intro f.
    apply (eqv_eqind_refl (fun B f => A == B) B f).
    reflexivity.
  Defined.

  Lemma strong_univalence A B : isEqv (@id_to_eqv A B).
  Proof.
    apply (isEqv_intro eqv_to_id).
    - intro f.
      apply (eqv_eqind_refl (fun B f => id_to_eqv (eqv_to_id f) == f)).
      unfold eqv_to_id.
      rewrite eqv_eqind_refl_idfun.
      reflexivity.
    - intros [].
      unfold eqv_to_id.
      simpl.
      rewrite eqv_eqind_refl_idfun.
      reflexivity.
  Defined.

End with_univalence.
