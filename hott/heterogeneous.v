Require Import eqv.

(* This file aims to compare the following variations of heterogenous equality with and without the axioms of extensionality and univalence *)

(* This is Conor McBride's "John Major Equality" *)
Inductive heq0 : forall {A B}, A -> B -> Type :=
| hrefl0 : forall {A} (a : A), heq0 a a.

(* I propose this one, I do not know if it has been studied elsewhere. *)
Inductive heq1 : forall {A B}, (A -> B) -> A -> B -> Type :=
| hrefl1 : forall {A} a, heq1 (fun x : A => x) a a.

(* This one was proposed to me by François Thiré to simplify the
statement of symmetry. *)
Inductive heq2 : forall {A B}, (A -> B) -> (B -> A) -> A -> B -> Type :=
| hrefl2 : forall {A} a, heq2 (fun x : A => x) (fun x : A => x) a a.

(* This looks like a natural middle step between heq2 and heq4 *)
Inductive heq3 : forall {A B}, (eqv A B) -> A -> B -> Type :=
| hrefl3 : forall {A} a, heq3 (eqv_refl A) a a.

(* This one is pretty close to the heterogeneous equality of Cubical
Type Theory (CTT) but in CTT the type equality used is also
heterogeneous (recursively). *)
Inductive heq4 : forall {A B}, (A == B) -> A -> B -> Type :=
| hrefl4 : forall {A} a, heq4 (eq_refl A) a a.

(* This is not an heterogeneous equality but a property of functions
   that implies beeing an equivalence. It arises naturally
   in the study of heq1. *)
Inductive isStrongEqv : forall {A B}, (A -> B) -> Type :=
| isStrongEqv_id : forall A, isStrongEqv (id A).

Section going_down.

Lemma heq4to3 {A B} {e : A == B} {a b} :
  heq4 e a b ->
  heq3 (id_to_eqv e) a b.
Proof.
  intros [].
  apply hrefl3.
Defined.

Lemma heq4to2 {A B} {e : A == B} {a b} :
  heq4 e a b ->
  heq2 (id_to_eqv e) (id_to_eqv (eq_sym e)) a b.
Proof.
  intros [].
  apply hrefl2.
Defined.

Lemma heq4to1 {A B} {e : A == B} {a b} :
  heq4 e a b ->
  heq1 (id_to_eqv e) a b.
Proof.
  intros [].
  apply hrefl1.
Defined.

Lemma heq4to0 {A B} {e : A == B} {a b} :
  heq4 e a b ->
  heq0 a b.
Proof.
  intros [].
  apply hrefl0.
Defined.

Lemma heq3to2 {A B} {f : eqv A B} {a b} :
  heq3 f a b ->
  heq2 f (eqv_sym f) a b.
Proof.
  intros [].
  apply hrefl2.
Defined.

Lemma heq3to1 {A B} {f : eqv A B} {a b} :
  heq3 f a b ->
  heq1 f a b.
Proof.
  intros [].
  apply hrefl1.
Defined.

Lemma heq3to0 {A B} {f : eqv A B} {a b} :
  heq3 f a b ->
  heq0 a b.
Proof.
  intros [].
  apply hrefl0.
Defined.

Lemma heq2to1 {A B} {f : A -> B} {g a b} :
  heq2 f g a b ->
  heq1 f a b.
Proof.
  intros [].
  apply hrefl1.
Defined.

Lemma heq2to0 {A B} {f : A -> B} {g a b} :
  heq2 f g a b ->
  heq0 a b.
Proof.
  intros [].
  apply hrefl0.
Defined.

Lemma heq1to0 {A B} {f : A -> B} {a b} :
  heq1 f a b ->
  heq0 a b.
Proof.
  intros [].
  apply hrefl0.
Defined.

End going_down.

Section heq1_eqv_heq3.

(* I am too lazy to prove this, maybe this requires extensionality *)
Hypothesis isProp_isEqv : forall A B (f : A -> B), isProp (isEqv f).

Lemma isProp_diag : forall A B f x, isProp_isEqv A B f x x == eq_refl x.
Proof.
  intros A B f x.
  apply isProp_eq.
  apply isProp_isEqv.
Defined.

(* From heq1 we can go back to heq3 *)
Lemma heq1to3 {A B} {f : eqv A B} {a b} :
  heq1 f a b ->
  heq3 f a b.
Proof.
  destruct f as (f, Hf).
  simpl.
  intro e.
  destruct e.
  assert (Hf == isEqv_id A).
  + apply isProp_isEqv.
  + rewrite X.
    apply hrefl3.
Defined.

(* And it is actually an equivalence *)
Lemma heq1to3_eqv {A B} {f : eqv A B} {a b} :
  eqv (heq1 f a b) (heq3 f a b).
Proof.
  exists heq1to3.
  apply (isEqv_intro heq3to1).
  - intro e.
    destruct e.
    simpl.
    rewrite isProp_diag.
    reflexivity.
  - destruct f as (f, Hf).
    simpl.
    intro e.
    destruct e.
    assert (Hf == isEqv_id A).
    + apply isProp_isEqv.
    + rewrite X.
      rewrite isProp_diag.
      reflexivity.
Defined.

End heq1_eqv_heq3.

Section going_up_with_existentials.

(* From heq0, we can go back all the way up to heq4 by existentially
quantifying on the missing piece of information: an equality between
A and B *)

Lemma heq0to4_ex {A B} {a : A} {b : B} :
  heq0 a b ->
  {e : A == B & heq4 e a b}.
Proof.
  intros [].
  exists (eq_refl A0).
  apply hrefl4.
Defined.

Lemma heq4to0_ex {A B} {a : A} {b : B} :
  {e : A == B & heq4 e a b} -> heq0 a b.
Proof.
  intros (e, h).
  destruct h.
  apply hrefl0.
Defined.

Lemma heq0to4_ex_eqv {A B} {a : A} {b : B} :
  eqv (heq0 a b) {e : A == B & heq4 e a b}.
Proof.
  exists heq0to4_ex.
  apply (isEqv_intro heq4to0_ex).
  - intros (e, h4).
    destruct h4.
    reflexivity.
  - intro h.
    destruct h.
    reflexivity.
Defined.



Lemma heq1toeq {A B} {f : A -> B} {a b} : heq1 f a b -> b == f a.
Proof.
  intros [].
  apply eq_refl.
Defined.

Lemma heq1to2_ex {A B a b} {f : A -> B} : heq1 f a b -> {g : B -> A & heq2 f g a b}.
Proof.
  intros [].
  exists (fun x => x).
  apply hrefl2.
Defined.

Lemma heq1to2_eqv {A B a b} {f : A -> B} : eqv (heq1 f a b) {g : B -> A & heq2 f g a b}.
Proof.
  exists heq1to2_ex.
  apply (isEqv_intro (fun gh : {g : B -> A & heq2 f g a b} =>
                      let (_, h) := gh in heq2to1 h)).
  - intros (g, Hg).
    destruct Hg.
    reflexivity.
  - intro h.
    destruct h.
    reflexivity.
Defined.

Definition heq5 {A B} (f : A -> B) a b := (isStrongEqv f * (f a == b))%type.

Lemma heq1to5 {A B} {f : A -> B} {a b} : heq1 f a b -> heq5 f a b.
Proof.
  intros [].
  split.
  - apply isStrongEqv_id.
  - reflexivity.
Defined.

Lemma heq5to1 {A B} {f : A -> B} {a b} : heq5 f a b -> heq1 f a b.
Proof.
  intros (Hf, e).
  destruct Hf.
  unfold id in e.
  destruct e.
  apply hrefl1.
Defined.

Lemma heq1to5_eqv {A B} {f : A -> B} {a b} : eqv (heq1 f a b) (heq5 f a b).
Proof.
  exists heq1to5.
  apply (isEqv_intro heq5to1).
  - intros (Hf, e).
    destruct Hf.
    unfold id in e.
    destruct e.
    reflexivity.
  - intro h.
    destruct h.
    reflexivity.
Defined.

Definition seqv A B := {f : A -> B & isStrongEqv f}.

Definition seqv_fun {A B} (e : seqv A B) : A -> B :=
  let (f, _) := e in f.

Coercion seqv_fun : seqv >-> Funclass.

Lemma seqv_refl A : seqv A A.
Proof.
  exists (id A).
  apply isStrongEqv_id.
Defined.

Lemma seqv_to_eq {A B} : seqv A B -> A == B.
Proof.
  intros (f, Hf).
  destruct Hf.
  reflexivity.
Defined.

Lemma eq_to_seqv {A B} : A == B -> seqv A B.
Proof.
  intros [].
  apply seqv_refl.
Defined.

Lemma StrongEqv_eq {A B} : eqv (A == B) (seqv A B).
Proof.
  exists eq_to_seqv.
  apply (isEqv_intro seqv_to_eq).
  - intros (f, Hf).
    destruct Hf.
    reflexivity.
  - intros [].
    reflexivity.
Defined.

Lemma seqv_is_eq_to_seqv {A B} (f : seqv A B) : f == eq_to_seqv (seqv_to_eq f).
Proof.
  destruct f as (f, Hf).
  destruct Hf.
  reflexivity.
Defined.

Lemma eq_is_seqv_to_eq {A B} (e : A == B) : e == seqv_to_eq (eq_to_seqv e).
Proof.
  destruct e.
  reflexivity.
Defined.

Goal forall A B (e : A == B), (eq_to_seqv e : A -> B) == (id_to_eqv e : A -> B).
Proof.
  intros A B e.
  unfold eq_to_seqv, id_to_eqv.
  destruct e.
  reflexivity.
Defined.

Lemma heq5to4 {A B} {e : A == B} {a b} : eq_to_seqv e a == b -> heq4 e a b.
Proof.
  intro H.
  rewrite (eq_is_seqv_to_eq e).
  generalize H; clear H.
  generalize (eq_to_seqv e) as f.
  intro f; clear e.
  destruct f as (f, Hf).
  destruct Hf.
  simpl.
  intros [].
  apply hrefl4.
Defined.

Lemma heq4to5 {A B} {e : A == B} {a b} : heq4 e a b -> eq_to_seqv e a == b.
Proof.
  intro h4.
  destruct h4.
  reflexivity.
Defined.

Lemma heq4to5_eqv {A B} {e : A == B} {a b} :
  eqv (heq4 e a b) (eq_to_seqv e a == b).
Proof.
  exists heq4to5.
  apply (isEqv_intro heq5to4).
  - intro h.
    destruct e.
    simpl in h.
    unfold id in h.
    destruct h.
    reflexivity.
  - unfold pinv.
    intro h.
    destruct h.
    reflexivity.
Defined.

Lemma heq1_seqv_intro {A B} (f : seqv A B) a b : b == f a -> heq1 f a b.
Proof.
  rewrite (seqv_is_eq_to_seqv f).
  generalize (seqv_to_eq f).
  intro e; destruct e.
  simpl.
  unfold id.
  intro e; destruct e.
  apply hrefl1.
Defined.

Lemma heq1to4_eqv2 {A B} (f : A -> B) a b :
  eqv (heq1 f a b) {H : isStrongEqv f & (heq4 (seqv_to_eq (existT _ f H)) a b)}.
Proof.
  apply (eqv_trans heq1to5_eqv).
  unfold heq5.
  apply (eqv_trans eqv_prod_sigma).
  apply eqv_sym.
  apply sigT_eqv.
  intros Hf.
  apply (eqv_trans heq4to5_eqv).
  rewrite <- seqv_is_eq_to_seqv.
  apply eqv_refl.
Defined.


(* Going from heq1 to heq2 by taking as g the inverse of f (actually, any right pseudo-inverse) requires a weak version of functional extensionality *)
Definition id_to_fun {A B} (f g : forall x : A, B x) : f == g -> forall x, f x == g x.
Proof.
  intros [].
  reflexivity.
Defined.

Axiom functional_extensionality : forall A B (f g : forall x : A, B x), isEqv (id_to_fun f g).

Definition funext {A B} (f g : forall x : A, B x) :
  (forall x : A, f x == g x) -> f == g
  := isEqv_inv _ (functional_extensionality A B f g).

Lemma funext_id {A} f : (forall x : A, f x == x) -> f == (fun x => x).
Proof.
  apply funext.
Defined.

Lemma funext_inv1 {A B} {f g : forall x : A, B x} (p : f == g) :
  funext f g (id_to_fun f g p) == p.
Proof.
  unfold funext.
  apply isEqv_inv_eta.
Defined.

Lemma funext_refl {A B} {f : forall x : A, B x} :
  funext f f (fun x => eq_refl (f x)) == eq_refl f.
Proof.
  apply (funext_inv1 (eq_refl f)).
Defined.

Lemma fun_is_id_to_fun {A B} {f g : forall x : A, B x} (h : forall x, f x == g x) :
  h == id_to_fun f g (funext f g h).
Proof.
  unfold funext.
  apply eq_sym.
  apply isEqv_inv_eps.
Defined.

Lemma eq_is_funext {A B} {f g : forall x : A, B x} (h : f == g) :
  h == funext f g (id_to_fun f g h).
Proof.
  unfold funext.
  apply eq_sym.
  apply isEqv_inv_eta.
Defined.

Lemma funext_inj {A B} {f g : forall x : A, B x} (h1 h2 : forall x, f x == g x) :
  funext f g h1 == funext f g h2 -> h1 == h2.
Proof.
  intro H.
  rewrite (fun_is_id_to_fun h1).
  rewrite (fun_is_id_to_fun h2).
  rewrite H.
  reflexivity.
Defined.

Lemma heq1to2_all {A B} {f : A -> B} {a b} :
  forall g, pinv f g ->
            heq1 f a b ->
            heq2 f g a b.
Proof.
  intros g Hg.
  intros h.
  destruct h.
  apply (funext_id g) in Hg.
  rewrite Hg.
  apply hrefl2.
Defined.

Lemma heq1to2_alleqv {A B} {f : A -> B} {Hf : isEqv f} {a b} :
  heq1 f a b -> heq2 f (isEqv_inv f Hf) a b.
Proof.
  intro H.
  apply heq1to2_all.
  + apply isEqv_inv_eps.
  + assumption.
Defined.

(* Axiomatisation of the circle: all points of the circle are equal to
the base point and we have a non trivial equality between base and
base. *)

Variable Circle : Type.
Variable base : Circle.
Variable loop : base == base.
Variable eq_base : forall x : Circle, x == base.
Hypothesis eq_base_base : eq_base base == eq_refl base.
Hypothesis loop_not_refl : loop == eq_refl base -> Empty_set.

(* A non trivial proof of id = id *)
Definition id_is_id : id Circle == id Circle.
Proof.
  apply funext_id.
  intro x.
  unfold id.
  apply (transport (fun x => x == x) (eq_sym (eq_base x))).
  exact loop.
Defined.

Lemma id_is_id_is_not_refl : id_is_id == eq_refl _ -> Empty_set.
Proof.
  unfold id_is_id.
  rewrite <- funext_refl.
  unfold funext_id.
  fold (id Circle).
  intro H.
  apply funext_inj in H.
  assert (forall x : Circle, transport (fun x => x == x) (eq_sym (eq_base x)) loop == eq_refl _).
  - intro x.
    apply (id_to_fun _ _ H x).
  - specialize (X base).
    rewrite eq_base_base in X.
    simpl in X.
    apply loop_not_refl in X.
    assumption.
Defined.

(* going from heq1 or heq2 to heq4 is also possible using univalence.
   With univalence, we can also go from (b = f a /\ isEqv f) to heq1 *)

Section with_univalence.

  Variable univalence : forall A B, isEqv (@id_to_eqv A B).

  Definition ua {A B} : eqv A B -> A == B := isEqv_inv _ (univalence A B).

  Lemma ua_inv1 {A B} (p : A == B) : ua (id_to_eqv p) == p.
  Proof.
    unfold ua.
    apply isEqv_inv_eta.
  Defined.

  Lemma ua_refl A : ua (eqv_refl A) == eq_refl A.
  Proof.
    apply (ua_inv1 (eq_refl A)).
  Defined.

  Lemma eqv_is_ua {A B} (f : eqv A B) : f == id_to_eqv (ua f).
  Proof.
    unfold ua.
    apply eq_sym.
    apply isEqv_inv_eps.
  Defined.

  Lemma ua_sym {A B} {f : eqv A B} : ua (eqv_sym f) == eq_sym (ua f).
  Proof.
    rewrite (eqv_is_ua f).
    generalize (ua f).
    intro e.
    destruct e.
    rewrite ua_inv1.
    simpl.
    apply ua_refl.
  Defined.

  Lemma heq1_intro {A B} (f : eqv A B) a b : b == f a -> heq1 f a b.
  Proof.
    rewrite (eqv_is_ua f).
    generalize (ua f).
    intro e; destruct e.
    simpl.
    unfold id.
    intro e; destruct e.
    apply hrefl1.
  Defined.

  Lemma heq1to4 {A B} (f : eqv A B) a b : heq1 f a b -> heq4 (ua f) a b.
  Proof.
    rewrite (eqv_is_ua f).
    generalize (ua f).
    clear f.
    intro e.
    destruct e.
    rewrite ua_refl.
    simpl.
    intro H.
    apply heq1toeq in H.
    unfold id in H.
    destruct H.
    apply hrefl4.
  Defined.

  Lemma pinv_negb : pinv@{Type Type Type} negb negb.
  Proof.
    intros []; reflexivity.
  Defined.

  Definition NOT : eqv@{Type Type Type Type Type} bool bool.
  Proof.
    exists negb.
    apply (isEqv_intro negb); apply pinv_negb.
  Defined.

  Definition heq1_example: heq1 negb true false :=
    heq1_intro NOT true false (eq_refl false).

  Definition heq2_example: heq2 negb negb true false :=
    heq1to2_all negb pinv_negb heq1_example.

  Definition heq0_example: heq0 true false :=
    heq1to0 heq1_example.

  Definition heq4_example: heq4 (ua NOT) true false :=
    heq1to4 NOT true false heq1_example.

End with_univalence.
