Set Universe Polymorphism.

Definition comp {A B C : Type} (f : A -> B) (g : B -> C) := fun x => g (f x).
Definition id (A : Type) := fun x : A => x.

Lemma eq_trans_assoc {A} {w x y z : A} (p1 : eq w x) (p2 : eq x y) (p3 : eq y z) :
  eq_trans (eq_trans p1 p2) p3 = eq_trans p1 (eq_trans p2 p3).
Proof.
  destruct p3.
  reflexivity.
Defined.

Lemma eq_trans_sym {A} {x y : A} (p1 : eq x y) :
  eq_trans p1 (eq_sym p1) = eq_refl.
Proof.
  destruct p1.
  reflexivity.
Defined.

Lemma eq_trans_sym_eq {A} {x y z : A} (p : x = y) (q : x = z) (r : y = z) :
  q = eq_trans p r -> eq_trans (eq_sym p) q = r.
Proof.
  destruct r; simpl; destruct q; simpl.
  intros [].
  reflexivity.
Defined.

Lemma f_equal_id {A} {x y : A} (p : x = y) : f_equal (id A) p = p.
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma f_equal_comp {A B C} (f : A -> B) (g : B -> C) x y (p : x = y) :
  f_equal g (f_equal f p) = f_equal (comp f g) p.
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma natural_transf {A B} {f g : A -> B} (H : forall x, f x = g x) x y (p : x = y) :
  eq_trans (H x) (f_equal g p) = eq_trans (f_equal f p) (H y).
Proof.
  destruct p.
  simpl.
  destruct (H x).
  reflexivity.
Defined.

Definition isContr (A : Type) := {x : A & forall y : A, x = y}.
Definition isProp A := forall a b : A, a = b.

Definition funext_statement :=
  forall A B (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g.

Definition pinv {A B} (f : A -> B) (g : B -> A) :=
  forall x : B, f (g x) = x.

Definition qinv {A B} (f : A -> B) := {g : B -> A & ((pinv f g) * (pinv g f))%type}.

Definition fiber {A B} (f : A -> B) (y : B) := {x : A & f x = y}.

(* We choose this definition for equivalence (contractible function)
because a rather weak form of functional extensionality is enough to
prove that it is a mere proposition. *)
Definition isEqv {A B} (f : A -> B) :=
  forall y : B, isContr (fiber f y).

Definition eqv A B := sigT (@isEqv A B).

Definition eqv_fun {A B} (e : eqv A B) : A -> B :=
  let (f, _) := e in f.

Coercion eqv_fun : eqv >-> Funclass.

(* This other possible definition of equivalence is used to show qinv f -> isEqv f *)
Definition half_adjoint {A B} f :=
  { g : B -> A &
  { eta : pinv g f &
  { eps : pinv f g &
          forall x, f_equal f (eta x) = eps (f x)}}}.

Lemma qinv_half_adjoint {A B} (f : A -> B) : qinv f -> half_adjoint f.
  intros (g, (eps, eta)).
  exists g.
  exists eta.
  exists (fun b => eq_trans (eq_sym (eps (f(g(b))))) (eq_trans (f_equal f (eta (g b))) (eps b))).
  intro a.
  symmetry.
  assert (eta (g (f a)) = f_equal g (f_equal f (eta a))).
  - assert (forall p, eq_trans (eta (g (f a))) p = eq_trans (f_equal g (f_equal f p)) (eta a)).
    + intro p.
      destruct p.
      simpl.
      destruct (eta (g (f a))).
      reflexivity.
    + specialize (H (eta a)).
      apply (f_equal (fun e => eq_trans e (eq_sym (eta a)))) in H.
      rewrite eq_trans_assoc in H.
      rewrite eq_trans_sym in H.
      simpl in H.
      rewrite eq_trans_assoc in H.
      rewrite eq_trans_sym in H.
      exact H.
  - rewrite H.
    apply eq_trans_sym_eq.
    rewrite f_equal_comp.
    symmetry.
    refine (eq_trans _ (natural_transf eps _ _ (f_equal f (eta a)))).
    rewrite f_equal_id.
    reflexivity.
Defined.

Lemma half_adjoint_isEqv {A B} (f : A -> B) :
  half_adjoint f -> isEqv f.
Proof.
  intros (g, (eta, (eps, tau))) y.
  exists (existT _ (g y) (eps y)).
  intros (x, Hx).
  destruct Hx.
  rewrite <- tau.
  destruct (eta x).
  reflexivity.
Defined.

Lemma qinv_isEqv {A B} {f : A -> B} : qinv f -> isEqv f.
Proof.
  intro H.
  apply half_adjoint_isEqv.
  apply qinv_half_adjoint.
  exact H.
Defined.

(* Going in the other direction (from isEqv to qinv) is easy: *)
Definition isEqv_inv {A B} (f : A -> B) :
  isEqv f -> B -> A.
Proof.
  intros Hf y.
  destruct (Hf y) as ((x, _), _).
  exact x.
Defined.

Lemma isEqv_inv_eta {A B} (f : A -> B) (Hf : isEqv f) :
  pinv (isEqv_inv f Hf) f.
Proof.
  intro x.
  unfold isEqv_inv.
  destruct (Hf (f x)) as ((x', Hx'), H').
  specialize (H' (existT (fun x' => f x' = f x) x eq_refl)).
  apply (f_equal (@projT1 A (fun x' => f x' = f x))) in H'.
  exact H'.
Defined.

Lemma isEqv_inv_eps {A B} (f : A -> B) (Hf : isEqv f) :
  pinv f (isEqv_inv f Hf).
Proof.
  intro y.
  unfold isEqv_inv.
  destruct (Hf y) as ((x', Hx'), H').
  assumption.
Defined.

Lemma isEqv_qinv {A B} (f : A -> B) : isEqv f -> qinv f.
Proof.
  intro Hf.
  exists (isEqv_inv _ Hf).
  split.
  - apply isEqv_inv_eps.
  - apply isEqv_inv_eta.
Defined.

Section with_funext.
  Hypothesis funext : funext_statement.

  Lemma isProp_isContr A : isProp (isContr A).
  Proof.
    intros a b.
    destruct a as (a, Ha).
    destruct b as (b, Hb).
    transitivity
      (existT (fun x : A => forall y : A, x = y) a
              (fun y => eq_trans (Ha b) (Hb y))).
    - f_equal.
      apply funext.
      intro c.
      destruct (Hb c).
      reflexivity.
    - destruct (Ha b).
      f_equal.
      apply funext.
      intro b.
      destruct (Hb b).
      reflexivity.
  Defined.

  Lemma isProp_isEqv {A B} (f : A -> B) :
    isProp (isEqv f).
  Proof.
    intros H1 H2.
    apply funext.
    intro x.
    apply isProp_isContr.
  Defined.
End with_funext.

Lemma isEqv_id A : isEqv (id A).
Proof.
  apply qinv_isEqv.
  exists (id A).
  split; exact (fun x => eq_refl).
Defined.

Definition eqv_refl A : eqv A A := existT _ (id A) (isEqv_id A).

Lemma id_to_eqv {A B} : A = B -> eqv A B.
Proof.
  intros [].
  apply eqv_refl.
Defined.

Lemma f_equal_trans {A B} (f : A -> B) x y z (p : x = y) (q : y = z):
  f_equal f (eq_trans p q) = eq_trans (f_equal f p) (f_equal f q).
Proof.
  destruct q.
  reflexivity.
Defined.

Lemma f_equal_sym {A B} (f : A -> B) x y (p : x = y) :
  f_equal f (eq_sym p) = eq_sym (f_equal f p).
Proof.
  destruct p.
  reflexivity.
Defined.

Lemma isEqv_intro {A B} {f : A -> B} g : pinv f g -> pinv g f -> isEqv f.
Proof.
  intros eps eta.
  apply qinv_isEqv.
  exists g.
  split; assumption.
Defined.

Lemma inv_isEqv {A B} {f : A -> B} (H : isEqv f) : isEqv (isEqv_inv f H).
Proof.
  apply (isEqv_intro f).
  - apply isEqv_inv_eta.
  - apply isEqv_inv_eps.
Defined.

Lemma eqv_sym {A B} : eqv A B -> eqv B A.
Proof.
  intros (f, H).
  exists (isEqv_inv f H).
  apply inv_isEqv.
Defined.

Lemma eqv_sym_eps {A B} (f : eqv A B) : pinv f (eqv_sym f).
Proof.
  destruct f as (f, Hf).
  simpl.
  apply isEqv_inv_eps.
Defined.

Lemma eqv_sym_eta {A B} (f : eqv A B) : pinv (eqv_sym f) f.
Proof.
  destruct f as (f, Hf).
  simpl.
  apply isEqv_inv_eta.
Defined.

Lemma eqv_trans {A B C} : eqv A B -> eqv B C -> eqv A C.
Proof.
  intros (f, Hf) (g, Hg).
  exists (comp f g).
  apply (isEqv_intro (comp (isEqv_inv g Hg) (isEqv_inv f Hf))).
  - intro c.
    unfold comp.
    rewrite isEqv_inv_eps.
    apply isEqv_inv_eps.
  - intro a.
    unfold comp.
    rewrite isEqv_inv_eta.
    apply isEqv_inv_eta.
Defined.

Lemma isContr_retract {A B} (f : A -> B) (g : B -> A) :
  pinv f g -> isContr A -> isContr B.
Proof.
  intros H (a, Ha).
  exists (f a).
  intro y.
  rewrite <- H.
  f_equal.
  apply Ha.
Defined.

Lemma happly {A B} (f g : forall x : A, B x) : f = g -> forall x, f x = g x.
Proof.
  intros [].
  reflexivity.
Defined.

Lemma between_contr_isEqv {A B} (f : A -> B) :
  isContr A -> isContr B -> isEqv f.
Proof.
  intros (a, HA) (b, HB).
  apply qinv_isEqv.
  exists (fun y => a).
  split.
  - intro y.
    transitivity b.
    + symmetry.
      apply HB.
    + apply HB.
  - intro x.
    apply HA.
Defined.

Lemma isContr_eqv {A B} (f : eqv A B) : isContr A -> isContr B.
Proof.
  intros (a, HA).
  exists (f a).
  intro y.
  specialize (HA (eqv_sym f y)).
  rewrite HA.
  apply eqv_sym_eps.
Defined.

Definition total {A P Q} (f : forall x : A, P x -> Q x) :
  {x : A & P x} -> {x : A & Q x} :=
  (fun w => existT Q (projT1 w) (f (projT1 w) (projT2 w))).

Definition transport {A} (P : A -> Type) {x y : A} (p : x = y) : P x -> P y.
Proof.
  destruct p; auto.
Defined.

Lemma fiber_total_fun {A P Q} (f : forall x : A, P x -> Q x) (w : sigT Q) :
  (fiber (total f) w) -> (fiber (f (projT1 w)) (projT2 w)).
Proof.
  intros ((a, p), H).
  unfold total in H.
  simpl in H.
  unfold fiber.
  exists (transport P (f_equal (@projT1 A Q) H) p).
  destruct H.
  reflexivity.
Defined.

Lemma fiber_total_inv {A P Q} (f : forall x : A, P x -> Q x) (w : sigT Q) :
  (fiber (f (projT1 w)) (projT2 w)) -> (fiber (total f) w).
Proof.
  destruct w as (x, v).
  intros (p, H).
  unfold total, fiber.
  exists (existT P x p).
  simpl.
  f_equal.
  exact H.
Defined.

Lemma fiber_total {A P Q} (f : forall x : A, P x -> Q x) w :
  eqv (fiber (total f) w) (fiber (f (projT1 w)) (projT2 w)).
Proof.
  exists (fiber_total_fun f w).
  apply (isEqv_intro (fiber_total_inv f w)).
  - destruct w as (x, v).
    simpl.
    intros (p, H).
    simpl.
    destruct H.
    reflexivity.
  - intros ((a, p), H).
    simpl.
    destruct H.
    reflexivity.
Defined.

Definition fiberwise_eqv {A P Q} (f : forall x : A, P x -> Q x) :=
  forall x, isEqv (f x).

Lemma fiberwise_eqv_total {A P Q} (f : forall x : A, P x -> Q x) :
  fiberwise_eqv f -> isEqv (total f).
Proof.
  intro H.
  unfold isEqv.
  intros w.
  apply (isContr_eqv (eqv_sym (fiber_total f w))).
  apply H.
Defined.

Lemma fiberwise_eqv_total_rev {A P Q} (f : forall x : A, P x -> Q x) :
  isEqv (total f) -> fiberwise_eqv f.
Proof.
  unfold isEqv.
  intros H x.
  intro q.
  apply (isContr_eqv (fiber_total f (existT Q x q))).
  apply H.
Defined.

Section with_weak_funext.

  (* The proof of weak-funext -> funext from the HoTT book. *)

  Hypothesis weak_funext : forall A (P : A -> Type),
    (forall x, isContr (P x)) -> isContr (forall x, P x).

  Definition codom_happly1 {A B} (f : forall x : A, B x) :=
    {g : forall x, B x & forall x, f x = g x}.

  Lemma codom_happly1_to_fun {A B} (f : forall x : A, B x) :
    codom_happly1 f -> forall x, {u : B x & f x = u}.
  Proof.
    intros (g, H) x.
    exists (g x).
    apply H.
  Defined.

  Lemma fun_to_codom_happly1 {A B} (f : forall x : A, B x) :
    (forall x, {u : B x & f x = u}) -> codom_happly1 f.
  Proof.
    intros H.
    exists (fun x => projT1 (H x)).
    intro x.
    destruct (H x) as (u, Hu).
    exact Hu.
  Defined.

  Lemma isEqv_happly {A B} (f g : forall x : A, B x) : isEqv (happly f g).
  Proof.
    generalize g; clear g.
    apply fiberwise_eqv_total_rev.
    apply between_contr_isEqv.
    - exists (existT _ f eq_refl).
      intros (g, H).
      destruct H.
      reflexivity.
    - apply (isContr_retract (fun_to_codom_happly1 f) (codom_happly1_to_fun f)).
      + intros (g, H).
        reflexivity.
      + apply weak_funext.
        intro x.
        exists (existT _ (f x) eq_refl).
        intros (y, Hy).
        destruct Hy.
        reflexivity.
  Qed.

  Lemma happly_eqv {A B} (f g : forall x : A, B x) : eqv (f = g) (forall x, f x = g x).
  Proof.
    exists (happly f g).
    apply isEqv_happly.
  Defined.

  Theorem funext : funext_statement.
  Proof.
    intros A B f g.
    exact (eqv_sym (happly_eqv f g)).
  Defined.

  Lemma funext_id {A B} {f : forall x : A, B x} :
    funext A B f f (fun x => eq_refl (f x)) = eq_refl f.
  Proof.
    change (funext A B f f (happly_eqv f f (eq_refl f)) = eq_refl f).
    apply (eqv_sym_eta (happly_eqv f f)).
  Defined.

End with_weak_funext.

Definition FUNEXT := forall A B (f g : forall x : A, B x), isEqv (happly f g).


Lemma isProp_prod {A B} : isProp A -> isProp B -> isProp (A * B).
Proof.
  intros HA HB (a1, b1) (a2, b2).
  specialize (HA a1 a2).
  destruct HA.
  specialize (HB b1 b2).
  destruct HB.
  reflexivity.
Defined.

Lemma Dep_Funext (funext : FUNEXT) {A B} (f g : forall x : A, B x) :
  (forall x, f x = g x) -> f = g.
Proof.
  apply eqv_fun.
  apply eqv_sym.
  exists (happly f g).
  apply funext.
Defined.

Lemma Dep_Funext_funapp (funext : FUNEXT) {A B} (f g : forall x : A, B x) e :
  Dep_Funext funext f g (fun x => happly f g e x) = e.
Proof.
  apply isEqv_inv_eta.
Defined.

Lemma Dep_Funext_refl (funext : FUNEXT) {A B} (f : forall x : A, B x) :
  Dep_Funext funext f f (fun x => eq_refl) = eq_refl.
Proof.
  exact (Dep_Funext_funapp funext f f eq_refl).
Defined.

Lemma comp_id_pinv_eqv {A B} (f : A -> B) (g : B -> A) :
  FUNEXT -> eqv (pinv f g) (comp g f = id B).
Proof.
  unfold FUNEXT.
  intro funext.
  apply eqv_sym.
  eexists.
  exact (funext _ _ (comp g f) (id B)).
Defined.

Lemma sigT_eqv_fun {A B1 B2} :
  (forall x : A, eqv (B1 x) (B2 x)) ->
  {x : A & B1 x} -> {x : A & B2 x}.
Proof.
  intro H.
  intros (a, b).
  exists a.
  specialize (H a).
  exact (H b).
Defined.

Lemma sigT_eqv_pinv {A B1 B2} {H : forall x : A, eqv (B1 x) (B2 x)} :
  pinv (sigT_eqv_fun H) (sigT_eqv_fun (fun x => eqv_sym (H x))).
Proof.
  intros (a, b).
  simpl.
  assert ((H a) ((eqv_sym (H a)) b) = b).
  - generalize (H a).
    intros (F, HF).
    unfold eqv_sym.
    simpl.
    apply isEqv_inv_eps.
  - rewrite H0.
    reflexivity.
Defined.

Lemma sigT_eqv_pinv2 {A B1 B2} {H : forall x : A, eqv (B1 x) (B2 x)} :
  pinv (sigT_eqv_fun (fun x => eqv_sym (H x))) (sigT_eqv_fun H).
Proof.
  intros (a, b).
  simpl.
  assert (((eqv_sym (H a)) ((H a) b)) = b).
  - generalize (H a).
    intros (F, HF).
    unfold eqv_sym.
    simpl.
    apply isEqv_inv_eta.
  - rewrite H0.
    reflexivity.
Defined.

Lemma sigT_eqv {A B1 B2} :
  (forall x, eqv (B1 x) (B2 x)) -> eqv {x : A & B1 x} {x : A & B2 x}.
Proof.
  intro H.
  exists (sigT_eqv_fun H).
  apply (isEqv_intro (sigT_eqv_fun (fun x => eqv_sym (H x)))).
  - apply sigT_eqv_pinv.
  - apply sigT_eqv_pinv2.
Defined.

Lemma isProp_eqv {A B} : isProp A -> eqv A B -> isProp B.
Proof.
  intros HA HAB b1 b2.
  destruct HAB as (f, Hf).
  rewrite <- (isEqv_inv_eps _ Hf b1).
  rewrite <- (isEqv_inv_eps _ Hf b2).
  f_equal.
  apply HA.
Defined.

Definition fib {A B} (f : A -> B) (y : B) := {x : A & f x = y}.

Definition sigT_eqv_type {A P} (w w' : {x : A & P x}) :=
  let (x, p) := w in
  let (x', p') := w' in
  {e : x = x' & eq_rect _ P p x' e = p'}.

Definition sigT_fun {A P} (w w' : {x : A & P x}) :
  w = w' ->
  sigT_eqv_type w w'.
Proof.
  intros [].
  destruct w as (x, p).
  exists eq_refl.
  reflexivity.
Defined.

Definition sigT_fun_inv {A P} (w w' : {x : A & P x}) :
  sigT_eqv_type w w' -> w = w'.
Proof.
  destruct w as (x, p).
  destruct w' as (x', p').
  simpl.
  intros (e, gamma).
  destruct e.
  simpl in gamma.
  destruct gamma.
  reflexivity.
Defined.

Lemma sigT_eqv_eq {A P} (w w' : {x : A & P x}) :
  eqv (w = w') (sigT_eqv_type w w').
Proof.
  exists (sigT_fun w w').
  apply (isEqv_intro (sigT_fun_inv w w')).
  - destruct w as (x, p).
    destruct w' as (x', p').
    simpl.
    intros (e, gamma).
    destruct e.
    simpl in gamma.
    destruct gamma.
    reflexivity.
  - intro e.
    destruct e.
    destruct w as (w, p).
    reflexivity.
Defined.

Lemma fiber_path {A B} (f : A -> B) (y : B) x (p : f x = y) x' (p' : f x' = y) :
  eqv (@eq (fib f y) (existT _ x p) (existT _ x' p')) {gamma : x = x' & eq_trans (f_equal f gamma) p' = p}.
Proof.
  apply (eqv_trans (sigT_eqv_eq _ _)).
  simpl.
  apply sigT_eqv.
  intro e.
  destruct e.
  simpl.
  apply (@eqv_trans _ (p' = p)).
  - exists (@eq_sym _ p p').
    apply (isEqv_intro (@eq_sym _ p' p)).
    + intros [].
      reflexivity.
    + intros [].
      reflexivity.
  - destruct p'.
    apply eqv_refl.
Defined.

Lemma isContr_isProp {A : Type} : isContr A -> isProp A.
Proof.
  intros (x, H) a b.
  transitivity x.
  - symmetry.
    apply H.
  - apply H.
Defined.

Lemma isProp_to_isContr {A : Type} (a : A) : isProp A -> isContr A.
Proof.
  intro H.
  exists a.
  apply H.
Defined.

Lemma isProp_eq_is_contr A : isProp A -> forall x y : A, isContr (x = y).
Proof.
  intros f x y.
  exists (f x y).
  assert (forall z : A, forall p : z = y, p = eq_trans (eq_sym (f x z)) (f x y)).
  - intros z p.
    symmetry.
    apply eq_trans_sym_eq.
    destruct p.
    reflexivity.
  - assert (forall e1 e2 : x = y, e1 = e2).
    + specialize (H x).
      intros e1 e2.
      congruence.
    + apply H0.
Defined.

Lemma isProp_eq A : isProp A -> forall x y : A, isProp (x = y).
Proof.
  intros H x y.
  apply isContr_isProp.
  apply isProp_eq_is_contr.
  assumption.
Defined.

Lemma eqv_prod {A A' B B'} : eqv A B -> eqv A' B' -> eqv (A * A') (B * B').
Proof.
  intros (f, H) (f', H').
  exists (fun c : A * A' => let (a, a') := c in (f a, f' a')).
  apply (isEqv_intro (fun c : B * B' => let (b, b') := c in (isEqv_inv _ H b, isEqv_inv _ H' b'))).
  - intros (b, b').
    rewrite isEqv_inv_eps.
    rewrite isEqv_inv_eps.
    reflexivity.
  - intros (a, a').
    rewrite isEqv_inv_eta.
    rewrite isEqv_inv_eta.
    reflexivity.
Defined.

Lemma eqv_prod_sigma {A B} : eqv (A * B) {x : A & B}.
Proof.
  exists (fun c : A * B => let (a, b) := c in existT (fun _ => B) a b).
  apply (isEqv_intro (fun c : {x : A & B} => let (a, b) := c in (a, b))).
  - intros (a, b). reflexivity.
  - intros (a, b). reflexivity.
Defined.

Lemma isContr_unit {A} : isContr A -> eqv A unit.
Proof.
  intros (x, H).
  exists (fun _ => tt).
  apply (isEqv_intro (fun _ => x)).
  - intros [].
    reflexivity.
  - intro y.
    apply H.
Defined.

Lemma eqv_prod_unit {A} : eqv (A * unit) A.
Proof.
  exists (fun au : A * unit => let (a, _) := au in a).
  apply (isEqv_intro (fun a => (a, tt))).
  - intro.
    reflexivity.
  - intros (a, []).
    reflexivity.
Defined.

Lemma isEqv_homotopy {A B} (f g : A -> B) :
  isEqv f -> (forall x, f x = g x) -> isEqv g.
Proof.
  intros Hf Hfg.
  apply isEqv_qinv in Hf.
  destruct Hf as (h, (Hhf, Hfh)).
  apply (isEqv_intro h).
  - intro y.
    rewrite <- Hfg.
    apply Hhf.
  - intro x.
    rewrite <- Hfg.
    apply Hfh.
Defined.
