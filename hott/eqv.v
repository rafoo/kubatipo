Set Universe Polymorphism.

Definition comp {A B C : Type} (f : A -> B) (g : B -> C) := fun x => g (f x).
Definition id (A : Type) := fun x : A => x.

(* One possible definition of the isEqv proposition *)
Definition pinv {A B} (f : A -> B) (g : B -> A) :=
  forall x : B, f (g x) = x.

Definition isEqv {A B} f :=
  { g : B -> A &
  { eta : pinv g f &
  { eps : pinv f g &
          forall x, f_equal f (eta x) = eps (f x)}}}.

Definition eqv A B := sigT (@isEqv A B).

Definition eqv_fun {A B} (e : eqv A B) : A -> B :=
  let (f, _) := e in f.

Coercion eqv_fun : eqv >-> Funclass.

Lemma isEqv_id A : isEqv (id A).
Proof.
  exists (id A).
  exists (fun x => eq_refl).
  exists (fun x => eq_refl).
  reflexivity.
Defined.

Definition eqv_refl A : eqv A A := existT _ (id A) (isEqv_id A).

Lemma id_to_eqv {A B} : A = B -> eqv A B.
Proof.
  intros [].
  apply eqv_refl.
Defined.

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

Lemma natural_transf {A B} {f g : A -> B} (H : forall x, f x = g x) x y (p : x = y) :
  eq_trans (H x) (f_equal g p) = eq_trans (f_equal f p) (H y).
Proof.
  destruct p.
  simpl.
  destruct (H x).
  reflexivity.
Defined.

Lemma f_equal_comp {A B C} (f : A -> B) (g : B -> C) x y (p : x = y) :
  f_equal g (f_equal f p) = f_equal (comp f g) p.
Proof.
  destruct p.
  reflexivity.
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

Lemma f_equal_id {A} {x y : A} (p : x = y) : f_equal (id A) p = p.
Proof.
  destruct p.
  reflexivity.
Defined.

Definition qinv {A B} (f : A -> B) := {g : B -> A & (pinv f g * pinv g f)%type}.

Lemma eqv_intro {A B} {f : A -> B} g : pinv f g -> pinv g f -> isEqv f.
Proof.
  intros eps eta.
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

Lemma qinv_to_isEqv {A B} {f : A -> B} : qinv f -> isEqv f.
Proof.
  intros (g, (Hfg, Hgf)).
  apply (eqv_intro g); assumption.
Defined.

Definition isEqv_inv {A B} {f : A -> B} (H : isEqv f) : B -> A.
Proof.
  destruct H as (g, _).
  exact g.
Defined.

Definition pinv_isEqv {A B} {f : A -> B} (H : isEqv f) : pinv f (isEqv_inv H).
Proof.
  unfold isEqv_inv.
  destruct H as (g, (eta, (eps, tau))).
  assumption.
Defined.

Definition pinv_isEqv2 {A B} {f : A -> B} (H : isEqv f) : pinv (isEqv_inv H) f.
Proof.
  unfold isEqv_inv.
  destruct H as (g, (eta, (eps, tau))).
  assumption.
Defined.

Lemma inv_isEqv {A B} {f : A -> B} (H : isEqv f) : isEqv (isEqv_inv H).
Proof.
  apply (eqv_intro f).
  - apply pinv_isEqv2.
  - apply pinv_isEqv.
Defined.

Lemma eqv_sym {A B} : eqv A B -> eqv B A.
Proof.
  intros (f, H).
  exists (isEqv_inv H).
  apply inv_isEqv.
Defined.

Lemma eqv_trans {A B C} : eqv A B -> eqv B C -> eqv A C.
Proof.
  intros (f, Hf) (g, Hg).
  exists (comp f g).
  apply (eqv_intro (comp (isEqv_inv Hg) (isEqv_inv Hf))).
  - intro c.
    unfold comp.
    rewrite pinv_isEqv.
    apply pinv_isEqv.
  - intro a.
    unfold comp.
    rewrite pinv_isEqv2.
    apply pinv_isEqv2.
Defined.

Definition isProp A := forall a b : A, a = b.

Lemma isProp_prod {A B} : isProp A -> isProp B -> isProp (A * B).
Proof.
  intros HA HB (a1, b1) (a2, b2).
  specialize (HA a1 a2).
  destruct HA.
  specialize (HB b1 b2).
  destruct HB.
  reflexivity.
Defined.

Lemma funapp {A B} (f g : forall x : A, B x) : f = g -> forall x, f x = g x.
Proof.
  intros [].
  reflexivity.
Defined.

Definition FUNEXT := forall A B (f g : forall x : A, B x), isEqv (funapp f g).

Lemma Dep_Funext (funext : FUNEXT) {A B} (f g : forall x : A, B x) :
  (forall x, f x = g x) -> f = g.
Proof.
  apply eqv_fun.
  apply eqv_sym.
  exists (funapp f g).
  apply funext.
Defined.

Lemma Dep_Funext_funapp (funext : FUNEXT) {A B} (f g : forall x : A, B x) e :
  Dep_Funext funext f g (fun x => funapp f g e x) = e.
Proof.
  apply pinv_isEqv2.
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
    apply pinv_isEqv.
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
    apply pinv_isEqv2.
  - rewrite H0.
    reflexivity.
Defined.

Lemma sigT_eqv {A B1 B2} :
  (forall x, eqv (B1 x) (B2 x)) -> eqv {x : A & B1 x} {x : A & B2 x}.
Proof.
  intro H.
  exists (sigT_eqv_fun H).
  apply (eqv_intro (sigT_eqv_fun (fun x => eqv_sym (H x)))).
  - apply sigT_eqv_pinv.
  - apply sigT_eqv_pinv2.
Defined.

Lemma isProp_eqv {A B} : isProp A -> eqv A B -> isProp B.
Proof.
  intros HA HAB b1 b2.
  destruct HAB as (f, Hf).
  rewrite <- (pinv_isEqv Hf b1).
  rewrite <- (pinv_isEqv Hf b2).
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
  apply (eqv_intro (sigT_fun_inv w w')).
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
    apply (eqv_intro (@eq_sym _ p' p)).
    + intros [].
      reflexivity.
    + intros [].
      reflexivity.
  - destruct p'.
    apply eqv_refl.
Defined.

Lemma fiber_contractible {A B} (f : eqv A B) (y : B) : {w : fib f y & forall w', w' = w}.
Proof.
  destruct f as (f, (g, (eta, (eps, tau)))).
  simpl.
  exists (existT _ (g y) (eps y)).
  intros (x, p).
  apply (eqv_sym (fiber_path f y x p _ _)).
  exists (eq_trans (eq_sym (eta x)) (f_equal g p)).
  rewrite f_equal_trans.
  rewrite f_equal_sym.
  rewrite tau.
  rewrite f_equal_comp.
  rewrite eq_trans_assoc.
  apply eq_trans_sym_eq.
  apply (eq_trans (eq_sym (natural_transf eps (f x) y p))).
  f_equal.
  apply f_equal_id.
Defined.


Definition isContr (A : Type) := {x : A & forall y : A, x = y}.

Lemma isContr_isProp {A : Type} : isContr A -> isProp A.
Proof.
  intros (x, H) a b.
  transitivity x.
  - symmetry.
    apply H.
  - apply H.
Defined.

Lemma isProp_isContr {A : Type} (a : A) : isProp A -> isContr A.
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
  apply (eqv_intro (fun c : B * B' => let (b, b') := c in (isEqv_inv H b, isEqv_inv H' b'))).
  - intros (b, b').
    rewrite pinv_isEqv.
    rewrite pinv_isEqv.
    reflexivity.
  - intros (a, a').
    rewrite pinv_isEqv2.
    rewrite pinv_isEqv2.
    reflexivity.
Defined.

Lemma eqv_prod_sigma {A B} : eqv (A * B) {x : A & B}.
Proof.
  exists (fun c : A * B => let (a, b) := c in existT (fun _ => B) a b).
  apply (eqv_intro (fun c : {x : A & B} => let (a, b) := c in (a, b))).
  - intros (a, b). reflexivity.
  - intros (a, b). reflexivity.
Defined.

Lemma isContr_unit {A} : isContr A -> eqv A unit.
Proof.
  intros (x, H).
  exists (fun _ => tt).
  apply (eqv_intro (fun _ => x)).
  - intros [].
    reflexivity.
  - intro y.
    apply H.
Defined.

Lemma eqv_prod_unit {A} : eqv (A * unit) A.
Proof.
  exists (fun au : A * unit => let (a, _) := au in a).
  apply (eqv_intro (fun a => (a, tt))).
  - intro.
    reflexivity.
  - intros (a, []).
    reflexivity.
Defined.
