(* From "A Coq proof that Univalence Axioms implies Functional
Extensionality" by Andrej Bauer and Peter LeFanu Lumsdaine *)

(* Since eta conversion for functions is now judgmental in Coq, a big
   part of the original proof is not needed anymore. *)

Definition idmap A := fun x : A => x.

Definition compose {A B C} (g : B -> C) (f : A -> B) (x : A) := g (f x).

Inductive paths {A} : A -> A -> Type := idpath : forall x, paths x x.

Notation "x == y" := (paths x y) (at level 70).

Hint Resolve @idpath.

Ltac path_induction :=
  intros; repeat progress (
    match goal with
    | [p : _ == _ |- _] => induction p
    | _ => idtac
    end); auto.

Definition concat {A} {x y z : A} : x == y -> y == z -> x == z.
Proof.
  path_induction.
Qed.

Notation "p @ q" := (concat p q) (at level 60).

Definition opposite {A} {x y : A} : x == y -> y == x.
Proof.
  path_induction.
Qed.

Notation "! p" := (opposite p) (at level 50).

Lemma map {A B} {x y : A} (f : A -> B) (p : x == y) : f x == f y.
Proof.
  path_induction.
Qed.

Ltac path_via x := apply @concat with (y := x); auto.

Theorem transport {A} {P : A -> Type} {x y : A} (p : x == y) : P x -> P y.
Proof.
  path_induction.
Defined.

Lemma total_paths (A : Type) (P : A -> Type) (x y : sigT P)
      (p : projT1 x == projT1 y) : transport p (projT2 x) == projT2 y -> x == y.
Proof.
  intros q.
  destruct x as [x H].
  destruct y as [y G].
  simpl in * |- *.
  induction p.
  simpl in q.
  path_induction.
Qed.

Definition base_path {A} {P : A -> Type} {u v : sigT P} :
  u == v -> projT1 u == projT1 v.
Proof.
  path_induction.
Qed.

Definition contractible A := {x : A & forall y : A, y == x}.

Definition hfiber {A B} (f : A -> B) (y : B) := {x : A & f x == y}.

Definition is_wequiv {A B} (f : A -> B) := forall y : B, contractible (hfiber f y).

Definition wequiv A B := {w : A -> B & is_wequiv w}.

Definition wequiv_coerce_to_function : forall A B, wequiv A B -> A -> B.
Proof.
  intros A B w.
  exact (projT1 w).
Defined.

Coercion wequiv_coerce_to_function : wequiv >-> Funclass.

Lemma is_wequiv_idmap A : is_wequiv (idmap A).
Proof.
  intros x.
  exists (existT (fun z => z == x) x (idpath x)).
  intros [z q].
  apply total_paths with (p := q).
  simpl.
  compute in q.
  path_induction.
Qed.

Definition idweq A : wequiv A A.
Proof.
  exists (idmap A).
  apply is_wequiv_idmap.
Defined.

Definition path_to_weq {U V} : U == V -> wequiv U V.
Proof.
  intro p.
  induction p as [S].
  exact (idweq S).
Defined.

Definition weq_inv {U V} : wequiv U V -> V -> U.
Proof.
  intros [w H] y.
  destruct (H y) as [[x p] _].
  exact x.
Defined.

Lemma weq_inv_is_section U V (w : wequiv U V) : forall y, w (weq_inv w y) == y.
Proof.
  intro y.
  destruct w as [w G].
  simpl.
  destruct (G y) as [[x p] c].
  exact p.
Qed.

Lemma weq_inv_is_retraction U V (w : wequiv U V) : forall x, weq_inv w (w x) == x.
Proof.
  intro x.
  destruct w as [w H].
  simpl.
  destruct (H (w x)) as [[y p] c].
  apply opposite.
  exact (base_path (c (existT _ x (idpath (w x))))).
Qed.

Lemma weq_injective U V : forall (w : wequiv U V) x y, w x == w y -> x == y.
Proof.
  intros w x y.
  simpl.
  intro p.
  assert (q := map (weq_inv w) p).
  path_via (weq_inv w (w x)).
  - apply opposite; apply weq_inv_is_retraction.
  - path_via (weq_inv w (w y)).
    apply weq_inv_is_retraction.
Qed.

Axiom univalence : forall U V, is_wequiv (@path_to_weq U V).

Definition weq_to_path {U V} : wequiv U V -> U == V.
Proof.
  apply weq_inv.
  exists path_to_weq.
  apply univalence.
Defined.

Lemma weq_to_path_section U V : forall w : wequiv U V, path_to_weq (weq_to_path w) == w.
Proof.
  intro w.
  exact (weq_inv_is_section _ _ (existT _ (@path_to_weq U V) (univalence U V)) w).
Qed.

Definition pred_weq_to_path U V : (wequiv U V -> Type) -> (U == V -> Type).
Proof.
  intros Q p.
  apply Q.
  apply path_to_weq.
  exact p.
Defined.

Theorem weq_induction (P : forall U V, wequiv U V -> Type) :
  (forall T, P T T (idweq T)) -> (forall U V w, P U V w).
Proof.
  intro r.
  pose (P' := (fun U V => pred_weq_to_path U V (P U V))).
  assert (r' : forall T, P' T T (idpath T)).
  - intro T.
    exact (r T).
  - intros U V w.
    apply (transport (weq_to_path_section _ _ w)).
    exact (paths_rect _ P' r' U V (weq_to_path w)).
Qed.

Theorem weq_exponential : forall {A B} (w : wequiv A B) C, wequiv (C -> A) (C -> B).
Proof.
  intros A B w C.
  exists (fun h => compose w h).
  generalize A B w.
  apply weq_induction.
  intro D.
  exact (projT2 (idweq (C -> D))).
Defined.

Definition path_pred A := fun xy : A * A => fst xy == snd xy.

Definition path_space A := sigT (path_pred A).

Definition src A : wequiv (path_space A) A.
Proof.
  exists (fun p => fst (projT1 p)).
  intros x.
  eexists (existT _ (existT (fun (xy : A * A) => fst xy == snd xy) (x, x) (idpath x)) _).
  intros [[[u v] p] q].
  unfold path_pred in p.
  simpl in * |- *.
  induction q as [a].
  induction p as [b].
  apply idpath.
Defined.

Definition trg A : wequiv (path_space A) A.
Proof.
  exists (fun p => snd (projT1 p)).
  intros x.
  eexists (existT _ (existT (fun (xy : A * A) => fst xy == snd xy) (x, x) (idpath x)) _).
  intros [[[u v] p] q].
  unfold path_pred in p.
  simpl in * |- *.
  induction q as [a].
  induction p as [b].
  apply idpath.
Defined.

Theorem extensionality {A B : Type} (f g : A -> B) : (forall x, f x == g x) -> f == g.
Proof.
  intro p.
  pose (d := fun x : A => existT (path_pred B) (f x, f x) (idpath (f x))).
  pose (e := fun x : A => existT (path_pred B) (f x, g x) (p x)).
  pose (src_compose := weq_exponential (src B) A).
  pose (trg_compose := weq_exponential (trg B) A).
  path_via (projT1 trg_compose e).
  path_via (projT1 trg_compose d).
  apply map.
  apply weq_injective with (w := src_compose).
  apply idpath.
Qed.
