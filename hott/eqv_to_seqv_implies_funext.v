(* From "A Coq proof that Univalence Axioms implies Functional
Extensionality" by Andrej Bauer and Peter LeFanu Lumsdaine *)

(* Since eta conversion for functions is now judgmental in Coq, a big
   part of the original proof is not needed anymore. *)

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

Ltac path_via x := apply @concat with (y := x); auto.

Lemma map {A B} {x y : A} (f : A -> B) (p : x == y) : f x == f y.
Proof.
  path_induction.
Qed.

Definition contractible A := {x : A & forall y : A, y == x}.

Definition hfiber {A B} (f : A -> B) (y : B) := {x : A & f x == y}.

Definition is_wequiv {A B} (f : A -> B) := forall y : B, contractible (hfiber f y).

Inductive is_sequiv {A : Type} : forall {B}, (A -> B) -> Type :=
| is_sequiv_id : is_sequiv (fun x : A => x).

Definition sequiv A B := {s : A -> B & is_sequiv s}.

Definition sequiv_coerce_to_function A B (s : sequiv A B) : A -> B := projT1 s.

Coercion sequiv_coerce_to_function : sequiv >-> Funclass.

Lemma seq_injective U V : forall (s : sequiv U V) x y, s x == s y -> x == y.
Proof.
  intros (s, H) x y p.
  destruct H.
  exact p.
Qed.

Theorem seq_exponential : forall {A B} (s : sequiv A B) C, sequiv (C -> A) (C -> B).
Proof.
  intros A B (s, H) C.
  exists (fun h x => s (h x)).
  destruct H.
  apply is_sequiv_id.
Defined.

Definition path_pred A := fun xy : A * A => fst xy == snd xy.

Definition path_space A := sigT (path_pred A).

Axiom is_weq_to_seq : forall A B (f : A -> B), is_wequiv f -> is_sequiv f.

Definition src A : sequiv (path_space A) A.
Proof.
  exists (fun p => fst (projT1 p)).
  apply is_weq_to_seq.
  intros x.
  eexists (existT _ (existT (fun (xy : A * A) => fst xy == snd xy) (x, x) (idpath x)) _).
  intros [[[u v] p] q].
  unfold path_pred in p.
  simpl in * |- *.
  destruct q, p.
  apply idpath.
Defined.

Definition trg A : sequiv (path_space A) A.
Proof.
  exists (fun p => snd (projT1 p)).
  apply is_weq_to_seq.
  intros x.
  eexists (existT _ (existT (fun (xy : A * A) => fst xy == snd xy) (x, x) (idpath x)) _).
  intros [[[u v] p] q].
  unfold path_pred in p.
  simpl in * |- *.
  destruct q, p.
  apply idpath.
Defined.

Theorem extensionality {A B : Type} (f g : A -> B) : (forall x, f x == g x) -> f == g.
Proof.
  intro p.
  pose (d := fun x : A => existT (path_pred B) (f x, f x) (idpath (f x))).
  pose (e := fun x : A => existT (path_pred B) (f x, g x) (p x)).
  pose (src_compose := seq_exponential (src B) A).
  pose (trg_compose := seq_exponential (trg B) A).
  path_via (projT1 trg_compose e).
  path_via (projT1 trg_compose d).
  apply map.
  apply seq_injective with (s := src_compose).
  apply idpath.
Qed.
