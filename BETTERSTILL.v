Set Implicit Arguments.

Inductive Identity (T : Type) : T -> T -> Prop := I : forall t, Identity t t.
Section Theory.
  Variable T : Type.
  Theorem Identity_reflexivity {x : T} : Identity x x.
    constructor.
  Qed.
  Theorem Identity_symmetry {x y : T} : Identity x y -> Identity y x.
    intros x y H; elim H.
    constructor.
  Qed.
  Theorem Identity_transitivity {x y z : T} : Identity x y -> Identity y z -> Identity x z.
    intros x y z H H'.
    destruct H; destruct H'.
    constructor.
  Qed.
End Theory.

Section Sigma.
  Variable K : Type.
  Variable P : K -> Type.
  Inductive Sigma : Type := witness : forall k : K, P k -> Sigma.
  Definition pi1 (s : Sigma) : K := match s with witness k _ => k end.
  Definition pi2 (s : Sigma) : P (pi1 s) := match s with witness _ prf => prf end.
End Sigma.

Inductive list (T : Type) : Type :=
| nil : list T
| cons : T -> list T -> list T.
Notation "[]" := (@nil _).
Infix "::" := cons (right associativity, at level 20).

Definition relation (T : Type) := T -> T -> Prop.
Class equivalence (T : Type) (R : relation T) : Prop :=
  { reflexivity : forall x, R x x
  ; symmetry : forall x y, R x y -> R y x
  ; transitivity : forall x y z, R x y -> R y z -> R x z
  }.
Instance Identity_equivalence (T : Type) : equivalence (@Identity T).
split; [ apply Identity_reflexivity | apply Identity_symmetry | apply Identity_transitivity ].
Qed.
Instance Proof_Irrelevant_equivalence (P : Prop) : equivalence (fun (p q : P) => Identity P P).
split; intros; constructor.
Qed.

Class setoid (carrier : Type) : Type := { eq : relation carrier ; equiv : equivalence eq  }.
Instance identity_setoid (T : Type) : setoid T := { equiv := Identity_equivalence T }.
Instance proof_setoid (P : Prop) : setoid P := { equiv := Proof_Irrelevant_equivalence P }.
Infix "=" := eq (no associativity, at level 30).

Section Morphisms.
  Definition morphismArguments := list (Sigma setoid).
  
  Fixpoint morphismFunctionType (A : morphismArguments) (T : Sigma setoid) : Type :=
    match A with
      | nil => pi1 T
      | cons a A => pi1 a -> morphismFunctionType A T
    end.
  Fixpoint morphismProper' (A : morphismArguments) (T : Sigma setoid) : relation (morphismFunctionType A T) :=
    match A as A' return relation (morphismFunctionType A' T) with
      | nil => fun f g => f = g
      | cons (witness k pk) A => fun f g => forall x y : k, x = y -> morphismProper' A T (f x) (g y)
    end.
  Definition morphismProper (A : morphismArguments) (T : Sigma setoid) (f : morphismFunctionType A T) := morphismProper' A T f f.
End Morphisms.

Class category
  (Ob : Type) (ObSetoid : setoid Ob)
  (Hom : Ob -> Ob -> Type) (HomSetoid : forall A B : Ob, setoid (Hom A B))
  : Type :=
  { identity {A} : Hom A A
  ; compose {A B C} : Hom A B -> Hom B C -> Hom A C
  ; composeProper {A B C} : morphismProper (witness _ _ (HomSetoid A B) :: witness _ _ (HomSetoid B C) :: []) (witness _ _ (HomSetoid A C)) (@compose A B C)
  ; leftIdentity {A} : forall f : Hom A A, compose identity f = f
  ; rightIdentity {A} : forall f : Hom A A, compose f identity = f
  ; associativity {A B C D} : forall (f : Hom A B) (g : Hom B C) (h : Hom C D),
    compose f (compose g h) = compose (compose f g) h
  }.

Record small_cat : Type :=
  { small_Ob : Type ; small_ObSetoid : setoid small_Ob
  ; small_Hom : small_Ob -> small_Ob -> Type ; small_HomSetoid : forall A B : small_Ob, setoid (small_Hom A B)
  ; small_category : category small_ObSetoid small_Hom small_HomSetoid
  }.

Class Functor `(C : category) `(D : category) : Type :=
  { F0 : Ob -> Ob0
  ; F1 {A B} : forall f : Hom A B, Hom0 (F0 A) (F0 B)
  }.
Instance IdentityFunctor `(C : category) : Functor C C :=
  { F0 := fun A => A
  ; F1 A B := fun f => f
  }.
Instance ComposeFunctor `(C : category) `(D : category) `(E : category)
  (F : Functor C D) (G : Functor D E) : Functor C E :=
  { F0 := fun A => F0 (F0 A)
  ; F1 A B := fun f => F1 (F1 f)
  }.

Definition small_functor (C D : small_cat) : Type := Functor (@small_category C) (@small_category D).

Axiom F : forall P, P.
Ltac admit := apply F.

Instance category_of_small_cats : category (identity_setoid small_cat) small_functor _ :=
  { identity C := IdentityFunctor (small_category C)
  ; compose A B C := ComposeFunctor (small_category A) (small_category B) (small_category C)
  }.
unfold morphismProper; unfold morphismProper'; simpl; intros.
destruct H.
destruct H0.
constructor.

unfold morphismProper; unfold morphismProper'; simpl; intros.
destruct f.
unfold IdentityFunctor.
unfold ComposeFunctor.
simpl.
admit.

unfold morphismProper; unfold morphismProper'; simpl; intros.
destruct f.
unfold IdentityFunctor; unfold ComposeFunctor.
admit.

unfold morphismProper; unfold morphismProper'; simpl; intros.
unfold ComposeFunctor.
constructor.

Qed.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-nois") ***
*** End: ***
*) 
