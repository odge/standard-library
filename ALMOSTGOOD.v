Set Implicit Arguments.

Definition relation (T : Type) := T -> T -> Prop.

Class equivalence (T : Type) (R : relation T) :=
  { reflexivity : forall x, R x x
  ; symmetry : forall x y, R x y -> R y x
  ; transitivity : forall x y z, R x y -> R y z -> R x z
  }.

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
Instance Identity_equivalence T : equivalence (@Identity T).
split; [apply Identity_reflexivity|apply Identity_symmetry|apply Identity_transitivity].
Qed.

Class setoid :=
  { carrier : Type
  ; eq : relation carrier
  ; equiv : equivalence eq
  }.
Coercion carrier : setoid >-> Sortclass.
Infix "=" := eq (at level 20).

Inductive list (T : Type) : Type :=
| nil : list T
| cons : T -> list T -> list T.
Implicit Arguments nil [T].

Fixpoint morphismFunctionType (A : list setoid) (X : setoid) : Type :=
  match A with
    | nil => X
    | cons a A => a -> morphismFunctionType A X
  end.

Fixpoint morphismProperType (A : list setoid) (X : setoid) : forall (f : morphismFunctionType A X) (g : morphismFunctionType A X), Prop :=
  match A as A' return forall (f : morphismFunctionType A' X) (g : morphismFunctionType A' X), Prop with
    | nil => fun f g => eq f g
    | cons a A => fun f g => forall x y : a, eq x y -> morphismProperType A X (f x) (g y)
  end.

Definition morphism (A : list setoid) (X : setoid) (f : morphismFunctionType A X) := morphismProperType A X f f.

Class Category :=
  { Ob : setoid
  ; Hom : Ob -> Ob -> setoid
  ; identity {A} : Hom A A
  ; compose {A B C} : Hom A B -> Hom B C -> Hom A C
  ; composeProper {A B C} : morphism (cons (Hom A B) (cons (Hom B C) nil)) (Hom A C) compose
  ; leftIdentity {A} : forall f : Hom A A,
    compose f identity = f
  ; rightIdentity {A} : forall f : Hom A A,
    compose identity f = f
  ; associativity {A B C D} : forall (f : Hom A B) (g : Hom B C) (h : Hom C D),
    compose (compose f g) h = compose f (compose g h)
  }.

Instance category : setoid :=
  { carrier := Category
  ; eq := @Identity Category
  }.

Class Functor `(C : Category) `(D : Category) :=
  { F0 : @Ob C -> @Ob D
  ; F0Proper : morphism (cons (@Ob C) nil) (@Ob D) F0
  ; F1 {A B} : Hom A B -> Hom (F0 A) (F0 B)
  ; F1Proper {A B} : morphism (cons (Hom A B) nil) (Hom (F0 A) (F0 B)) F1
  }.

Instance IdentityFunctor `(C : Category) : Functor C C :=
  { F0 := fun A => A
  ; F1 A B := fun f => f
  }.
unfold morphism; unfold morphismProperType.
intros; assumption.
unfold morphism; unfold morphismProperType.
intros; assumption.
Qed.

Instance FunctorCompose
  `{C : Category} `{D : Category} `{E : Category}
  (F : Functor C D) (G : Functor D E) :
  Functor C E :=
  { F0 := fun A => F0 (F0 A)
  ; F1 A B := fun f => F1 (F1 f)
  }.
unfold morphism; unfold morphismProperType.
intros.
apply F0Proper.
apply F0Proper.
assumption.
unfold morphism; unfold morphismProperType.
intros.
apply F1Proper.
apply F1Proper.
assumption.
Qed.

Instance FunctorCategory : Category := {}.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-nois") ***
*** End: ***
*) 
