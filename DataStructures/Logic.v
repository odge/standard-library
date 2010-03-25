Inductive Identity (T : Type) : T -> T -> Prop :=
| refl : forall t : T, Identity T t t.
Inductive False : Prop :=. 
Inductive True : Prop := I.
Inductive And (P Q : Prop) : Prop :=
| both : P -> Q -> And P Q.
Inductive Or (P Q : Prop) : Prop :=
| left : P -> Or P Q
| right : Q -> Or P Q.
Inductive Exists (T : Type) (P : T -> Prop) : Prop :=
| witness : forall t : T, P t -> Exists T P.

Class Equivalence {T : Type} (Rel : T -> T -> Prop) :=
  { reflexivity : forall t, Rel t t
  ; symmetry : forall u v, Rel u v -> Rel v u
  ; transitivity : forall u v w, Rel u v -> Rel v w -> Rel u w
  }.

Instance IdentityEquivalence {T} : Equivalence (Identity T).
split.
apply refl.
intros u v prf; destruct prf; apply refl.
intros u v w prf1 prf2; destruct prf1; destruct prf2; apply refl.
Qed.

