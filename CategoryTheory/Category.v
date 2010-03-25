Require Import
 DataStructures.Logic
 DataStructures.Nat
 DataStructures.Fin
 DataStructures.OperatorDomain
 DataStructures.Set.

Class Category (Object : Type) (Arrow : Object -> Object -> Type) {eq : forall A B, Arrow A B -> Arrow A B -> Prop} (E : forall A B, Equivalence (eq A B)) :=
  { identity {A} : Arrow A A
  ; compose {A B C} : Arrow A B -> Arrow B C -> Arrow A C
  ; leftIdentity {A B} : forall f : Arrow A B, eq _ _ (compose f identity) f
  ; rightIdentity {A B} : forall f : Arrow A B, eq _ _ (compose identity f) f
  ; associativity {A B C D} : forall (f : Arrow A B) (g : Arrow B C) (h : Arrow C D),
    eq _ _ (compose f (compose g h)) (compose (compose f g) h)
  }.

Record SmallCategory : Type := { object : Set ; arrow : object -> object -> Set ; eq : _ ; equiv : forall A B, Equivalence (eq A B) ; cat : Category object arrow equiv }.

Class Functor {Object Arrow Object' Arrow' eq eq'} `(C : Category Object Arrow eq) `(D : Category Object' Arrow' eq') :=
  { F_0 : Object -> Object'
  ; F_1 {A B} : Arrow A B -> Arrow' (F_0 A) (F_0 B)
  ; F_id {A} : eq' _ _ (F_1 identity) (@identity _ _ _ _ _ (F_0 A))
  ; F_compose {A B C} : forall (f : Arrow A B) (g : Arrow B C),
    eq' _ _ (F_1 (compose f g)) (compose (F_1 f) (F_1 g))
  }.

Instance IdentityFunctor `(C : Category) : Functor C C :=
  { F_0 := fun O => O
  ; F_1 A B := fun arr => arr
  }.
intros; apply reflexivity.
intros; apply reflexivity.
Qed.

Instance ComposeFunctor `{C : Category} `{D : Category} `{E : Category}
  (F : Functor C D) (G : Functor D E) : Functor C E :=
  { F_0 := fun O => F_0 (F_0 O)
  ; F_1 A B := fun arr => F_1 (F_1 arr)
  }.
intros.
eapply transitivity with (v := F_1 identity).
Focus 2.
apply F_id.
pose (@F_id Object Arrow Object0 Arrow0 eq0 eq1 E).


Instance TYPE : Category Type (fun X Y => X -> Y) :=
  { identity A := fun a : A => a
  ; compose A B C := fun f g =>  fun x => g (f x)
  }.

Instance FIN : Category Nat (fun n m => Fin n -> Fin m) :=
  { identity n := fun i => i
  ; compose n m r := fun f g => fun x => g (f x)
  }.

Instance SMALL : Category SmallCategory (fun C D => Functor (cat C) (cat D)) :=
  { identity A := IdentityFunctor (cat A)
  ; compose A B C := fun F G => ComposeFunctor F G
  }.

Section OperatorDomain.
Variable (Symbol : Set) (arity : Symbol -> Nat).
Instance TERM : Category Set (Substitution Symbol arity) :=
  { identity A := fun i => variable i
  ; compose A B C := fun f g => fun x => substitute g (f x)
  }.
End OperatorDomain.

Instance SET : Category Setoid Morphism.
split; unfold Morphism.

refine (fun A => @witness _ _ (fun i => i) _).
intros x y Rxy; exact Rxy.

refine (fun A B C f g =>
  match f with witness f' fPrf => 
  match g with witness g' gPrf => 
    @witness _ _ (fun x => g' (f' x)) _
  end
  end
).
intros x y prf; apply gPrf; apply fPrf; exact prf.
Defined.

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-nois") ***
*** End: ***
*) 
