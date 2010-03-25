Require Import
 DataStructures.Nat
 DataStructures.Fin.

Section OperatorDomain.

Variable (Symbol : Set) (arity : Symbol -> Nat).

Inductive Term (X : Set) : Set :=
| variable : X -> Term X
| operator : forall (S : Symbol), (Fin (arity S) -> Term X) -> Term X.

End OperatorDomain.
Implicit Arguments variable [Symbol arity X].


Section TermSubstitution.

Variable (Symbol : Set) (arity : Symbol -> Nat).
Variable X Y : Set.

Definition Substitution X Y := X -> Term Symbol arity Y.

Fixpoint substitute (f : Substitution X Y) (t : Term Symbol arity X) : Term Symbol arity Y :=
  match t with
    | variable x => f x
    | operator s xs => operator _ _ _ s (fun i => substitute f (xs i))
  end.

End TermSubstitution.
Implicit Arguments substitute [Symbol arity X Y].
