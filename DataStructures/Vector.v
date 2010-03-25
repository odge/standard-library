Require Import
 DataStructures.Nat.

Section Vector.

Inductive Vector (X : Type) : Nat -> Type :=
| Vnil : Vector X Z
| Vcons {n} : X -> Vector X n -> Vector X (S n).

End Vector.
