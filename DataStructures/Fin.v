Require Import DataStructures.Nat.

Inductive Fin : Nat -> Set :=
| Fz {n} : Fin (S n)
| Fs {n} : Fin n -> Fin (S n).

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-nois") ***
*** End: ***
*) 
