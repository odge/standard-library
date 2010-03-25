Require Import
 DataStructures.Logic.

(* I'd rather just call this Set but you can't always get what you want *)

Class Setoid := 
  { set : Type
  ; Rel : set -> set -> Prop
  ; equivalence : Equivalence Rel
  }.

Definition Morphism (S S' : Setoid) :=
  Exists (@set S -> @set S') (fun f =>
    forall x y,
      Rel x y -> Rel (f x) (f y)).

(*
*** Local Variables: ***
*** coq-prog-args: ("-emacs-U" "-nois") ***
*** End: ***
*)
