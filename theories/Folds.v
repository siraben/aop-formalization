From Stdlib Require Import List.
Import ListNotations.

(** The initial algebra of cons-lists (sections 2.6 and 3.1).
    Equality of arrows is stated pointwise throughout. *)
Section Lists.
  Context {A B : Type} (z : B) (s : A -> B -> B).

  Theorem fold_unique (h : list A -> B) :
    h [] = z -> (forall x xs, h (x :: xs) = s x (h xs)) ->
    forall xs, h xs = fold_right s z xs.
  Proof. intros Hnil Hcons xs; induction xs; simpl; congruence. Qed.

  Corollary fold_fusion {C} (h : B -> C) (t : A -> C -> C) :
    (forall x b, h (s x b) = t x (h b)) ->
    forall xs, h (fold_right s z xs) = fold_right t (h z) xs.
  Proof. intros H xs; induction xs; simpl; congruence. Qed.

  Theorem banana_split {C} (w : C) (t : A -> C -> C) xs :
    (fold_right s z xs, fold_right t w xs) =
    fold_right (fun x p => (s x (fst p), t x (snd p))) (z, w) xs.
  Proof. induction xs; simpl; [reflexivity | now rewrite <- IHxs]. Qed.
End Lists.
