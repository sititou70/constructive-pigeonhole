Require Import Lia.
Require Import normal.
Require Import inversion.

Theorem contraposition :
  forall p q: Prop,
  (p -> q) -> (~q -> ~p).
Proof.
  intros p q Hp_imp_q Hnot_q.
  intro Hcontra.
  destruct Hnot_q.
  apply Hp_imp_q.
  assumption.
Qed.

Theorem bijection__n_eq_m :
  forall (n m : nat) (f : nat -> nat),
  (forall x, x < n -> f x < m) ->
  ~ (
    exists i j,
      i < n /\
      j < n /\
      i <> j /\
      f i = f j
  ) ->
  ~ (
    exists i,
      i < m /\
      ~ (exists j, j < n /\ f j = i)
  ) ->
  n = m.
Proof.
  intros n m f Hmap Hinjection Hsurjection.
  specialize (contraposition _ _ (pigeonhole_principle n m f Hmap)) as pigeonhole_principle_contra.
  specialize (contraposition _ _ (pigeonhole_principle_inversion n m f Hmap)) as pigeonhole_principle_inversion_contra.

  specialize (pigeonhole_principle_contra Hinjection) as Hn_not_gt_m.
  specialize (pigeonhole_principle_inversion_contra Hsurjection) as Hn_not_lt_m.
  lia.
Qed.
