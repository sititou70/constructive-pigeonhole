Require Import Lia.
Require Import normal.

Theorem pigeonhole_principle_inversion :
  forall (n m : nat) (f : nat -> nat),
  (forall x, x < n -> f x < m) ->
  n < m ->
  exists i,
    i < m /\
    ~ (exists j, j < n /\ f j = i).
Proof.
  intros n m f Hmap Hn_lt_m.
  generalize dependent m.
  generalize dependent f.
  induction n; intros.

    +
    exists 0.
    split; try lia.
    intro Hcontra.
    inversion Hcontra.
    lia.

    +
    destruct m.

      -
      lia.

      -
      apply Arith_base.lt_S_n_stt in Hn_lt_m.

      set (
        g :=
          fun x =>
            if
              Nat.ltb (f x) (f n) then f x
            else if
              Nat.ltb (f n) (f x) then f x - 1
            else
              0
      ).
      assert (IHmap: forall x : nat, x < n -> g x < m).
      {
        intros.
        unfold g.
        assert (Hcases: f x < f n \/ f n < f x \/ f x = f n) by lia.
        destruct Hcases as [Hcases | [Hcases | Hcases]];
        simpl_ltb (f x) (f n).

          +
          specialize (Hmap n) as Hmap_for_n.
          lia.

          +
          specialize (Hmap x) as Hmap_for_x.
          lia.

          +
          lia.
      }

      specialize (IHn g m IHmap Hn_lt_m) as Hexists; clear IHn.

      inversion Hexists as [i Hnot_exists]; clear Hexists.
      inversion Hnot_exists as [Hi_lt_m Hnot_exists']; clear Hnot_exists.

      assert (Hi_cases: i < f n \/ i >= f n) by lia.
      destruct Hi_cases as [Hi_cases | Hi_cases].

        *
        exists i.
        split; try lia.

        intro Hcontra.
        inversion Hcontra as [j Hcontra']; clear Hcontra.
        apply Hnot_exists'; clear Hnot_exists'.
        
        assert (Hj_cases: j < n \/ j = n) by lia.
        destruct Hj_cases as [Hj_cases | Hj_cases].

          ++
          exists j.
          split; try lia.
          unfold g.
          simpl_ltb (f n) (f j).
          lia.

          ++
          subst.
          lia.
        
        *
        exists (S i).
        split; try lia.

        intro Hcontra.
        inversion Hcontra as [j Hcontra']; clear Hcontra.
        apply Hnot_exists'; clear Hnot_exists'.

        assert (Hj_cases: j < n \/ j = n) by lia.
        destruct Hj_cases as [Hj_cases | Hj_cases].

          ++
          exists j.
          split; try lia.
          unfold g.
          simpl_ltb (f n) (f j).
          lia.

          ++
          subst.
          lia.
Qed.
