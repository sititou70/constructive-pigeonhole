Require Import Lia.

(* 参考：https://math.stackexchange.com/questions/910741/constructive-proof-of-pigeonhole-principle *)

Lemma n_collision_or_not :
  forall (n k : nat) (f : nat -> nat),
  (exists x, x < n /\ f x = k) \/
  ~ (exists x, x < n /\ f x = k).
Proof.
  intros.
  induction n.

    +
    right.
    intro Hcontra.
    inversion Hcontra.
    lia.

    +
    destruct IHn as [IHn | IHn].

      -
      left.
      inversion IHn.
      exists x.
      lia.

      -
      destruct (Peano_dec.eq_nat_dec (f n) k) as [Hfn_k | Hfn_k].

        *
        left.
        exists n.
        lia.

        *
        right.
        intro Hcontra.
        apply Hfn_k.
        inversion Hcontra as [x Hcontra'].
        destruct Hcontra' as [Hx_Sn Hfx_k].
        apply PeanoNat.Nat.le_lteq in Hx_Sn.
        destruct Hx_Sn as [Hsx_sn | Hsx_sn].

          ++
          destruct IHn.
          exists x.
          lia.

          ++
          inversion Hsx_sn.
          subst.
          reflexivity.
Qed.

Tactic Notation "simpl_ltb'" constr(v1) constr(v2) :=
  try assert (v1 < v2) by lia;
  try match goal with | [ H: v1 < v2 |- _ ] => apply PeanoNat.Nat.ltb_lt in H end;
  try match goal with | [ H: PeanoNat.Nat.ltb v1 v2 = true |- _ ] => rewrite H in * end;

  try assert (~ v1 < v2) by lia;
  try match goal with | [ H: ~ v1 < v2 |- _ ] => apply PeanoNat.Nat.ltb_nlt in H end;
  try match goal with | [ H: PeanoNat.Nat.ltb v1 v2 = false |- _ ] => rewrite H in * end.

Tactic Notation "simpl_ltb" constr(v1) constr(v2) :=
  simpl_ltb' v1 v2;
  simpl_ltb' v2 v1.

(* n羽の鳩をm個の巣に割り当てる *)
Theorem pigeonhole_principle :
  forall (n m : nat) (f : nat -> nat),
  (forall x, x < n -> f x < m) ->
  n > m ->
  exists i j,
    i < n /\
    j < n /\
    i <> j /\
    f i = f j.
Proof.
  intros n m f Hmap Hn_gt_m.
  generalize dependent m.
  generalize dependent f.
  induction n; intros.

    +
    lia.

    +
    assert (
      Hn_collision_or_not:
        (exists x, x < n /\ f x = f n) \/
        ~ (exists x, x < n /\ f x = f n)
    ).
      apply n_collision_or_not.

    destruct Hn_collision_or_not as [Hn_collision_or_not | Hn_collision_or_not].

      -
      inversion Hn_collision_or_not as [x Hfx_eq_fn].
      exists x, n.
      lia.

      -
      destruct m.

        *
        specialize (Hmap n) as Hmap_for_n.
        lia.

        *
        apply Arith_base.gt_S_n_stt in Hn_gt_m.

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
          intros x Hx_lt_n.
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
            destruct Hn_collision_or_not.
            exists x.
            lia.
        }

        specialize (IHn g m IHmap Hn_gt_m) as Hexists; clear IHn.
        inversion Hexists as [i Hexists']; clear Hexists.
        inversion Hexists' as [j Hexists'']; clear Hexists'.
        exists i, j.
        repeat split; try lia.

        assert (Hcollision: g i = g j -> f i = f j).
        {
          intros Hgi_eq_gj.
          unfold g in Hgi_eq_gj.
          assert (Hi_cases: f i < f n \/ f n < f i \/ f i = f n) by lia.
          assert (Hj_cases: f j < f n \/ f n < f j \/ f j = f n) by lia.

          destruct Hi_cases as [Hi_cases | [Hi_cases | Hi_cases]]; destruct Hj_cases as [Hj_cases | [Hj_cases | Hj_cases]];
          simpl_ltb (f i) (f n);
          simpl_ltb (f j) (f n);

          try solve [
            lia
          ];
          try solve [
            destruct Hn_collision_or_not;
            exists i;
            lia
          ];
          try solve [
            destruct Hn_collision_or_not;
            exists j;
            lia
          ].
        }

        lia.
Qed.
