/- ARISTOTLE Q3 — EXPECTED FALSE: we request a COUNTEREXAMPLE, not a proof.
Sharpness probe for SatReadout.no_eps_midpoint: that theorem needs the
quadratic bound 2aε < (satDist a p q / 2 − ε)². The claim below DROPS it,
keeping only ε ≤ D/2. If our bound is doing real work, this weakened claim
is refutable — e.g. X = ℝ with p, q far apart relative to a (saturation
makes f(d(p,m)) and f(d(m,q)) both ≈ a ≈ f(d(p,q)), so for moderate ε the
true midpoint IS an ε-midpoint in the saturated metric).
A concrete counterexample (X, a, ε, p, q, m) certifies the quadratic bound
is not an artifact of our proof. -/
import SatReadout

open SatReadout

/-
ORIGINAL (FALSE) CLAIM — left here, commented out, because it is refutable.
A direct disproof of the general statement is given below as
`no_eps_midpoint_without_quadratic_bound_is_false`, together with the explicit
witnessing instance `eps_midpoint_counterexample`.

theorem no_eps_midpoint_without_quadratic_bound
    {X : Type*} [MetricSpace X] {a ε : ℝ} (ha : 0 < a)
    {p q : X} (hpq : p ≠ q) (hε : 0 ≤ ε)
    (hfe : ε ≤ satDist a p q / 2) :
    ¬ ∃ m : X, satDist a p m ≤ satDist a p q / 2 + ε ∧
               satDist a m q ≤ satDist a p q / 2 + ε := by
  sorry

CONCRETE COUNTEREXAMPLE.  Take `X = ℝ`, `a = 1`, `p = 0`, `q = 10`,
`m = 5` (the true midpoint), and `ε = satDist 1 0 10 / 2`.

All hypotheses of the dropped claim hold:
* `0 < a` (`a = 1`),
* `p ≠ q` (`0 ≠ 10`),
* `0 ≤ ε` (`satDist` is nonnegative),
* `ε ≤ satDist a p q / 2` (in fact `ε = satDist a p q / 2`).

Yet `m = 5` *is* an ε-midpoint: since `satDist 1 0 10 / 2 + ε = satDist 1 0 10`,
and `satDist 1 0 5 = f 1 5 ≤ f 1 10 = satDist 1 0 10` by monotonicity of `f`
(and likewise `satDist 1 5 10 = f 1 5`), both required inequalities hold.
This refutes the weakened claim, certifying that the quadratic bound in
`SatReadout.no_eps_midpoint` is doing real work.
-/
theorem eps_midpoint_counterexample :
    ∃ (a ε : ℝ) (p q m : ℝ),
      0 < a ∧ p ≠ q ∧ 0 ≤ ε ∧ ε ≤ satDist a p q / 2 ∧
        satDist a p m ≤ satDist a p q / 2 + ε ∧
        satDist a m q ≤ satDist a p q / 2 + ε := by
  unfold satDist;
  use 1;
  unfold f;
  refine' ⟨ _, 0, 1, 0.5, _, _, _, _, _ ⟩ <;> norm_num [ Real.dist_eq ];
  exact ( 1 - Real.exp ( -1 ) ) / 2;
  · linarith [ Real.exp_le_one_iff.2 ( show -1 ≤ 0 by norm_num ) ];
  · norm_num;
  · linarith [ Real.exp_le_exp.2 ( show -1 ≤ - ( 1 / 2 ) by norm_num ) ]

/-
The general claim (the dropped-bound version of `no_eps_midpoint`) is FALSE.
We disprove the universally quantified statement directly by instantiating it at
the counterexample above (`X = ℝ`, `a = 1`, `p = 0`, `q = 10`, `m = 5`,
`ε = satDist 1 0 10 / 2`).
-/
theorem no_eps_midpoint_without_quadratic_bound_is_false :
    ¬ ∀ (X : Type) [MetricSpace X] (a ε : ℝ), 0 < a →
        ∀ (p q : X), p ≠ q → 0 ≤ ε → ε ≤ satDist a p q / 2 →
        ¬ ∃ m : X, satDist a p m ≤ satDist a p q / 2 + ε ∧
                   satDist a m q ≤ satDist a p q / 2 + ε := by
  push_neg;
  have := @eps_midpoint_counterexample;
  obtain ⟨ a, ε, p, q, m, ha, hpq, hε, hfe, hpm, hmq ⟩ := this; exact ⟨ ℝ, inferInstance, a, ε, ha, p, q, hpq, hε, hfe, m, hpm, hmq ⟩ ;