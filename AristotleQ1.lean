/- ARISTOTLE Q1 — fill the sorry.
Target: the lemma mathlib4 measurably lacks (Loogle 2026-06-10: pattern
`ConcaveOn, ?f (?x+?y) ≤ ?f ?x + ?f ?y` → 0 matches; Analysis/Subadditive is
sequences-only). Intended as an upstream PR.

Prove: a strictly concave function on [0,∞) vanishing at 0 is strictly
subadditive. Proof idea: x = ((y/(x+y))·0 + ((x)/(x+y))·(x+y)) is a strict
convex combination, so strict concavity gives
  f x > (y/(x+y))·f 0 + (x/(x+y))·f (x+y) = (x/(x+y))·f (x+y);
symmetrically for y; add the two inequalities.
Useful: ConcaveOn.slope_anti_adjacent / StrictConcaveOn.2 / smul_le_smul. -/
import Mathlib

theorem StrictConcaveOn.subadditive_of_map_zero
    {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) (h0 : f 0 = 0)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    f (x + y) < f x + f y := by
  have := hf.2 ( show 0 ∈ Set.Ici 0 by norm_num ) ( show x + y ∈ Set.Ici 0 by norm_num; linarith ) ( by linarith );
  have := @this ( y / ( x + y ) ) ( x / ( x + y ) ) ( by positivity ) ( by positivity ) ( by rw [ ← add_div, div_eq_iff ] <;> linarith ) ; simp_all +decide [ mul_comm, div_eq_inv_mul ];
  have := ‹∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 → b * f ( x + y ) < f ( b * ( x + y ) ) › ( show 0 < x / ( x + y ) by positivity ) ( show 0 < y / ( x + y ) by positivity ) ( by rw [ ← add_div, div_self <| by positivity ] ) ; simp_all +decide [ div_eq_inv_mul, mul_comm, mul_left_comm, ne_of_gt ( add_pos hx hy ) ] ;
  nlinarith [ mul_inv_cancel_left₀ ( by linarith : ( x + y ) ≠ 0 ) ( f ( x + y ) ) ]