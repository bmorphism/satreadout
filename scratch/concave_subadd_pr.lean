import Mathlib

/-!
# Concave functions vanishing at 0 are subadditive  (mathlib PR candidate)

mathlib has `Convex_subadditive_le` (subadditive ⇒ convex sublevel sets) but no
forward `concave + f 0 = 0 ⇒ subadditive` lemma (`Analysis/Subadditive` is the
Fekete sequence theory only). These fill that gap.

Idea: `x = (y/(x+y))·0 + (x/(x+y))·(x+y)` is a (nontrivial) convex combination,
so (strict) concavity at `0, x+y` with `f 0 = 0` gives `(x/(x+y))·f(x+y) (<)≤ f x`;
symmetrically for `y`; add and use `(x+y)/(x+y) = 1`.
-/

open Set

theorem ConcaveOn.subadditive_of_map_zero
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Ici 0) f) (h0 : f 0 = 0)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f (x + y) ≤ f x + f y := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp [h0]
  rcases eq_or_lt_of_le hy with rfl | hy
  · simp [h0]
  have hxy0 : x + y ≠ 0 := by positivity
  have m0 : (0:ℝ) ∈ Ici (0:ℝ) := self_mem_Ici
  have mxy : x + y ∈ Ici (0:ℝ) := mem_Ici.mpr (by positivity)
  have hax : x / (x + y) * (x + y) = x := by field_simp
  have hay : y / (x + y) * (x + y) = y := by field_simp
  have hbx : x / (x + y) * f (x + y) ≤ f x := by
    have key := hf.2 m0 mxy (by positivity) (by positivity)
      (show y / (x + y) + x / (x + y) = 1 by rw [← add_div, add_comm y x, div_self hxy0])
    simp only [smul_eq_mul, h0, mul_zero, zero_add] at key
    rwa [hax] at key
  have hby : y / (x + y) * f (x + y) ≤ f y := by
    have key := hf.2 m0 mxy (by positivity) (by positivity)
      (show x / (x + y) + y / (x + y) = 1 by rw [← add_div, div_self hxy0])
    simp only [smul_eq_mul, h0, mul_zero, zero_add] at key
    rwa [hay] at key
  have hcomb : x / (x + y) * f (x + y) + y / (x + y) * f (x + y) = f (x + y) := by
    rw [← add_mul, ← add_div, div_self hxy0, one_mul]
  linarith

theorem StrictConcaveOn.subadditive_of_map_zero
    {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Ici 0) f) (h0 : f 0 = 0)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    f (x + y) < f x + f y := by
  have hxy0 : x + y ≠ 0 := by positivity
  have hne : (0:ℝ) ≠ x + y := by positivity
  have m0 : (0:ℝ) ∈ Ici (0:ℝ) := self_mem_Ici
  have mxy : x + y ∈ Ici (0:ℝ) := mem_Ici.mpr (by positivity)
  have hax : x / (x + y) * (x + y) = x := by field_simp
  have hay : y / (x + y) * (x + y) = y := by field_simp
  have hbx : x / (x + y) * f (x + y) < f x := by
    have key := hf.2 m0 mxy hne (by positivity) (by positivity)
      (show y / (x + y) + x / (x + y) = 1 by rw [← add_div, add_comm y x, div_self hxy0])
    simp only [smul_eq_mul, h0, mul_zero, zero_add] at key
    rwa [hax] at key
  have hby : y / (x + y) * f (x + y) < f y := by
    have key := hf.2 m0 mxy hne (by positivity) (by positivity)
      (show x / (x + y) + y / (x + y) = 1 by rw [← add_div, div_self hxy0])
    simp only [smul_eq_mul, h0, mul_zero, zero_add] at key
    rwa [hay] at key
  have hcomb : x / (x + y) * f (x + y) + y / (x + y) * f (x + y) = f (x + y) := by
    rw [← add_mul, ← add_div, div_self hxy0, one_mul]
  linarith
