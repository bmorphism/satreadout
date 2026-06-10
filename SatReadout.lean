/-
SatReadout: the saturating perceptual readout f_a(t) = a·(1 − exp(−t/a))
and the non-Riemannian gate theorems.

Companion to ~/worlds/o/MATHLIB4_NONRIEMANNIAN.md and IMPROVE_NONRIEMANNIAN.md.
Everything flows from the KEY identity (divisionless form, pure ring):
    f_a x · f_a y = a · (f_a x + f_a y − f_a (x+y))
which needs only `Real.exp_add` — no convexity theory, and not even 0 < a.

T1: local validity (f 0 = 0, derivative 1 at 0, t − t²/2a ≤ f t ≤ t, f < a)
T3: strict subadditivity (defect = f x · f y / a)
T5: collinear strictness, no-midpoint, no-ε-midpoint — valid in ANY
    metric space; no length-space theory required (mathlib has none,
    confirmed by Loogle 2026-06-10).
-/
import Mathlib

namespace SatReadout

noncomputable def f (a t : ℝ) : ℝ := a * (1 - Real.exp (-t / a))

variable {a x y t ε : ℝ}

@[simp] theorem f_zero : f a 0 = 0 := by simp [f]

/-- KEY identity, divisionless: `f x * f y = a * (f x + f y − f (x+y))`.
Pure `exp_add` + `ring`; holds for ALL `a` (even `a = 0`). The engine of
every theorem below. -/
theorem key_identity' (x y : ℝ) :
    f a x * f a y = a * (f a x + f a y - f a (x + y)) := by
  have hexp : Real.exp (-(x + y) / a) = Real.exp (-x / a) * Real.exp (-y / a) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold f
  rw [hexp]
  ring

/-- KEY identity, divided form (needs `0 < a`):
the subadditivity defect is exactly `f x * f y / a`. -/
theorem key_identity (ha : 0 < a) (x y : ℝ) :
    f a x + f a y - f a (x + y) = f a x * f a y / a := by
  have h := key_identity' (a := a) x y
  field_simp
  linarith [h]

theorem strictMono_f (ha : 0 < a) : StrictMono (f a) := by
  intro s t hst
  unfold f
  have h0 : -t / a < -s / a := by
    apply div_lt_div_of_pos_right (by linarith) ha
  have h1 : Real.exp (-t / a) < Real.exp (-s / a) := Real.exp_lt_exp.mpr h0
  nlinarith [h1, ha]

theorem f_nonneg (ha : 0 < a) (ht : 0 ≤ t) : 0 ≤ f a t := by
  simpa using (strictMono_f ha).monotone ht

theorem f_pos (ha : 0 < a) (ht : 0 < t) : 0 < f a t := by
  simpa using strictMono_f ha ht

/-- Saturation: `f a t < a` always (asymptote). -/
theorem f_lt_asymptote (ha : 0 < a) : f a t < a := by
  unfold f
  nlinarith [Real.exp_pos (-t / a), ha]

/-- T1 upper: `f a t ≤ t` for all `t` (tangent line at 0).
Only needs `Real.add_one_le_exp`. -/
theorem f_le_self (ha : 0 < a) : f a t ≤ t := by
  have h := Real.add_one_le_exp (-(t / a))
  have key : 1 - Real.exp (-(t / a)) ≤ t / a := by linarith
  have harg : -t / a = -(t / a) := by ring
  calc f a t = a * (1 - Real.exp (-(t / a))) := by rw [f, harg]
    _ ≤ a * (t / a) := mul_le_mul_of_nonneg_left key ha.le
    _ = t := by rw [mul_div_cancel₀ _ ha.ne']

/-- T1 lower (quadratic): `t − t²/(2a) ≤ f a t` for `t ≥ 0`.
Route: `quadratic_le_exp_of_nonneg` + the identity
`(1 − x + x²/2)(1 + x + x²/2) = 1 + x⁴/4 ≥ 1`. -/
theorem sq_lower (ha : 0 < a) (ht : 0 ≤ t) : t - t ^ 2 / (2 * a) ≤ f a t := by
  set x := t / a with hxdef
  have hx0 : 0 ≤ x := div_nonneg ht ha.le
  have h1 : 1 + x + x ^ 2 / 2 ≤ Real.exp x := Real.quadratic_le_exp_of_nonneg hx0
  have hpos : (0 : ℝ) < 1 + x + x ^ 2 / 2 := by positivity
  have h4 : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]; simp
  have h2 : Real.exp (-x) * (1 + x + x ^ 2 / 2) ≤ 1 := by
    nlinarith [Real.exp_pos (-x), h1, h4]
  have h5 : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
    nlinarith [h2, hpos, sq_nonneg (x ^ 2), sq_nonneg x]
  have harg : -t / a = -x := by rw [hxdef]; ring
  have h6 : a * (x - x ^ 2 / 2) = t - t ^ 2 / (2 * a) := by
    rw [hxdef]; field_simp
  calc t - t ^ 2 / (2 * a) = a * (x - x ^ 2 / 2) := h6.symm
    _ ≤ a * (1 - Real.exp (-x)) := by nlinarith [h5, ha]
    _ = f a t := by rw [f, harg]

/-- T1: derivative 1 at the origin — `f` agrees with the identity (= raw ΔE)
to first order, where CIEDE2000 is valid. -/
theorem hasDerivAt_f_zero (ha : 0 < a) : HasDerivAt (f a) 1 0 := by
  have h1 : HasDerivAt (fun s : ℝ => -s / a) (-1 / a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).neg.div_const a)
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s / a))
      (Real.exp (-(0 : ℝ) / a) * (-1 / a)) 0 := h1.exp
  have h3 : HasDerivAt (fun s : ℝ => a * (1 - Real.exp (-s / a)))
      (a * (0 - Real.exp (-(0 : ℝ) / a) * (-1 / a))) 0 :=
    ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub h2).const_mul a
  have h4 : HasDerivAt (f a)
      (a * (0 - Real.exp (-(0 : ℝ) / a) * (-1 / a))) 0 := h3
  have hval : a * (0 - Real.exp (-(0 : ℝ) / a) * (-1 / a)) = 1 := by
    have h0 : -(0 : ℝ) / a = 0 := by simp
    rw [h0, Real.exp_zero]
    field_simp
    ring
  rw [hval] at h4
  exact h4

/-- T3: strict subadditivity, defect `f x * f y / a > 0`. -/
theorem strict_subadd (ha : 0 < a) (hx : 0 < x) (hy : 0 < y) :
    f a (x + y) < f a x + f a y := by
  have hk := key_identity' (a := a) x y
  have h1 : 0 < f a x := f_pos ha hx
  have h2 : 0 < f a y := f_pos ha hy
  nlinarith [mul_pos h1 h2, ha]

theorem subadd (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    f a (x + y) ≤ f a x + f a y := by
  have hk := key_identity' (a := a) x y
  have h1 := f_nonneg ha hx
  have h2 := f_nonneg ha hy
  nlinarith [mul_nonneg h1 h2, ha]

/-- Midpoint defect, exact: `2·f(t/2) − f(t) = f(t/2)²/a`. -/
theorem midpoint_defect (ha : 0 < a) (t : ℝ) :
    2 * f a (t / 2) - f a t = (f a (t / 2)) ^ 2 / a := by
  have hk := key_identity ha (t / 2) (t / 2)
  have ht : t / 2 + t / 2 = t := by ring
  rw [ht] at hk
  rw [sq]
  linarith

/-! ## The metric layer -/

section PseudoMetric

variable {X : Type*} [PseudoMetricSpace X]

/-- The saturated distance `D = f_a ∘ d`. -/
noncomputable def satDist (a : ℝ) (p q : X) : ℝ := f a (dist p q)

theorem satDist_self (p : X) : satDist a p p = 0 := by simp [satDist]

theorem satDist_comm (p q : X) : satDist a p q = satDist a q p := by
  simp [satDist, dist_comm]

theorem satDist_triangle (ha : 0 < a) (p q r : X) :
    satDist a p r ≤ satDist a p q + satDist a q r := by
  have h1 : f a (dist p r) ≤ f a (dist p q + dist q r) :=
    (strictMono_f ha).monotone (dist_triangle p q r)
  exact h1.trans (subadd ha dist_nonneg dist_nonneg)

/-- T4 (metric axioms): `satDist` is a pseudometric. Uniformity equality with
the ambient structure (via the sandwich `t(1−t/2a) ≤ f t ≤ t`) is future work;
see MATHLIB4_NONRIEMANNIAN.md §4 (`PseudoMetricSpace.replaceUniformity`). -/
noncomputable def satPseudoMetricSpace (a : ℝ) (ha : 0 < a) :
    PseudoMetricSpace X where
  dist p q := satDist a p q
  dist_self := satDist_self
  dist_comm := satDist_comm
  dist_triangle := satDist_triangle ha

end PseudoMetric

section MetricGates

/- The gate theorems need `dist_pos` (distinct points at positive distance),
i.e. a genuine `MetricSpace`. -/
variable {X : Type*} [MetricSpace X]

/-- T5(a): STRICT triangle inequality on collinear (metrically-between) triples.
This is the CI property test, with its tolerance: the gap is exactly
`satDist p r · satDist r q / a`. Equality here is the Riemannian/length-metric
signature; `satDist` never attains it. -/
theorem collinear_strict (ha : 0 < a) {p r q : X}
    (h : dist p r + dist r q = dist p q) (hpr : p ≠ r) (hrq : r ≠ q) :
    satDist a p q < satDist a p r + satDist a r q := by
  have h1 : 0 < dist p r := dist_pos.mpr hpr
  have h2 : 0 < dist r q := dist_pos.mpr hrq
  have heq : satDist a p q = f a (dist p r + dist r q) := by
    unfold satDist
    rw [← h]
  rw [heq]
  exact strict_subadd ha h1 h2

/-- T5(b): NO point of `X` is a `satDist`-midpoint of two distinct points.
Holds in ANY metric space — no geodesics, no length structure assumed.
Hence `(X, satDist)` is not a length metric, a fortiori not Riemannian. -/
theorem no_midpoint (ha : 0 < a) {p q : X} (hpq : p ≠ q) :
    ¬ ∃ m : X, satDist a p m = satDist a p q / 2 ∧
               satDist a m q = satDist a p q / 2 := by
  rintro ⟨m, h1, h2⟩
  have ht : 0 < dist p q := dist_pos.mpr hpq
  have hft : 0 < f a (dist p q) := f_pos ha ht
  have htri : dist p q ≤ dist p m + dist m q := dist_triangle p m q
  have hs1 : 0 < dist p m := by
    rcases (dist_nonneg : 0 ≤ dist p m).lt_or_eq with hc | hc
    · exact hc
    · exfalso
      have hz : f a (dist p m) = 0 := by rw [← hc]; exact f_zero
      simp only [satDist] at h1
      rw [hz] at h1
      linarith
  have hs2 : 0 < dist m q := by
    rcases (dist_nonneg : 0 ≤ dist m q).lt_or_eq with hc | hc
    · exact hc
    · exfalso
      have hz : f a (dist m q) = 0 := by rw [← hc]; exact f_zero
      simp only [satDist] at h2
      rw [hz] at h2
      linarith
  have hsum : f a (dist p m) + f a (dist m q) = f a (dist p q) := by
    simp only [satDist] at h1 h2
    linarith
  have hmono : f a (dist p q) ≤ f a (dist p m + dist m q) :=
    (strictMono_f ha).monotone htri
  have hstrict : f a (dist p m + dist m q) < f a (dist p m) + f a (dist m q) :=
    strict_subadd ha hs1 hs2
  linarith

/-- T5(c), quantitative: no ε-midpoints once `2aε < (D/2 − ε)²` where
`D = satDist p q`. As ε → 0 the right side → D²/4 > 0, so every distinct pair
has an ε-midpoint-free neighbourhood — the gap a length space cannot have.
NOTE: this DERIVED bound replaces the unproven `f(t/2)²/(2a)` guess in earlier
prose; the CI test should assert this inequality. -/
theorem no_eps_midpoint (ha : 0 < a) {p q : X} (_hpq : p ≠ q) (hε : 0 ≤ ε)
    (hfe : ε ≤ satDist a p q / 2)
    (hbound : 2 * a * ε < (satDist a p q / 2 - ε) ^ 2) :
    ¬ ∃ m : X, satDist a p m ≤ satDist a p q / 2 + ε ∧
               satDist a m q ≤ satDist a p q / 2 + ε := by
  rintro ⟨m, h1, h2⟩
  have htri : dist p q ≤ dist p m + dist m q := dist_triangle p m q
  have hmono : f a (dist p q) ≤ f a (dist p m + dist m q) :=
    (strictMono_f ha).monotone htri
  have hkey := key_identity' (a := a) (dist p m) (dist m q)
  have hns1 : 0 ≤ f a (dist p m) := f_nonneg ha dist_nonneg
  have hns2 : 0 ≤ f a (dist m q) := f_nonneg ha dist_nonneg
  simp only [satDist] at h1 h2 hfe hbound ⊢
  -- defect ≥ 0 (divisionless): a·defect = f₁f₂ ≥ 0 and a > 0
  have hdefect : 0 ≤ f a (dist p m) + f a (dist m q) -
      f a (dist p m + dist m q) := by
    nlinarith [hkey, mul_nonneg hns1 hns2, ha]
  -- sum lower bound: f₁ + f₂ ≥ f t
  have hlow : f a (dist p q) ≤ f a (dist p m) + f a (dist m q) := by
    linarith
  -- individual lower bounds
  have hl1 : f a (dist p q) / 2 - ε ≤ f a (dist p m) := by linarith
  have hl2 : f a (dist p q) / 2 - ε ≤ f a (dist m q) := by linarith
  -- product upper bound, divisionless: f₁f₂ = a·defect ≤ a·2ε
  have hprod : f a (dist p m) * f a (dist m q) ≤ 2 * a * ε := by
    have hd : f a (dist p m) + f a (dist m q) -
        f a (dist p m + dist m q) ≤ 2 * ε := by linarith
    calc f a (dist p m) * f a (dist m q)
        = a * (f a (dist p m) + f a (dist m q) -
            f a (dist p m + dist m q)) := hkey
      _ ≤ a * (2 * ε) := mul_le_mul_of_nonneg_left hd ha.le
      _ = 2 * a * ε := by ring
  -- product lower bound from individual bounds (both factors ≥ D/2 − ε ≥ 0)
  have hge : (0 : ℝ) ≤ f a (dist p q) / 2 - ε := by linarith
  have hpl : (f a (dist p q) / 2 - ε) ^ 2 ≤
      f a (dist p m) * f a (dist m q) := by
    nlinarith [hl1, hl2, hge]
  nlinarith [hbound, hprod, hpl]

end MetricGates

end SatReadout
