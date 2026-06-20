/-
SatReadoutAtlas: convex two-chart readouts.

The ML/color-space experiments use several local predictors/readouts and route or
blend them. This file proves the formal invariant survives that move: a convex
blend of two saturating readouts is still first-order raw at 0, bounded, and
strictly subadditive on positive increments. In particular, atlas/ensemble
readouts do not regain the Riemannian equality signature.
-/
import SatReadoutNotGeodesic

namespace SatReadout

variable {a b w x y t : ℝ}

/-- A two-chart saturating readout:
`w · f_a + (1-w) · f_b`.

Think of `a,b` as two local saturation scales and `w` as the chart/router
weight. The main theorems below assume `0 < w < 1`; endpoint weights collapse to
the one-chart `f`. -/
noncomputable def atlas2 (a b w t : ℝ) : ℝ :=
  w * f a t + (1 - w) * f b t

@[simp] theorem atlas2_zero : atlas2 a b w 0 = 0 := by
  simp [atlas2]

/-- The atlas readout is still first-order equal to the raw metric at 0. -/
theorem hasDerivAt_atlas2_zero (ha : 0 < a) (hb : 0 < b) :
    HasDerivAt (atlas2 a b w) 1 0 := by
  have hfa := hasDerivAt_f_zero (a := a) ha
  have hfb := hasDerivAt_f_zero (a := b) hb
  have h := (hfa.const_mul w).add (hfb.const_mul (1 - w))
  simpa [atlas2, show w * 1 + (1 - w) * 1 = (1 : ℝ) by ring] using h

/-- A convex atlas is bounded by the weighted asymptotes. -/
theorem atlas2_lt_weighted_asymptote
    (ha : 0 < a) (hb : 0 < b) (hw0 : 0 < w) (hw1 : w < 1) :
    atlas2 a b w t < w * a + (1 - w) * b := by
  have hfa := f_lt_asymptote (a := a) (t := t) ha
  have hfb := f_lt_asymptote (a := b) (t := t) hb
  have hwa := mul_lt_mul_of_pos_left hfa hw0
  have hwb := mul_lt_mul_of_pos_left hfb (by linarith : 0 < 1 - w)
  unfold atlas2
  linarith

theorem atlas2_nonneg
    (ha : 0 < a) (hb : 0 < b) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ht : 0 ≤ t) :
    0 ≤ atlas2 a b w t := by
  have hfa := f_nonneg (a := a) ha ht
  have hfb := f_nonneg (a := b) hb ht
  have hwa : 0 ≤ w * f a t := mul_nonneg hw0 hfa
  have hwb : 0 ≤ (1 - w) * f b t := mul_nonneg (by linarith) hfb
  unfold atlas2
  linarith

/-- Exact atlas defect: a weighted sum of the two one-chart defects. -/
theorem atlas2_defect (ha : 0 < a) (hb : 0 < b) :
    atlas2 a b w x + atlas2 a b w y - atlas2 a b w (x + y)
      = w * (f a x * f a y / a) + (1 - w) * (f b x * f b y / b) := by
  have hka := key_identity (a := a) ha x y
  have hkb := key_identity (a := b) hb x y
  calc
    atlas2 a b w x + atlas2 a b w y - atlas2 a b w (x + y)
        = w * (f a x + f a y - f a (x + y)) +
            (1 - w) * (f b x + f b y - f b (x + y)) := by
          unfold atlas2
          ring
    _ = w * (f a x * f a y / a) + (1 - w) * (f b x * f b y / b) := by
          rw [hka, hkb]

theorem atlas2_subadd
    (ha : 0 < a) (hb : 0 < b) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    atlas2 a b w (x + y) ≤ atlas2 a b w x + atlas2 a b w y := by
  have hsa := subadd (a := a) ha hx hy
  have hsb := subadd (a := b) hb hx hy
  have hwa := mul_le_mul_of_nonneg_left hsa hw0
  have hwb := mul_le_mul_of_nonneg_left hsb (by linarith : 0 ≤ 1 - w)
  unfold atlas2
  linarith

/-- The atlas keeps the non-Riemannian strict subadditivity signature. -/
theorem atlas2_strict_subadd
    (ha : 0 < a) (hb : 0 < b) (hw0 : 0 < w) (hw1 : w < 1)
    (hx : 0 < x) (hy : 0 < y) :
    atlas2 a b w (x + y) < atlas2 a b w x + atlas2 a b w y := by
  have hsa := strict_subadd (a := a) ha hx hy
  have hsb := strict_subadd (a := b) hb hx hy
  have hwa := mul_lt_mul_of_pos_left hsa hw0
  have hwb := mul_lt_mul_of_pos_left hsb (by linarith : 0 < 1 - w)
  unfold atlas2
  linarith

theorem strictMono_atlas2
    (ha : 0 < a) (hb : 0 < b) (hw0 : 0 < w) (hw1 : w < 1) :
    StrictMono (atlas2 a b w) := by
  intro s t hst
  have hfa := strictMono_f (a := a) ha hst
  have hfb := strictMono_f (a := b) hb hst
  have hwa := mul_lt_mul_of_pos_left hfa hw0
  have hwb := mul_lt_mul_of_pos_left hfb (by linarith : 0 < 1 - w)
  unfold atlas2
  linarith

section PseudoMetric

variable {X : Type*} [PseudoMetricSpace X]

/-- The atlas-saturated distance `D = atlas2 a b w ∘ d`. -/
noncomputable def satAtlasDist (a b w : ℝ) (p q : X) : ℝ :=
  atlas2 a b w (dist p q)

theorem satAtlasDist_self (p : X) : satAtlasDist a b w p p = 0 := by
  simp [satAtlasDist]

theorem satAtlasDist_comm (p q : X) : satAtlasDist a b w p q = satAtlasDist a b w q p := by
  simp [satAtlasDist, dist_comm]

theorem satAtlasDist_triangle
    (ha : 0 < a) (hb : 0 < b) (hw0 : 0 < w) (hw1 : w < 1) (p q r : X) :
    satAtlasDist a b w p r ≤ satAtlasDist a b w p q + satAtlasDist a b w q r := by
  have hmono : atlas2 a b w (dist p r) ≤ atlas2 a b w (dist p q + dist q r) :=
    (strictMono_atlas2 ha hb hw0 hw1).monotone (dist_triangle p q r)
  have hsub := atlas2_subadd (a := a) (b := b) (w := w)
    ha hb hw0.le hw1.le
    (show 0 ≤ dist p q from dist_nonneg)
    (show 0 ≤ dist q r from dist_nonneg)
  unfold satAtlasDist
  exact hmono.trans hsub

noncomputable def satAtlasPseudoMetricSpace
    (a b w : ℝ) (ha : 0 < a) (hb : 0 < b) (hw0 : 0 < w) (hw1 : w < 1) :
    PseudoMetricSpace X where
  dist p q := satAtlasDist a b w p q
  dist_self := satAtlasDist_self
  dist_comm := satAtlasDist_comm
  dist_triangle := satAtlasDist_triangle ha hb hw0 hw1

end PseudoMetric

section MetricGates

variable {X : Type*} [MetricSpace X]

/-- Atlas form of the collinear strictness gate: even blended/local readouts
break Riemannian length-additivity on positive collinear pieces. -/
theorem atlas2_collinear_strict
    (ha : 0 < a) (hb : 0 < b) (hw0 : 0 < w) (hw1 : w < 1) {p r q : X}
    (h : dist p r + dist r q = dist p q) (hpr : p ≠ r) (hrq : r ≠ q) :
    satAtlasDist a b w p q < satAtlasDist a b w p r + satAtlasDist a b w r q := by
  have h1 : 0 < dist p r := dist_pos.mpr hpr
  have h2 : 0 < dist r q := dist_pos.mpr hrq
  have heq : satAtlasDist a b w p q = atlas2 a b w (dist p r + dist r q) := by
    unfold satAtlasDist
    rw [h]
  rw [heq]
  exact atlas2_strict_subadd ha hb hw0 hw1 h1 h2

end MetricGates

section FiniteAtlas

variable {ι : Type*} [Fintype ι]
variable {scale weight : ι → ℝ}

/-- A finite weighted atlas of saturating readouts. This is the formal version of
the color-space ensemble story: each chart has its own saturation scale, and the
weights blend their readouts. -/
noncomputable def atlasN (scale weight : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, weight i * f (scale i) t

@[simp] theorem atlasN_zero : atlasN scale weight 0 = 0 := by
  simp [atlasN]

/-- The derivative at zero is the total atlas weight. Thus normalized finite
atlases are first-order equal to the raw metric. -/
theorem hasDerivAt_atlasN_zero (hs : ∀ i, 0 < scale i) :
    HasDerivAt (atlasN scale weight) (∑ i, weight i) 0 := by
  unfold atlasN
  simpa using HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hasDerivAt_f_zero (a := scale i) (hs i)).const_mul (weight i))

theorem hasDerivAt_atlasN_zero_of_sum_weight_eq_one
    (hs : ∀ i, 0 < scale i) (hw_sum : ∑ i, weight i = 1) :
    HasDerivAt (atlasN scale weight) 1 0 := by
  simpa [hw_sum] using hasDerivAt_atlasN_zero (scale := scale) (weight := weight) hs

theorem atlasN_nonneg
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i) (ht : 0 ≤ t) :
    0 ≤ atlasN scale weight t := by
  unfold atlasN
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hw i) (f_nonneg (a := scale i) (hs i) ht)

theorem atlasN_pos
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i)
    {k : ι} (hwk : 0 < weight k) (ht : 0 < t) :
    0 < atlasN scale weight t := by
  unfold atlasN
  exact Finset.sum_pos' (fun i _ =>
    mul_nonneg (hw i) (f_nonneg (a := scale i) (hs i) ht.le))
    ⟨k, Finset.mem_univ k, mul_pos hwk (f_pos (a := scale k) (hs k) ht)⟩

/-- A finite atlas saturates below the weighted sum of chart asymptotes. -/
theorem atlasN_lt_weighted_asymptote
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i)
    {k : ι} (hwk : 0 < weight k) :
    atlasN scale weight t < ∑ i, weight i * scale i := by
  unfold atlasN
  exact Finset.sum_lt_sum
    (fun i _ => mul_le_mul_of_nonneg_left
      (le_of_lt (f_lt_asymptote (a := scale i) (t := t) (hs i))) (hw i))
    ⟨k, Finset.mem_univ k,
      mul_lt_mul_of_pos_left (f_lt_asymptote (a := scale k) (t := t) (hs k)) hwk⟩

/-- A finite atlas never exceeds its total-weight multiple of the raw metric. -/
theorem atlasN_le_weighted_self
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i) :
    atlasN scale weight t ≤ (∑ i, weight i) * t := by
  unfold atlasN
  calc
    ∑ i, weight i * f (scale i) t
        ≤ ∑ i, weight i * t := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (f_le_self (a := scale i) (t := t) (hs i)) (hw i)
    _ = (∑ i, weight i) * t := by
          rw [Finset.sum_mul]

/-- Normalized finite atlases stay below the raw metric everywhere. -/
theorem atlasN_le_self_of_sum_weight_eq_one
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i)
    (hw_sum : ∑ i, weight i = 1) :
    atlasN scale weight t ≤ t := by
  simpa [hw_sum] using
    atlasN_le_weighted_self (scale := scale) (weight := weight) (t := t) hs hw

/-- Near zero, a finite atlas keeps the weighted quadratic lower envelope of
the underlying charts. -/
theorem atlasN_sq_lower_weighted
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i) (ht : 0 ≤ t) :
    (∑ i, weight i * (t - t ^ 2 / (2 * scale i))) ≤ atlasN scale weight t := by
  unfold atlasN
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (sq_lower (a := scale i) (t := t) (hs i) ht) (hw i)

theorem atlasN_monotone
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i) :
    Monotone (atlasN scale weight) := by
  intro s t hst
  unfold atlasN
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left ((strictMono_f (a := scale i) (hs i)).monotone hst) (hw i)

/-- Exact finite-atlas defect: a weighted sum of the one-chart defects. -/
theorem atlasN_defect (hs : ∀ i, 0 < scale i) :
    atlasN scale weight x + atlasN scale weight y - atlasN scale weight (x + y)
      = ∑ i, weight i * (f (scale i) x * f (scale i) y / scale i) := by
  calc
    atlasN scale weight x + atlasN scale weight y - atlasN scale weight (x + y)
        = ∑ i, weight i *
            (f (scale i) x + f (scale i) y - f (scale i) (x + y)) := by
          unfold atlasN
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ i, weight i * (f (scale i) x * f (scale i) y / scale i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [key_identity (a := scale i) (hs i) x y]

theorem atlasN_subadd
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    atlasN scale weight (x + y) ≤ atlasN scale weight x + atlasN scale weight y := by
  unfold atlasN
  calc
    ∑ i, weight i * f (scale i) (x + y)
        ≤ ∑ i, weight i * (f (scale i) x + f (scale i) y) := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (subadd (a := scale i) (hs i) hx hy) (hw i)
    _ = ∑ i, weight i * f (scale i) x + ∑ i, weight i * f (scale i) y := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring

theorem atlasN_strict_subadd
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i)
    {k : ι} (hwk : 0 < weight k) (hx : 0 < x) (hy : 0 < y) :
    atlasN scale weight (x + y) < atlasN scale weight x + atlasN scale weight y := by
  have hdef := atlasN_defect (scale := scale) (weight := weight) (x := x) (y := y) hs
  have hnonneg : ∀ i, 0 ≤ weight i * (f (scale i) x * f (scale i) y / scale i) := by
    intro i
    exact mul_nonneg (hw i) (div_nonneg
      (mul_nonneg (f_nonneg (a := scale i) (hs i) hx.le)
        (f_nonneg (a := scale i) (hs i) hy.le))
      (le_of_lt (hs i)))
  have hkpos : 0 < weight k * (f (scale k) x * f (scale k) y / scale k) := by
    exact mul_pos hwk (div_pos
      (mul_pos (f_pos (a := scale k) (hs k) hx)
        (f_pos (a := scale k) (hs k) hy))
      (hs k))
  have hsumpos : 0 < ∑ i, weight i * (f (scale i) x * f (scale i) y / scale i) := by
    exact Finset.sum_pos' (fun i _ => hnonneg i) ⟨k, Finset.mem_univ k, hkpos⟩
  linarith

section PseudoMetric

variable {X : Type*} [PseudoMetricSpace X]

/-- The finite-atlas saturated distance. -/
noncomputable def satAtlasNDist (scale weight : ι → ℝ) (p q : X) : ℝ :=
  atlasN scale weight (dist p q)

theorem satAtlasNDist_self (p : X) : satAtlasNDist scale weight p p = 0 := by
  simp [satAtlasNDist]

theorem satAtlasNDist_comm (p q : X) :
    satAtlasNDist scale weight p q = satAtlasNDist scale weight q p := by
  simp [satAtlasNDist, dist_comm]

theorem satAtlasNDist_le_weighted_dist
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i) (p q : X) :
    satAtlasNDist scale weight p q ≤ (∑ i, weight i) * dist p q := by
  simpa [satAtlasNDist] using
    atlasN_le_weighted_self (scale := scale) (weight := weight) (t := dist p q) hs hw

theorem satAtlasNDist_le_dist_of_sum_weight_eq_one
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i)
    (hw_sum : ∑ i, weight i = 1) (p q : X) :
    satAtlasNDist scale weight p q ≤ dist p q := by
  simpa [satAtlasNDist] using
    atlasN_le_self_of_sum_weight_eq_one
      (scale := scale) (weight := weight) (t := dist p q) hs hw hw_sum

theorem satAtlasNDist_sq_lower_weighted
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i) (p q : X) :
    (∑ i, weight i * (dist p q - dist p q ^ 2 / (2 * scale i))) ≤
      satAtlasNDist scale weight p q := by
  simpa [satAtlasNDist] using
    atlasN_sq_lower_weighted (scale := scale) (weight := weight) (t := dist p q)
      hs hw (show 0 ≤ dist p q from dist_nonneg)

theorem satAtlasNDist_triangle
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i) (p q r : X) :
    satAtlasNDist scale weight p r ≤
      satAtlasNDist scale weight p q + satAtlasNDist scale weight q r := by
  have hmono := atlasN_monotone (scale := scale) (weight := weight) hs hw
  have h1 : atlasN scale weight (dist p r) ≤
      atlasN scale weight (dist p q + dist q r) :=
    hmono (dist_triangle p q r)
  have h2 := atlasN_subadd (scale := scale) (weight := weight) hs hw
    (show 0 ≤ dist p q from dist_nonneg)
    (show 0 ≤ dist q r from dist_nonneg)
  unfold satAtlasNDist
  exact h1.trans h2

noncomputable def satAtlasNPseudoMetricSpace
    (scale weight : ι → ℝ) (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i) :
    PseudoMetricSpace X where
  dist p q := satAtlasNDist scale weight p q
  dist_self := satAtlasNDist_self
  dist_comm := satAtlasNDist_comm
  dist_triangle := satAtlasNDist_triangle hs hw

end PseudoMetric

section MetricGates

variable {X : Type*} [MetricSpace X]

/-- Finite-atlas collinear strictness. One genuinely active chart is enough:
finite mixtures still cannot recover Riemannian length additivity. -/
theorem atlasN_collinear_strict
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i)
    {k : ι} (hwk : 0 < weight k) {p r q : X}
    (h : dist p r + dist r q = dist p q) (hpr : p ≠ r) (hrq : r ≠ q) :
    satAtlasNDist scale weight p q <
      satAtlasNDist scale weight p r + satAtlasNDist scale weight r q := by
  have h1 : 0 < dist p r := dist_pos.mpr hpr
  have h2 : 0 < dist r q := dist_pos.mpr hrq
  have heq : satAtlasNDist scale weight p q =
      atlasN scale weight (dist p r + dist r q) := by
    unfold satAtlasNDist
    rw [h]
  rw [heq]
  exact atlasN_strict_subadd (scale := scale) (weight := weight) hs hw hwk h1 h2

/-- Finite-atlas midpoint exclusion. Even after blending many local readouts,
no point can split the atlas distance of a distinct pair exactly in half. -/
theorem satAtlasNDist_no_midpoint
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i)
    {k : ι} (hwk : 0 < weight k) {p q : X} (hpq : p ≠ q) :
    ¬ ∃ m : X, satAtlasNDist scale weight p m = satAtlasNDist scale weight p q / 2 ∧
               satAtlasNDist scale weight m q = satAtlasNDist scale weight p q / 2 := by
  rintro ⟨m, h1, h2⟩
  have ht : 0 < dist p q := dist_pos.mpr hpq
  have hDpos : 0 < satAtlasNDist scale weight p q := by
    exact atlasN_pos (scale := scale) (weight := weight) hs hw hwk ht
  have htri : dist p q ≤ dist p m + dist m q := dist_triangle p m q
  have hs1 : 0 < dist p m := by
    rcases (dist_nonneg : 0 ≤ dist p m).lt_or_eq with hc | hc
    · exact hc
    · exfalso
      have hz : satAtlasNDist scale weight p m = 0 := by
        unfold satAtlasNDist
        rw [← hc]
        simp
      rw [hz] at h1
      linarith
  have hs2 : 0 < dist m q := by
    rcases (dist_nonneg : 0 ≤ dist m q).lt_or_eq with hc | hc
    · exact hc
    · exfalso
      have hz : satAtlasNDist scale weight m q = 0 := by
        unfold satAtlasNDist
        rw [← hc]
        simp
      rw [hz] at h2
      linarith
  have hsum : atlasN scale weight (dist p m) + atlasN scale weight (dist m q)
      = atlasN scale weight (dist p q) := by
    simp only [satAtlasNDist] at h1 h2
    linarith
  have hmono : atlasN scale weight (dist p q) ≤
      atlasN scale weight (dist p m + dist m q) :=
    atlasN_monotone (scale := scale) (weight := weight) hs hw htri
  have hstrict : atlasN scale weight (dist p m + dist m q) <
      atlasN scale weight (dist p m) + atlasN scale weight (dist m q) :=
    atlasN_strict_subadd (scale := scale) (weight := weight) hs hw hwk hs1 hs2
  linarith

/-- Finite-atlas geodesic exclusion: one active positive chart is enough to
destroy metric segments. This is the many-chart analogue of
`satDist_not_geodesic`. -/
theorem satAtlasNDist_not_geodesic [Nontrivial X]
    (hs : ∀ i, 0 < scale i) (hw : ∀ i, 0 ≤ weight i)
    {k : ι} (hwk : 0 < weight k) :
    ¬ IsGeodesicMetric (X := X) (satAtlasNDist scale weight) := by
  intro h
  obtain ⟨p, q, hpq⟩ := exists_pair_ne X
  exact satAtlasNDist_no_midpoint
    (scale := scale) (weight := weight) hs hw hwk hpq
    (h.midpointConvex p q hpq)

end MetricGates

end FiniteAtlas

end SatReadout
