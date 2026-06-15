/-
SatReadoutGeodesic: the Riemannian / length-space exclusion, FORMALIZED against
mathlib's betweenness + midpoint API — moving the BBI 2.4.16 corollary from prose
(where the 2026-06-10 notes left it, believing mathlib had no length theory) to a
theorem. The needed lemmas are confirmed present in mathlib v4.28.0 (no bump):
  · `dist_add_dist_eq_iff` (Analysis/Convex/StrictConvexBetween): dist-additivity ↔ `Wbtw`
  · `dist_left_midpoint` / `dist_right_midpoint` (Analysis/Normed/Affine/AddTorsor)
Base must be a strict-convex normed ℝ-space (e.g. `EuclideanSpace ℝ (Fin n)`),
where mathlib's geodesic/betweenness vocabulary applies; SatReadout's gates over
general `[MetricSpace X]` specialise to it.
-/
import SatReadout

namespace SatReadout

section StrictConvexBase
-- Base = a strict-convex normed ℝ-space `V` (e.g. `EuclideanSpace ℝ (Fin n)`).
-- `NormedAddCommGroup V` gives `MetricSpace V`; the self-torsor `NormedAddTorsor V V`
-- is automatic — so mathlib's betweenness/midpoint API and SatReadout's gates coincide.
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [StrictConvexSpace ℝ V] {a : ℝ}

/-- `collinear_strict` in mathlib's vocabulary: for points genuinely BETWEEN
(`Wbtw ℝ p r q`, equivalent to dist-additivity by `dist_add_dist_eq_iff`), the
saturated metric is STRICTLY super-additive — the non-Riemannian signature, stated
with the canonical betweenness predicate rather than an ad-hoc additivity hypothesis. -/
theorem collinear_strict_wbtw (ha : 0 < a) {p r q : V}
    (h : Wbtw ℝ p r q) (hpr : p ≠ r) (hrq : r ≠ q) :
    satDist a p q < satDist a p r + satDist a r q :=
  collinear_strict ha (dist_add_dist_eq_iff.mpr h) hpr hrq

-- strict convexity is NOT needed here: the segment midpoint exists in any normed
-- ℝ-space and `no_midpoint` is general — only `collinear_strict_wbtw` needs it.
omit [StrictConvexSpace ℝ V] in
/-- The length-space exclusion, FORMAL (was prose): the base metric `dist` has a
midpoint of any two distinct points (the segment midpoint `midpoint ℝ p q`), but the
saturated metric `satDist = f_a ∘ dist` has NONE. Hence `f_a ∘ dist` destroys the
geodesic structure `(P, dist)` carries — a fortiori `(P, satDist)` is not a length
metric, not Riemannian. -/
theorem satDist_breaks_geodesic (ha : 0 < a) {p q : V} (hpq : p ≠ q) :
    (∃ m : V, dist p m = dist p q / 2 ∧ dist m q = dist p q / 2) ∧
    ¬ ∃ m : V, satDist a p m = satDist a p q / 2 ∧ satDist a m q = satDist a p q / 2 := by
  refine ⟨⟨midpoint ℝ p q, ?_, ?_⟩, no_midpoint ha hpq⟩
  · rw [dist_left_midpoint, Real.norm_ofNat]; ring
  · rw [dist_midpoint_right, Real.norm_ofNat]; ring

end StrictConvexBase

end SatReadout
