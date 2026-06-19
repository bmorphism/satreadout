/-
SatReadoutNotGeodesic: upgrade "no midpoint" to the textbook statement
"`satDist` is not a geodesic metric space" — a full Lean theorem, closing the
gap where `non-Riemannian` was previously a classical (Hopf–Rinow) inference.

A *geodesic metric space* is one where every pair `p, q` is joined by a metric
segment: an `γ : ℝ → X` with `γ 0 = p`, `γ 1 = q`, and `D (γ s) (γ t) = |s−t|·D p q`
on `[0,1]` (isometric image of an interval). This is the standard definition; a
complete Riemannian manifold is geodesic (Hopf–Rinow). We prove `satDist` fails it.
-/
import SatReadout

open SatReadout Set

/-- A metric is *midpoint-convex* (Menger) if every distinct pair has a metric
midpoint. -/
def MidpointConvexFn {X : Type*} [MetricSpace X] (D : X → X → ℝ) : Prop :=
  ∀ p q : X, p ≠ q → ∃ m, D p m = D p q / 2 ∧ D m q = D p q / 2

/-- A metric is *geodesic* if every pair is joined by a metric segment (an
isometric image of `[0,1]` rescaled to length `D p q`). -/
def IsGeodesicMetric {X : Type*} [MetricSpace X] (D : X → X → ℝ) : Prop :=
  ∀ p q : X, ∃ γ : ℝ → X, γ 0 = p ∧ γ 1 = q ∧
    ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, D (γ s) (γ t) = |s - t| * D p q

/-- Every geodesic metric is midpoint-convex: the segment's `γ(1/2)` is the
midpoint. -/
theorem IsGeodesicMetric.midpointConvex {X : Type*} [MetricSpace X] {D : X → X → ℝ}
    (h : IsGeodesicMetric D) : MidpointConvexFn D := by
  intro p q _
  obtain ⟨γ, h0, h1, hiso⟩ := h p q
  refine ⟨γ (1/2), ?_, ?_⟩
  · have e := hiso 0 (by norm_num) (1/2) (by norm_num)
    rw [h0] at e
    rw [e, abs_of_nonpos (by norm_num : (0:ℝ) - 1/2 ≤ 0)]; ring
  · have e := hiso (1/2) (by norm_num) 1 (by norm_num)
    rw [h1] at e
    rw [e, abs_of_nonpos (by norm_num : (1:ℝ)/2 - 1 ≤ 0)]; ring

/-- Sanity / non-vacuity: an ordinary metric (here `ℝ`) IS geodesic, via the
linear segment `t ↦ (1-t)p + t q`. So `IsGeodesicMetric` is a real property that
ordinary metrics satisfy — and `satDist` provably does not (below). -/
example : IsGeodesicMetric (X := ℝ) dist := by
  intro p q
  refine ⟨fun t => (1 - t) * p + t * q, by ring, by ring, ?_⟩
  intro s _ t _
  simp only [Real.dist_eq]
  rw [show (1 - s) * p + s * q - ((1 - t) * p + t * q) = (s - t) * (q - p) by ring,
      abs_mul, abs_sub_comm q p]

/-- **The saturated perceptual metric is not a geodesic space.** For any metric
space with at least two points and `0 < a`, `satDist a = f_a ∘ dist` admits no
metric segments — because it has no midpoints (`no_midpoint`). Hence it is not a
length/geodesic metric, and (Hopf–Rinow) not the distance of any complete
Riemannian structure. -/
theorem satDist_not_geodesic {X : Type*} [MetricSpace X] [Nontrivial X]
    {a : ℝ} (ha : 0 < a) : ¬ IsGeodesicMetric (X := X) (satDist a) := by
  intro h
  obtain ⟨p, q, hpq⟩ := exists_pair_ne X
  exact no_midpoint ha hpq (h.midpointConvex p q hpq)
