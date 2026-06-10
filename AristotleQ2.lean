/- ARISTOTLE Q2 — fill the sorry (T4 completion).
Prove the saturated pseudometric induces the SAME uniformity as the ambient
one. Project lemmas available (Analysis.SatReadout):
  SatReadout.f_le_self    : 0 < a → f a t ≤ t
  SatReadout.sq_lower     : 0 < a → 0 ≤ t → t - t^2/(2*a) ≤ f a t
  SatReadout.strictMono_f : 0 < a → StrictMono (f a)
Sandwich argument: f a t ≤ t gives one entourage inclusion; for the other,
on t ≤ a we have f a t ≥ t·(1 − t/(2a)) ≥ t/2, so dist-balls and
satDist-balls are mutually nested. `Metric.uniformity_basis_dist` /
`Filter.HasBasis.ext` are the expected plumbing. -/
import SatReadout

open SatReadout

theorem satPseudoMetricSpace_uniformity
    {X : Type*} [m : PseudoMetricSpace X] {a : ℝ} (ha : 0 < a) :
    (satPseudoMetricSpace (X := X) a ha).toUniformSpace = m.toUniformSpace := by
  have h_amb : ∀ (s : Set (X × X)), s ∈ (PseudoMetricSpace.toUniformSpace : UniformSpace X).uniformity ↔ ∃ ε > 0, s ⊇ {p : X × X | dist p.1 p.2 < ε} := by
    intro s; exact ⟨fun hs => by
      rcases Metric.mem_uniformity_dist.1 hs with ⟨ ε, εpos, hε ⟩ ; exact ⟨ ε, εpos, fun p hp => hε hp ⟩ ;, fun hs => by
      exact Filter.mem_of_superset ( Metric.dist_mem_uniformity hs.choose_spec.1 ) hs.choose_spec.2⟩;
  have h_sat : ∀ (s : Set (X × X)), s ∈ (satPseudoMetricSpace a ha).toUniformSpace.uniformity ↔ ∃ ε > 0, s ⊇ {p : X × X | satDist a p.1 p.2 < ε} := by
    intro s;
    have := @Metric.uniformity_basis_dist X ( satPseudoMetricSpace a ha );
    exact this.mem_iff;
  ext s;
  simp_all +decide only [uniformity];
  constructor <;> rintro ⟨ ε, ε_pos, hε ⟩;
  · refine' ⟨ ε, ε_pos, fun p hp => hε _ ⟩;
    exact lt_of_le_of_lt ( SatReadout.f_le_self ha ) hp;
  · use f a ε, f_pos ha ε_pos, fun p hp => hε <| by
      exact strictMono_f ha |>.lt_iff_lt.mp hp