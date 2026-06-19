# The non-Riemannian nature of perceptual color space, formalized

*A short note. Companion to the Lean 4 development in this repository
(`SatReadout.lean`, `SatReadoutGeodesic.lean`, `SatReadoutNotGeodesic.lean`;
blueprint in `blueprint/strangeness.tex`). All theorem names below are
machine-checked, mathlib `v4.28.0`, axioms = `propext, Classical.choice,
Quot.sound` only.*

## Abstract
Bujack et al. (PNAS 2022) showed empirically that perceptual color space is not
Riemannian: large color differences exhibit *diminishing returns*, so perceived
difference is subadditive, which no length/Riemannian metric can be. We give a
machine-checked Lean 4 formalization of the geometric core of this claim. Modelling
perceived difference as the saturating readout `f_a(t) = a(1 − e^{−t/a})` composed
with a local metric, we prove (i) the exact subadditivity defect `f_a(x)f_a(y)/a`
from a single algebraic identity, (ii) that the saturated metric admits no
midpoints, and (iii) that it is therefore **not a geodesic metric space**
(`satDist_not_geodesic`). Since a complete Riemannian manifold is geodesic
(Hopf–Rinow), this is the formal sense of "non-Riemannian." The one empirical
premise — that human perception *is* such a readout — is isolated as a hypothesis,
never a theorem.

## 1. The result, precisely
Let `(X, d)` be a metric space and `a > 0`. Define the **saturating readout**
`f_a(t) = a(1 − e^{−t/a})` and the **saturated metric** `satDist_a = f_a ∘ d`.

- **KEY identity** (`key_identity'`): `f_a(x)·f_a(y) = a·(f_a(x)+f_a(y)−f_a(x+y))`,
  from `Real.exp_add` alone. The subadditivity defect is exactly `f_a(x)f_a(y)/a > 0`.
- **Strict subadditivity** (`strict_subadd`): for `x,y>0`, `f_a(x+y) < f_a(x)+f_a(y)`.
  Diminishing returns: summing JND steps overcounts the direct difference (X11 gray
  ramp, measured: Σ = 95.16 vs direct = 10.00, a 9.5× gap).
- **No midpoint** (`no_midpoint`): for `p ≠ q`, no `m` satisfies
  `satDist_a(p,m) = satDist_a(m,q) = satDist_a(p,q)/2`.
- **Not geodesic** (`satDist_not_geodesic`): with `IsGeodesicMetric` the textbook
  definition (every pair joined by an isometric segment), `¬ IsGeodesicMetric
  (satDist_a)` — because every geodesic metric is midpoint-convex
  (`IsGeodesicMetric.midpointConvex`), which `no_midpoint` refutes. Self-certifying:
  ordinary `ℝ` *is* geodesic (linear segment), `satDist` is not.
- **Not even a length metric** (`satDist_not_length_metric`): with `IsLengthMetric`
  the *intrinsic* condition (approximate midpoints for every `ε>0`),
  `¬ IsLengthMetric (satDist_a)` — `satDist` has no approximate midpoints, via the
  quantitative `no_eps_midpoint`. Strictly stronger than non-geodesic.

A Riemannian distance **is** a length metric *by definition* (the infimum of path
lengths is intrinsic), so `satDist_a` is the distance of no Riemannian structure.
**This is "non-Riemannian," now a theorem with no appeal to Hopf–Rinow** — the only
remaining classical input is the definitional identity "Riemannian distance = length
metric," far weaker than the geodesic completeness Hopf–Rinow would require.

## 2. The empirical premise (not formalized, by design)
The Lean proves the *geometry of the readout*; the bridge to human vision —
"perception **is** `f_a ∘ ΔE`" — is the empirical content of Bujack et al. plus a
per-context fit `â` (`Â ≈ 10` on the ΔE₀₀ anchor; `Â = 0.1537` fit from real
Sentinel-2/OlmoEarth embedding data, `world/EO_SCALE.md`). It is a hypothesis node,
refutable by data, never a theorem. Formal statement: *if* perception is a
saturating readout, *then* color space is non-geodesic (machine-checked), hence —
Hopf–Rinow — non-Riemannian.

## 3. The strangeness illustration
Define the *strangeness* of a color pair as `ΔE / f_a(ΔE)` (Riemannian vs readout
verdict). It is ≈1 for `ΔE ≲` a few JND (both metrics agree — where CIEDE is
valid) and grows without bound as `ΔE → ∞`, because `f_a → a`. Over the X11
catalogue (676 colors, vs magenta): least strange = magenta and its purple
neighbourhood (1.0×); most strange = the greens (15.7×) — magenta's opponent
complement ("−green"). The non-spectral hue and its complement bracket exactly the
span where the Riemannian ruler is most confidently wrong.

## 4. Contribution
A self-contained, axiom-clean Lean development of a published empirical result's
geometric core; a supporting mathlib lemma (`ConcaveOn`/`StrictConcaveOn.subadditive_of_map_zero`,
filling a real gap); and the upgrade of "non-Riemannian" from a hand-wave to
`satDist_not_geodesic`. Remaining: formalizing a general geodesic/length-space
typeclass + Hopf–Rinow would erase even the last classical footnote.

## References
- R. Bujack, E. Teti, J. Miller, E. Caffrey, T. L. Turton, *The non-Riemannian
  nature of perceptual color space*, PNAS 119(18), 2022.
- G. Sharma, W. Wu, E. N. Dalal, *The CIEDE2000 color-difference formula*, 2005.
- The mathlib community, *mathlib4*.
