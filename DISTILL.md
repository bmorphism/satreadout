# Distillation — SatReadout, end to end

One line: **a saturating non-Riemannian perceptual readout `f_A(t)=A(1−e^{−t/A})`,
Lean-certified, whose tolerance is one identity across substrates and is
established per-context from a real discrimination device — done on Earth
(Sentinel-2/OlmoEarth, `Â=0.1537`) and expressed as a lake-built, axiom-clean
Lean4 Anoma/Geb intent.**

## The spine (one identity)

    KEY:  f x · f y = a·(f x + f y − f(x+y))          ( = the subadditivity defect )

Pure `exp_add`+`ring`, holds ∀a. Every gate (strict subadditivity, no-midpoint,
no-ε-midpoint, collinear strictness) is its corollary. Non-Riemannian: equality
(additivity along geodesics) never attained ⇒ excluded from large-difference use.

## What stands, by epistemic status

**PROVEN (Lean v4.28, pushed, CI-enforced — not re-run this session):**
- SatReadout gates + KEY identity; axioms = `propext/Classical.choice/Quot.sound`
  only, 6/6 theorems, enforced by `proof-health.yml`. `81a3929`,`85f629d`.

**MEASURED this session (real, falsifiable, reproduced):**
- *Bridge*: `idtol = 64·ε·A` replaces tuned `1e-9`/`1e-6`; KEY float-residual
  `3.55e-15 < idtol` (bb-measured this session; Julia test edited, not re-run).
  CI green (run `27571358117`). `fbff48b` (satreadout, PUSHED) + `e3c403a`
  (Gay.jl `gay`, PUSHED).
- *world://gerbils*: two `color://` kernels (gay:// avalanche identity vs perceptual
  saturating); saturation collapse (gerbils.bb selftest): raw ΔE-spread **12.3** →
  f-spread **0.0067**; Σ≡0 GREEN. `world/gerbils.bb`, `fbff48b`.
- *Color*: colorimetric conversion round-trips to ~1e-7 (invertible, H¹=0); the
  percept (magenta = non-spectral, learned categorical perception) carries H¹≠0.
  Color = gauge section; percept = the orbit; `f_A`'s non-invertibility = the spread.
- *Earth = the device* (`seek on ea`): OlmoEarth-Nano (dim 128) over `world://OLC`,
  Sentinel-2; `world/eo_trit.bb` (selftest GREEN). **Tolerance ESTABLISHED from real
  device data**: `Â=0.1537` (ocean↔urban p95), `a=0.0120`, `b=0.1011` (Otsu valley),
  `idtol=2.18e-15`. Regimes all correct: floor 0.0007→SAME, seasonal 0.066→MAYBE,
  ocean↔urban 0.154→DIFFERENT. Synthetic `A=0.45` falsified. `4f8aa78`,`4f2c9b1`.

**DONE (loop closing gate):**
- `ToleranceIntent.lean` lake-builds GREEN (0 warnings); `eoIntent` commits the
  device-fit `Â=0.1537` with `strict_subadd`/`f_lt_asymptote` as proven
  constraints; `eoIntent_sound` axiom-clean (std triple; axcheck 7/7). `1de4e79`.
  ⇒ tolerance ESTABLISHED from a device AND EXPRESSED as a Lean4 Anoma/Geb intent.

**NEW — Riemannian-exclusion no longer prose (`SatReadoutGeodesic.lean`):**
- The 2026-06-10 note "mathlib has no length/geodesic theory ⇒ exclusion stays
  prose" is SUPERSEDED — `dist_add_dist_eq_iff`, `dist_left/right_midpoint`,
  `Wbtw` are present in our pinned mathlib v4.28.0 (verified against source, no
  bump). Two theorems, lake-build GREEN (0 warn), axiom-clean (std triple, 9/9):
  `collinear_strict_wbtw` (strict super-additivity over `Wbtw`-between points) and
  `satDist_breaks_geodesic` (base has a midpoint, `satDist` has none — `f∘dist`
  destroys the geodesic structure). Confirmed via DeepWiki: `concave⇒subadditive`
  still absent from mathlib (PR stands); Geb morphism machinery present
  (`compileIntent` realizable). (introduced this commit — see `git log`.)

**NEW — atlas/ensemble readouts keep the gate (`SatReadoutAtlas.lean`):**
- The MLX color-space experiments suggested chart mixtures: raw RGB/logit/OKLab,
  smooth-vs-caustic routing, and convex ensembles. The Lean contribution isolates
  the invariant: `atlas2 a b w t = w·f_a(t) + (1-w)·f_b(t)` has exact weighted
  defect, derivative `1` at `0`, bounded weighted asymptote, strict subadditivity,
  a `satAtlasDist` pseudometric, and collinear strictness. The finite form
  `atlasN = Σᵢ wᵢ·f_{aᵢ}` has derivative equal to total weight at `0`, bounded
  weighted asymptote, scalar and distance-level raw upper envelopes for
  normalized weights, weighted quadratic lower envelopes near zero, and the same
  weighted-defect, subadditivity, pseudometric, collinear strictness,
  no-midpoint, and not-geodesic theorems whenever the weights are nonnegative and
  at least one chart is active. Hence normalized local/ensemble readouts stay
  first-order raw but do **not** recover Riemannian additivity or metric
  segments; the non-Riemannian gate is stable under the useful atlas operations.
  Lake-build GREEN and axiom gate unchanged
  (`propext/Classical.choice/Quot.sound`) this session.

**DEFERRED (named, not hidden):**
- The literal `compileIntent : Intent → Geb.Morphism` functor into a Geb
  formalization (CL/Agda/Idris) + Juvix DSL is a doc-comment, not run — the
  intent is expressed *in Lean4* in the Anoma/Geb shape; the Geb compiler pass
  itself is not executed here.
- No live BCI device existed; Earth/Sentinel-2 was the honest substitute device.
- Commits `2c67bea`,`4f8aa78`,`4f2c9b1`,`970aff7`,`1de4e79` are **local, unpushed**.

## Content-H¹ preserved (genuine disagreement, never forced to 0)
- `fp(100000) ≠ a45b…` = .topos-miniature vs Gay.jl fingerprint convention (traced).
- EO crop label approximate: `san_bruno_q*` are MGRS-NW (ocean), not San Bruno
  (crop bug, fixed mid-arc for `ocean_beach.bin`).
- gerbil fur RGB = keeper-eye approximations.
- **`A` is per-context, no universal value**: color `A≈10`, EO-Nano `Â≈0.1537` —
  different substrates, different gauge orbit. This is the magenta/Color lesson and
  *why* the tolerance must be an intent (per-observer `commit`), not a constant.

## GF(3) of the whole arc (measured)
+1 generated (bridge, gerbils, adapter, EO fit) · 0 witnessed (duality, regime
sanity, the per-context gauge) · −1 falsified-and-survived (Riemannian kernel fails
the gate; synthetic A=0.45 refuted by device data; crop bug caught and fixed).
Σ≡0 — and the two open items above keep it honest, not closed.
