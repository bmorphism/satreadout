# SatReadout — the non-Riemannian nature of perceptual color space, formalized

A machine-checked Lean 4 formalization (mathlib `v4.28.0`, CI-green) of the result
that **perceived color difference is a saturating, subadditive readout — not a
Riemannian/length metric** (cf. Bujack et al., *PNAS* 2022). Every claim below is
a compiled theorem; the only empirical input is stated explicitly and is *not*
formalized (by design).

## The one-line statement
**If** perceptual difference is the saturating readout `f_a(t)=a(1−e^{−t/a})`
applied to a local color metric (`hypothesis Bujack`), **then** the resulting
perceptual metric is **provably not even a length (intrinsic) metric** —
`satDist_not_length_metric : ¬ IsLengthMetric (satDist a)` (it has no approximate
midpoints). Since a Riemannian distance *is* a length metric **by definition**
(infimum of path lengths), this is the formal sense of **non-Riemannian** — with
**no appeal to Hopf–Rinow**. (The geodesic-level statement `satDist_not_geodesic`
and ordinary-`ℝ`-is-geodesic contrast are also machine-checked.)

## What is proved (all `\leanok`)
| file | content |
|---|---|
| `SatReadout.lean` | `f`, KEY identity `key_identity'`, `strict_subadd`, saturation `f_lt_asymptote`, the metric layer `satDist`/`satPseudoMetricSpace`, `no_midpoint`, `no_eps_midpoint`, `collinear_strict` |
| `SatReadoutGeodesic.lean` | `collinear_strict_wbtw` (in mathlib `Wbtw` terms), **`satDist_breaks_geodesic`** (no-midpoint obstruction) |
| `SatReadoutNotGeodesic.lean` | `IsGeodesicMetric`/`IsLengthMetric` defs + **`satDist_not_geodesic`** and **`satDist_not_length_metric`** — `satDist` is provably not geodesic and not even intrinsic (`ℝ` is geodesic; `satDist` isn't). The formal "non-Riemannian", Hopf–Rinow-free. |
| `AristotleQ1.lean` | `StrictConcaveOn.subadditive_of_map_zero` (the convexity route) |
| `AristotleQ2.lean` | `satPseudoMetricSpace_uniformity` (T4: uniformity agrees with ambient) |
| `AristotleQ3.lean` | the resident falsifier: the unquantified ε-bound is *disproved* (`no_eps_midpoint_without_quadratic_bound_is_false`) |
| `scratch/concave_subadd_pr.lean` | clean `ConcaveOn`/`StrictConcaveOn.subadditive_of_map_zero` — **mathlib PR candidate** (see `PR.md`) |
| `ToleranceIntent.lean` | the fitted saturation scale `Â` as a typed commit (`Â=0.1537` from real EO data) |

## The empirical premise (honesty)
The development proves the *geometry of the saturating readout*. The bridge to
human vision — "perception **is** `f_a`" — is the empirical claim of Bujack et al.
(2022) plus the per-context fit `Â` (`satfit`; `world/EO_SCALE.md`). It is a
`\begin{hypothesis}` node in `blueprint/strangeness.tex`, never a theorem.

## Worked illustration
`world/` — the strangeness map over the X11 catalogue (676 colors vs magenta):
least strange = magenta/purples (`1.0×`), most strange = the greens (`15.7×`,
magenta's opponent complement "−green"). See `world/x11_magenta_strangeness.html`.

## Verify
```
lake build SatReadout AristotleQ1 AristotleQ2 AristotleQ3 ToleranceIntent SatReadoutGeodesic
lake env lean axcheck.lean   # axiom gate: all on propext/Classical.choice/Quot.sound
```
CI (`proof-health.yml`) runs both on every push; the blueprint
(`blueprint/strangeness.tex`) is OpenGauss-`/autoformalize`-able.
