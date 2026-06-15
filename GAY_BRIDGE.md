# SatReadout ⋈ Gay.jl — one identity, three substrates

The saturating perceptual readout `f_A(t) = A·(1 − e^{−t/A})` is the shared
spine of the Lean proof system here and the color-metric program in
`bmorphism/Gay.jl`. This file is the contract that ties them: **the tolerance
Gay.jl's gates spend is the theorem SatReadout proves.**

## The shared identity (the only thing that runs)

    f(x) + f(y) − f(x+y) = f(x)·f(y)/A          (KEY)

- **Lean (∀ / 0-Witness):** `SatReadout.key_identity'` proves it for *all*
  `a, x, y : ℝ` from `Real.exp_add` + `ring` — no convexity, not even `0 < a`.
  `strict_subadd`, `no_midpoint`, `no_eps_midpoint` are its corollaries.
- **Julia / babashka (float / +1-Play):** `A·(1−exp(−d/A))` evaluated in IEEE-754.
  Cross-substrate residual of KEY is `≈ 2·ε_mach·A`, measured bit-for-bit equal
  in bb (Clojure) and Julia: **3.55e-15 at A=10, 3.9e-14 at A=150**.

## Gay.jl symbols carrying f_A

| symbol | file | A | role |
|---|---|---|---|
| `perceptual_diff_sat(c1,c2; A=10)` | `src/colorspaces.jl` | 10 | default large-Δ color metric |
| `GayLearnableColor._sat` / MDS stress | `GayLearnableColor.jl/src/` | 150 | subadditive embedding |
| `DiminishingReturnScale` / `diagnose` | same | fit | Scale-Protocol class #1, the −1 gate |

## The combine: derived tolerance, not tuned

KEY is *exact* over ℝ (Lean), so the only admissible slack at the float level is
exp() rounding. The certified ceiling is

    idtol = 64 · ε_mach · max(A, |expected|, 1)        ( ≈ 1.42e-13 at A=10 )

This replaces two pre-existing tuned constants — each ~10⁹× looser than the
theorem licenses, i.e. prose pretending to be derived:

- `test/test_nonriemannian_gate.jl`: `slop = 1e-9` → `64·ε·A` (claim "DERIVED,
  not tuned" is now literally true; every test point clears it with 80× margin).
- `GayLearnableColor.diagnose`: identity-match `1e-6` → `idtol`. (The
  collinearity *predicate* `|x+y−z| ≤ 1e-6·max(1,z)` stays — it is a structural
  threshold on the LOCAL kernel's additivity, not an instance of KEY.)

## Measured GF(3) of the bridge (read off, never assigned)

- **+1 Play** — KEY holds at float level in both A-regimes (residual ≤ 3.6e-15);
  bb ≡ julia, 0 semantic drift (same SPI discipline as the splitmix64 kernel).
- **0 Witness** — `key_identity'` is the ∀-closure of that observation; the
  axiom gate (`axcheck.lean`) confirms it rests on `propext / Classical.choice /
  Quot.sound` only.
- **−1 Coplay** — falsifier: an additive/Riemannian kernel `g(d)=d` has defect
  *exactly 0* → fails the strict gate (`0 ≯ tol`), and `raw CIEDE2000` is
  asserted to fail it in the test. A kernel outside the `f_A` family overshoots
  `idtol` and trips the gate. Both refutations are live, not decorative.

Σ ≡ 0 — and now falsifiable on both sides of the bridge: tighten the tolerance
to what Lean proves, and any drift in either substrate is a measured failure,
not a tuned-away one.
