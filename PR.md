# mathlib PR package — `concave + map_zero ⇒ subadditive`

**Status:** lemma pair clean and verified on Lean `v4.28.0`
(`scratch/concave_subadd_pr.lean`, 0 warnings). Remaining to open the PR is a
human action (fork push + click) plus mathlib-CI verification against current
master — see "Caveats". I cannot open the PR; this is the package to do it.

## Title
`feat(Analysis/Convex): concave functions vanishing at 0 are subadditive`

## What & why
mathlib has `Convex_subadditive_le` (subadditive ⇒ convex sublevel sets) but **no
forward lemma** `concave + f 0 = 0 ⇒ subadditive`. `Analysis/Subadditive` is the
Fekete *sequence* theory only. (Verified absent via DeepWiki + Loogle, 2026.) This
is a small, frequently-wanted gap; it is the engine behind saturating perceptual
metrics (`f_a(t)=a(1−e^{−t/a})`).

## The lemmas (verified)
```lean
theorem ConcaveOn.subadditive_of_map_zero
    {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f) (h0 : f 0 = 0)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : f (x + y) ≤ f x + f y
theorem StrictConcaveOn.subadditive_of_map_zero
    {f : ℝ → ℝ} (hf : StrictConcaveOn ℝ (Set.Ici 0) f) (h0 : f 0 = 0)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : f (x + y) < f x + f y
```
Proof: `x = (y/(x+y))·0 + (x/(x+y))·(x+y)` is a (nontrivial) convex combination,
so (strict) concavity at `0, x+y` with `f 0 = 0` gives `(x/(x+y))·f(x+y) (<)≤ f x`;
symmetric for `y`; add and clear `(x+y)/(x+y)=1`. ~20 lines each, no `nlinarith`
sledgehammer.

## Target file
`Mathlib/Analysis/Convex/Function.lean` (alongside the `ConcaveOn` API), or
`Mathlib/Analysis/Convex/Slope.lean`. Namespace the names under `ConcaveOn` /
`StrictConcaveOn` (as written).

## Caveats / remaining −1 (honest)
1. Verified on **v4.28**, not master. Master uses `module` / `public section`
   syntax (post-v4.28); the statements/proofs port unchanged but the file header
   may differ — mathlib CI is the real check.
2. Reviewers may ask to **generalize `ℝ` to a `LinearOrderedField 𝕜`** on a
   suitable convex set. The `ℝ`-on-`[0,∞)` version is the clean, mergeable
   first pass; generalization is reviewer-iteration.
3. Add the symmetric/`Ici a` variants only if requested.

## To open (human step)
Fork `leanprover-community/mathlib4`, branch e.g.
`feat/concave-subadditive`, drop both lemmas into the target file, run
`lake build` against master locally or let CI run, open the PR with the body
above. The compare URL will be
`github.com/leanprover-community/mathlib4/compare/master...<fork>:<branch>`.
