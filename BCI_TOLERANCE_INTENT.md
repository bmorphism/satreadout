# Tolerance from BCI, as a Lean4 Anoma/Geb intent

Goal (loop invariant): the saturation tolerance `A` of the SatReadout readout
`f_A(t)=A(1−e^{−t/A})` — and hence the certified gate bound `idtol = 64·ε·A`
(see GAY_BRIDGE.md) — must be **established from BCI discrimination data**, not
hardcoded, and the establishment must be **expressible as a Lean4 intent in the
Anoma/Geb sense** (intent = morphism in a bicartesian-closed category, with a
nullify / commit / constraint structure, GF(3)-conserved).

## The chain

    BCI device  ──(same/maybe/different)──►  ternary trits  t ∈ GF(3)
        │                                         │  trit-0 = "maybe" = JND deadzone
        ▼                                         ▼
    stimulus pair (c1,c2)  ──CIEDE2000──►  ΔE      satfit.jl ordinal-logit fit
                                                  (θ = [logA, a, logΔ, logs])
                                                   │   R1 identifiability cert
                                                   ▼
                                          Â  (saturation scale, ΔE00 units)
                                                   │
                                                   ▼
                                  idtol = 64·ε·Â   +   SatReadout gates @ Â
                                  (certified tolerance, now data-grounded)

`satfit.jl` is pillar 1, already built and proven (synthetic observer: Â=10.0 ≡
A*, 3 inits, FD-grad 4e-9). A BCI device replaces ONLY the synthetic observer
(satfit.jl:70–96): real `(stimulus-pair → response-trit)` trials in, same fit out.

## The intent (pillar 3, Anoma/Geb shape)

```
intent ToleranceFromBCI {
  owner   : observer (the calibrating subject)
  nullify : DefaultTolerance   -- A = 10 hardcoded  (a +1 ungrounded assertion)
  commit  : GroundedTolerance Â -- fit from this subject's discrimination trits
  constraint :
      0 < Â                                  -- positivity (SatReadout needs it)
    ∧ identifiable(fit)                       -- R1: Â-spread among converged < 0.5
    ∧ idtol = 64·ε·Â                          -- the bridge bound at the fitted scale
    ∧ ∀ gates ∈ SatReadout, gates hold @ Â    -- strict_subadd, no_eps_midpoint, …
}
compileIntent : ToleranceFromBCI → Geb.Morphism   -- bicartesian-closed (Geb)
```

GF(3) of the intent (MEASURED, read off the solve, never assigned):
- **+1 Play** — `commit` asserts a grounded `Â` (a tolerance now backed by data).
- ** 0 Witness** — the BCI trit stream is the witness; the maybe-band closes the
  JND relation (no orphan threshold).
- **−1 Coplay** — the `satfit` solver is the falsifier: non-identifiable fit
  (Â-spread ≥ 0.5, or ΔNLL·n distinguishing the readout family) ⇒ REJECT the
  commit; the default is NOT nullified. This leg can fail and must be reported.

Σ ≡ 0 ⇔ a healthy calibration; drift names the pathology (ungrounded A, dangling
JND, contradictory cutpoints).

## Lean4 intent type (DRAFT — not yet lake-built; tick 2)

```lean
import SatReadout
namespace ToleranceIntent
open SatReadout

/-- A tolerance grounded in discrimination data: the saturation scale `A`
    together with the certificate that it is a usable SatReadout tolerance. -/
structure GroundedTolerance where
  A          : ℝ
  hA         : 0 < A
  /-- identifiability witness, supplied by the fit (R1): the converged Â-spread
      is below the gauge-resolution bound. Kept as a hypothesis Lean carries; the
      numeric fit lives in satfit.jl (the −1 solver). -/
  identifiable : Prop
  hid        : identifiable
  /-- derived gate bound at this scale -/
  idtol      : ℝ := 64 * (2 : ℝ)⁻¹ ^ 52 * A   -- 64·ε·A (ε = 2^-52)

/-- The commit is well-typed iff the SatReadout gates instantiate at A. -/
theorem commit_sound (g : GroundedTolerance) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    f g.A (x + y) < f g.A x + f g.A y :=
  strict_subadd g.hA hx hy
end ToleranceIntent
```

The intent's `constraint` is exactly `commit_sound` (+ positivity + identifiable):
a Lean proof that the fitted `Â` yields the non-Riemannian gate. "Established"
= this structure is inhabited by a value whose `A` came from a device fit and
whose `identifiable` witness the fit discharged.

## Tick plan (loop: "until tolerance CAN BE established")

- [x] tick 1 — orient 3 pillars; data contract; this spine; GF(3) reading.
- [ ] tick 2 — `ToleranceIntent.lean` lake-builds green against SatReadout v4.28.
- [ ] tick 3 — run `satfit` on synthetic-BCI trits; emit `Â`, `idtol`, R1 cert;
      wire `Â` into the intent's `commit`.
- [ ] tick 4 — `compileIntent → Geb.Morphism` (Common Lisp / geb-agda); Juvix
      intent DSL; measured GF(3) Σ≡0; define the device plug-in point.

## Standing −1 (do not hide)

No live BCI device is connected (only EntropyLoop QRNG). Everything is validated
on the synthetic observer / recordable trial format; the pipeline is
**device-ready**, not yet **device-calibrated**. "Can be established" is reached
when the Lean4 intent is built, the fit runs to an identifiable Â, the Geb
expression compiles, and the only missing input is a subject at the device — a
falsifiable, honest stopping point, not a claim that a brain has calibrated it.
