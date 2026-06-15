/-
ToleranceIntent: the SatReadout tolerance as a Lean4 Anoma/Geb intent.

The loop's closing gate — "tolerance established from a device, EXPRESSIBLE in
lean4 intents of anoma/geb." An Anoma intent is a morphism in a bicartesian-closed
category (Geb) with a nullify / commit / constraint structure. Here:

  nullify    : the ungrounded default scale (A = 10, a +1 ungrounded assertion)
  commit     : a GroundedTolerance — the saturation scale Â FIT FROM A DEVICE
  constraint : the non-Riemannian SatReadout gate instantiates at Â (commit_sound)

Per the magenta/Color lesson, there is NO universal A: each substrate commits its
own Â in its own gauge. The EO instance commits Â = 0.1537, established from real
Sentinel-2/OlmoEarth discrimination data (world/EO_SCALE.md).
-/
import SatReadout

namespace ToleranceIntent
open SatReadout

/-- The intent's `commit`: a tolerance grounded in real discrimination data — the
saturation scale `A` together with the proof `0 < A` that makes it a usable
SatReadout tolerance. This is the base⋉fiber type: `A` is the colorimetric/EO
coordinate scale (base), `hA` the well-typedness the fit discharges (fiber). -/
structure GroundedTolerance where
  A  : ℝ
  hA : 0 < A

namespace GroundedTolerance

/-- The bridge bound at the fitted scale: `idtol = 64·ε·A` (ε = 2⁻⁵²). -/
noncomputable def idtol (g : GroundedTolerance) : ℝ := 64 / 2 ^ 52 * g.A

/-- The `constraint`, part 1: the strict non-Riemannian gate holds at this `A`
(equality = the Riemannian signature, never attained). This is `strict_subadd`
specialised to the committed scale. -/
theorem commit_subadditive (g : GroundedTolerance) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    f g.A (x + y) < f g.A x + f g.A y :=
  strict_subadd g.hA hx hy

/-- The `constraint`, part 2: saturation — the readout never exceeds the committed
asymptote `A` (diminishing returns). -/
theorem commit_saturates (g : GroundedTolerance) (t : ℝ) : f g.A t < g.A :=
  f_lt_asymptote g.hA

end GroundedTolerance

/-- The Anoma/Geb intent: nullify the ungrounded default, commit the data-fit
tolerance. `compileIntent : ToleranceIntent → Geb.Morphism` would send this to a
morphism in the bicartesian-closed category; here we carry the typed contract. -/
structure Intent where
  nullify : ℝ                  -- the ungrounded default scale (e.g. 10)
  commit  : GroundedTolerance  -- the device-fit Â (with its soundness proof)

/-- The EO-substrate instance: `Â = 0.1537`, established from Sentinel-2/OlmoEarth
(ocean↔urban p95; world/EO_SCALE.md). The commit is well-typed because `0 < Â`. -/
noncomputable def eoIntent : Intent where
  nullify := 10
  commit  := { A := 0.1537, hA := by norm_num }

/-- The intent's constraint is satisfied: the SatReadout gate instantiates at the
device-fit Â. This is the loop's closing fact — tolerance established AND expressed. -/
theorem eoIntent_sound {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    f eoIntent.commit.A (x + y) < f eoIntent.commit.A x + f eoIntent.commit.A y :=
  eoIntent.commit.commit_subadditive hx hy

theorem eoIntent_saturates (t : ℝ) : f eoIntent.commit.A t < eoIntent.commit.A :=
  eoIntent.commit.commit_saturates t

end ToleranceIntent
