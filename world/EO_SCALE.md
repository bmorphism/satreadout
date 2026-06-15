# EO-Nano discrimination scale — first real measurement (tick: seek on ea)

The Earth device works: OlmoEarth-Nano (dim 128) over `world://849VPHJW+22W`,
two Sentinel-2 windows (winter `S2C…20260113` 0.005% cloud, spring
`S2A…20260515` 0.06% cloud), embeddings in `Build/eo/san_bruno_q{1,2}.bin`.
`world/eo_trit.bb` reads them and runs the saturating readout → keep/maybe/discard.

## Measured cosine-distance scale (n=256 real distances)

| source | min | p50 | p90 | max |
|---|---|---|---|---|
| spatial within-scene (n=240) | 0.0000 | 0.0001 | 0.0007 | 0.0015 |
| temporal winter→spring (n=16) | 0.0589 | 0.0644 | 0.0654 | 0.0666 |

- **same-floor ≈ 0.0007** (within a homogeneous patch)
- **seasonal/temporal shift ≈ 0.066** (no structural change)
- temporal change is **~100× the spatial floor** — the embedding shifts coherently
  by season; spatial heterogeneity within the patch is negligible.
- the synthetic `A = 0.45` was **wrong by ~7×** — established, not assigned.

## GF(3) (measured)
- **+1** device → adapter → readout runs end-to-end on real EO data.
- ** 0** the temporal/spatial 100× ratio is real content (witness, preserved).
- **−1 (two, both quantified — the loop's live falsifiers):**
  1. **`Â` not yet fully establishable**: a stable patch yields only "same"
     labels ⇒ upper anchor ("clearly different" = structural change) unmeasured
     ⇒ cutpoints `b,s` unidentifiable (`satfit` starvation, lesson #2).
  2. **crop-targeting bug**: `download_bands` crops the scene's top-left 256px,
     ignoring lat/lon for the window (lat/lon only drives STAC search). The
     patch is MGRS `T10SEG` NW corner (likely ocean), not San Bruno. Distances
     real, label approximate.

## What establishes the upper anchor (next)
1. Fix `download_bands` to window at (lat,lon) in scene CRS (≈10 lines:
   reproject point → row/col → offset transform) so we scout the INTENDED patch.
2. Scout a structural-change location (cropland fallow→canopy, burn scar,
   reservoir) to populate the "different" band ⇒ fit `Â` + cutpoints (`satfit`).
3. Then `idtol = 64·ε·Â` is grounded in EO units, and the Lean4 intent's
   `commit` carries a per-substrate, data-fit `Â` (EO-space), per the
   magenta/Color lesson: no universal scale, one `Â` per context.

## ESTABLISHED (real device data, both −1's resolved)

Crop bug fixed (window centered at lat/lon). Heterogeneous Ocean Beach scout
(`ocean_beach.bin`, centered) gave within-scene distances spanning 0.0001→0.161
(ocean↔ocean → ocean↔urban) — the missing upper anchor. Fit:

| param | value (EO-Nano cos-dist units) | source |
|---|---|---|
| `Â` (clearly-different / saturation) | **0.1537** | ocean↔urban, p95 |
| `a` (same/maybe) | **0.0120** | 8× uniform-ocean floor (0.0015) |
| `b` (maybe/different) | **0.1011** | Otsu valley of the bimodal distribution |
| `idtol = 64·ε·Â` | **2.18e-15** | bridge bound at the fitted scale |

Regime sanity (all correct, MEASURED): uniform-ocean 0.0007→SAME ·
seasonal shift 0.066→MAYBE (ambiguous, not land-cover change) ·
ocean↔urban 0.154→DIFFERENT. Synthetic `A=0.45` → device-fit **0.1537**.

**Tolerance is established from a real device** (Sentinel-2/OlmoEarth = the
available discrimination device). Loop's remaining gate: EXPRESS this grounded
`Â` as a Lean4 Anoma/Geb intent (`ToleranceIntent.lean`, tick 2) — the `commit`
carries `Â=0.1537` (EO-space), per the magenta/Color lesson: one `Â` per context.
