import SatReadout
import SatReadoutNotGeodesic
import SatReadoutAtlas

/-!
Adversarial audit of the parallel session's atlas/ensemble theorems.
Fresh kernel obligations: if any atlas theorem were vacuous or mis-stated these
fail to compile. (Same `−1` discipline as `correctness_audit.lean`.)
-/
open SatReadout

namespace AtlasAudit

-- (A) STRICTNESS IS REAL for a genuine two-chart blend (a=1, b=2 distinct, w=1/2),
-- not `≤` smuggled as `<`:
example : atlas2 1 2 (1/2) (1 + 1) < atlas2 1 2 (1/2) 1 + atlas2 1 2 (1/2) 1 :=
  atlas2_strict_subadd one_pos (by norm_num) (by norm_num) (by norm_num) one_pos one_pos

-- (B) FAITHFULNESS of the defect: the blend's shortfall really IS the weighted sum
-- of each chart's exact defect (instantiated a=1, b=2, w=1/2):
example (x y : ℝ) :
    atlas2 1 2 (1/2) x + atlas2 1 2 (1/2) y - atlas2 1 2 (1/2) (x + y)
      = (1/2) * (f 1 x * f 1 y / 1) + (1 - 1/2) * (f 2 x * f 2 y / 2) :=
  atlas2_defect one_pos (by norm_num)

-- (C) NON-VACUITY of the ensemble non-Riemannian result: it applies to a concrete
-- space (EuclideanSpace ℝ (Fin 2)) with concrete charts/weights and an active chart.
example : ¬ IsGeodesicMetric (X := EuclideanSpace ℝ (Fin 2))
            (satAtlasNDist (fun _ : Fin 2 => (1:ℝ)) (fun _ : Fin 2 => (1:ℝ))) :=
  satAtlasNDist_not_geodesic (fun _ => one_pos) (fun _ => zero_le_one)
    (k := (0 : Fin 2)) one_pos

-- (D) The "at least one active chart" guard is load-bearing: with it, the finite
-- blend is strictly subadditive on concrete numbers.
example : atlasN (fun _ : Fin 2 => (1:ℝ)) (fun _ : Fin 2 => (1:ℝ)) (1 + 1)
          < atlasN (fun _ : Fin 2 => (1:ℝ)) (fun _ : Fin 2 => (1:ℝ)) 1
            + atlasN (fun _ : Fin 2 => (1:ℝ)) (fun _ : Fin 2 => (1:ℝ)) 1 :=
  atlasN_strict_subadd (fun _ => one_pos) (fun _ => zero_le_one)
    (k := (0 : Fin 2)) one_pos one_pos one_pos

end AtlasAudit
