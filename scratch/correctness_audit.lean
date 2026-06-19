import SatReadout
import SatReadoutGeodesic

/-!
Adversarial correctness audit of the non-Riemannian color formalization.
Each `example` is a *new* obligation the kernel must discharge — if any were
vacuous or mis-stated, these would fail to compile.
-/
open SatReadout

namespace CorrectnessAudit

-- (A) NON-VACUITY OF THE BASE SPACE.
-- satDist_breaks_geodesic quantifies over strict-convex normed ℝ-spaces. If that
-- class were empty (or had no distinct points) the theorem would say nothing.
-- EuclideanSpace ℝ (Fin 2) is a concrete inhabitant with distinct points:
example : ∃ p q : EuclideanSpace ℝ (Fin 2), p ≠ q := exists_pair_ne _

-- (B) THE THEOREM APPLIES CONCRETELY (a = 1) — instance resolution succeeds, so the
-- hypotheses are genuinely satisfiable, not vacuously assumed:
example (p q : EuclideanSpace ℝ (Fin 2)) (hpq : p ≠ q) :
    (∃ m, dist p m = dist p q / 2 ∧ dist m q = dist p q / 2) ∧
    ¬ ∃ m, satDist (1:ℝ) p m = satDist 1 p q / 2 ∧ satDist 1 m q = satDist 1 p q / 2 :=
  satDist_breaks_geodesic one_pos hpq

-- (C) NON-TRIVIALITY IS INTERNAL. The statement asserts a midpoint EXISTS for the
-- base metric AND DOES NOT for satDist. A Riemannian/additive metric would satisfy
-- the first and FAIL the second — so the conjunction cannot be vacuously true.
-- Witness that the first conjunct is real content: the base midpoint exists.
example (p q : EuclideanSpace ℝ (Fin 2)) (hpq : p ≠ q) :
    ∃ m, dist p m = dist p q / 2 ∧ dist m q = dist p q / 2 :=
  (satDist_breaks_geodesic one_pos hpq).1

-- (D) STRICTNESS IS REAL, not `≤` smuggled as `<`, on concrete numbers:
example : f 1 (1 + 1) < f 1 1 + f 1 1 := strict_subadd one_pos one_pos one_pos

-- (E) SATURATION IS REAL: the readout never reaches its asymptote.
example (t : ℝ) : f 1 t < 1 := f_lt_asymptote one_pos

-- (F) AXIOM HYGIENE on every load-bearing theorem (must be the standard triple):
#print axioms SatReadout.key_identity'
#print axioms SatReadout.strict_subadd
#print axioms SatReadout.no_midpoint
#print axioms SatReadout.satDist_breaks_geodesic
#print axioms SatReadout.collinear_strict_wbtw

end CorrectnessAudit
