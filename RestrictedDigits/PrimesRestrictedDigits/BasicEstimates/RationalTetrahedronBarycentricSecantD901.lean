import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.NormNum
/-! # RationalTetrahedronBarycentricSecantD901 -/

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits

def barycentricCoordinate3
    (p : Fin 4 → Fin 3 → ℝ) (w : Fin 4 → ℝ) (j : Fin 3) : ℝ :=
  ∑ i, w i * p i j

theorem reciprocal_barycentric_secant_le
    {p : Fin 4 → Fin 3 → ℝ} {w : Fin 4 → ℝ} {j : Fin 3}
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hp : ∀ i, 0 < p i j) :
    (barycentricCoordinate3 p w j)⁻¹ ≤
      ∑ i, w i * (p i j)⁻¹ := by
  have hconv := (convexOn_zpow (-1 : Int)).map_sum_le
    (t := (Finset.univ : Finset (Fin 4)))
    (w := w) (p := fun i => p i j)
    (fun i hi => hw i) hwsum
    (fun i hi => Set.mem_Ioi.2 (hp i))
  simpa only [barycentricCoordinate3, smul_eq_mul, zpow_neg,
    zpow_one, inv_pow, pow_one] using hconv

theorem reciprocal_sq_barycentric_secant_le
    {p : Fin 4 → Fin 3 → ℝ} {w : Fin 4 → ℝ} {j : Fin 3}
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hp : ∀ i, 0 < p i j) :
    (barycentricCoordinate3 p w j)⁻¹ ^ 2 ≤
      ∑ i, w i * ((p i j)⁻¹) ^ 2 := by
  have hconv := (convexOn_zpow (-2 : Int)).map_sum_le
    (t := (Finset.univ : Finset (Fin 4)))
    (w := w) (p := fun i => p i j)
    (fun i hi => hw i) hwsum
    (fun i hi => Set.mem_Ioi.2 (hp i))
  simpa only [barycentricCoordinate3, smul_eq_mul, zpow_neg,
    zpow_ofNat, inv_pow, Nat.reduceAdd] using hconv

end PrimesRestrictedDigits
