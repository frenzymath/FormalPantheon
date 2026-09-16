import PrimesRestrictedDigits.BasicEstimates.PositivePartAffineReciprocalCapD967
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963
import Mathlib.Tactic.FinCases

/-!
# Concrete affine kernels for the two-ceiling P0 profile

The exact identity preserves total inverse at zero denominators. Vertex positivity is required
only for the subsequent regularity results. Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq.
(6.12).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

def sectionSixP0CoordinateD968 (j : Fin 3) : RationalAffine 3 :=
  ⟨0, fun k => if k = j then 1 else 0⟩

def sectionSixP0ComplementD968 : RationalAffine 3 := ⟨1, fun _ => -1⟩

def sectionSixP0BaselineNumeratorD968 : RationalAffine 3 :=
  ⟨-281 / 500, ![0, 0, 140500 / 16249]⟩

def sectionSixP0ExcessNumeratorD968 : RationalAffine 3 :=
  ⟨-643 / 125000, ![643 / 125000, 643 / 125000, 13503 / 500000]⟩

def sectionSixP0BaselineDenominatorD968 : Fin 4 -> RationalAffine 3 :=
  ![sectionSixP0CoordinateD968 0, sectionSixP0CoordinateD968 1,
    sectionSixP0CoordinateD968 2, sectionSixP0CoordinateD968 2]

def sectionSixP0ExcessDenominatorD968 : Fin 5 -> RationalAffine 3 :=
  ![sectionSixP0CoordinateD968 0, sectionSixP0CoordinateD968 1,
    sectionSixP0CoordinateD968 2, sectionSixP0CoordinateD968 2, sectionSixP0ComplementD968]

theorem sectionSixP0CoordinateD968_eval (j : Fin 3) (x : Fin 3 -> Real) :
    (sectionSixP0CoordinateD968 j).evalReal x = x j := by
  have hcast (k : Fin 3) : ((if k = j then 1 else 0 : Rat) : Real) =
      if k = j then 1 else 0 := by
    split_ifs <;> norm_num
  simp [sectionSixP0CoordinateD968, RationalAffine.evalReal, hcast, ite_mul]

theorem sectionSixP0ComplementD968_eval (x : Fin 3 -> Real) :
    sectionSixP0ComplementD968.evalReal x = 1 - x 0 - x 1 - x 2 := by
  simp [sectionSixP0ComplementD968, RationalAffine.evalReal, Fin.sum_univ_succ]
  ring

theorem sectionSixP0BaselineNumeratorD968_eval (x : Fin 3 -> Real) :
    sectionSixP0BaselineNumeratorD968.evalReal x =
      (281 / 500) / (16249 / 250000) * (x 2 - 16249 / 250000) := by
  norm_num [sectionSixP0BaselineNumeratorD968, RationalAffine.evalReal,
    Fin.sum_univ_succ]
  ring

theorem sectionSixP0ExcessNumeratorD968_eval (x : Fin 3 -> Real) :
    sectionSixP0ExcessNumeratorD968.evalReal x =
      (643 / 500000) * (17 * x 2 - 4 * (1 - x 0 - x 1 - x 2)) := by
  norm_num [sectionSixP0ExcessNumeratorD968, RationalAffine.evalReal,
    Fin.sum_univ_succ]
  ring

theorem sectionSixP0TwoCeilingProfile_eq_affineKernels_D968
    (x : Fin 3 -> Real) (hw : (16249 / 250000 : Real) ≤ x 2) :
    sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963 ((x 0, x 1), x 2) =
      positivePartAffineReciprocalKernel_D967 sectionSixP0BaselineNumeratorD968
        sectionSixP0BaselineDenominatorD968 x +
      positivePartAffineReciprocalKernel_D967 sectionSixP0ExcessNumeratorD968
        sectionSixP0ExcessDenominatorD968 x := by
  have hn : 0 ≤ (281 / 500 : Real) / (16249 / 250000) *
      (x 2 - 16249 / 250000) := mul_nonneg (by norm_num) (sub_nonneg.mpr hw)
  have hmax :
      max 0 ((643 / 500000 : Real) * (17 * x 2 - 4 * (1 - x 0 - x 1 - x 2))) =
        (643 / 500000) * max 0 (17 * x 2 - 4 * (1 - x 0 - x 1 - x 2)) := by
    rw [mul_max_of_nonneg _ _ (by norm_num : (0 : Real) ≤ 643 / 500000), mul_zero]
  unfold positivePartAffineReciprocalKernel_D967
  rw [sectionSixP0BaselineNumeratorD968_eval, sectionSixP0ExcessNumeratorD968_eval,
    max_eq_right hn, hmax]
  simp only [sectionSixP0BaselineDenominatorD968, sectionSixP0ExcessDenominatorD968,
    Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.prod_univ_zero,
    sectionSixP0CoordinateD968_eval, sectionSixP0ComplementD968_eval, mul_one]
  unfold sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963
    sectionSixFirstLowCentralSmallI5P0BaselineD963 sectionSixFirstLowCentralSmallI5P0ExcessD963
  simp only [div_eq_mul_inv, mul_inv_rev, pow_two]
  ring

theorem sectionSixP0_denominators_positive_D968 (T : RationalTetrahedron)
    (hv : ∀ i, 0 < T.vertexReal i 0 ∧ 0 < T.vertexReal i 1 ∧
      (16249 / 250000 : Real) ≤ T.vertexReal i 2 ∧
      0 < 1 - T.vertexReal i 0 - T.vertexReal i 1 - T.vertexReal i 2) :
    (∀ k i, 0 < (sectionSixP0BaselineDenominatorD968 k).evalReal (T.vertexReal i)) ∧
      (∀ k i, 0 < (sectionSixP0ExcessDenominatorD968 k).evalReal (T.vertexReal i)) := by
  have hw (i : Fin 4) : 0 < T.vertexReal i 2 :=
    lt_of_lt_of_le (by norm_num) (hv i).2.2.1
  constructor
  · intro k i
    fin_cases k <;>
      simp only [sectionSixP0BaselineDenominatorD968, Matrix.cons_val_zero',
        Matrix.cons_val_succ', sectionSixP0CoordinateD968_eval]
    · exact (hv i).1
    · exact (hv i).2.1
    · exact hw i
    · exact hw i
  · intro k i
    fin_cases k <;>
      simp only [sectionSixP0ExcessDenominatorD968, Matrix.cons_val_zero',
        Matrix.cons_val_succ', sectionSixP0CoordinateD968_eval,
        sectionSixP0ComplementD968_eval]
    · exact (hv i).1
    · exact (hv i).2.1
    · exact hw i
    · exact hw i
    · exact (hv i).2.2.2

private theorem lower_wall_D968 (T : RationalTetrahedron)
    (hv : ∀ i, (16249 / 250000 : Real) ≤ T.vertexReal i 2)
    {x : Fin 3 -> Real} (hx : x ∈ T.region) : (16249 / 250000 : Real) ≤ x 2 := by
  have h := T.affine_eval_ge_of_vertices (sectionSixP0CoordinateD968 2)
    (bound := (16249 / 250000 : Real)) (by simpa only [sectionSixP0CoordinateD968_eval] using hv)
    x hx
  simpa only [sectionSixP0CoordinateD968_eval] using h

theorem sectionSixP0_profile_nonneg_D968 (T : RationalTetrahedron)
    (hv : ∀ i, 0 < T.vertexReal i 0 ∧ 0 < T.vertexReal i 1 ∧
      (16249 / 250000 : Real) ≤ T.vertexReal i 2 ∧
      0 < 1 - T.vertexReal i 0 - T.vertexReal i 1 - T.vertexReal i 2)
    {x : Fin 3 -> Real} (hx : x ∈ T.region) :
    0 ≤ sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963 ((x 0, x 1), x 2) := by
  obtain ⟨hbase, hexcess⟩ := sectionSixP0_denominators_positive_D968 T hv
  rw [sectionSixP0TwoCeilingProfile_eq_affineKernels_D968 x
    (lower_wall_D968 T (fun i => (hv i).2.2.1) hx)]
  exact add_nonneg
    (T.positivePartAffineReciprocal_nonneg_D967 _ _ hbase hx)
    (T.positivePartAffineReciprocal_nonneg_D967 _ _ hexcess hx)

theorem sectionSixP0_profile_integrableOn_D968 (T : RationalTetrahedron)
    (hv : ∀ i, 0 < T.vertexReal i 0 ∧ 0 < T.vertexReal i 1 ∧
      (16249 / 250000 : Real) ≤ T.vertexReal i 2 ∧
      0 < 1 - T.vertexReal i 0 - T.vertexReal i 1 - T.vertexReal i 2) :
    IntegrableOn (fun x : Fin 3 -> Real =>
      sectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963 ((x 0, x 1), x 2))
      T.region volume := by
  obtain ⟨hbase, hexcess⟩ := sectionSixP0_denominators_positive_D968 T hv
  apply ((T.positivePartAffineReciprocal_integrableOn_D967 _ _ hbase).add
    (T.positivePartAffineReciprocal_integrableOn_D967 _ _ hexcess)).congr_fun
  · intro x hx
    exact (sectionSixP0TwoCeilingProfile_eq_affineKernels_D968 x
      (lower_wall_D968 T (fun i => (hv i).2.2.1) hx)).symm
  · exact T.region_measurable_D924

end PrimesRestrictedDigits
