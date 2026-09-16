import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronSubdivisionD918
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0TwoCeilingProfileD963

/-!
# A three-tetrahedron cover of the native P0 base

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12). The explicit barycentric cover is
project-derived; it asserts no numerical integral bound.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators

namespace PrimesRestrictedDigits

def sectionSixP0VertexD971 : Fin 6 -> Fin 3 -> Rat :=
  ![![212499 / 1000000, 212499 / 1000000, 16249 / 250000],
    ![212499 / 1000000, 212499 / 1000000, 147503 / 1000000],
    ![16 / 75, 16 / 75, 16249 / 250000],
    ![16 / 75, 16 / 75, 220003 / 1500000],
    ![147503 / 500000, 16249 / 125000, 16249 / 250000],
    ![147503 / 500000, 172497 / 1000000, 16249 / 250000]]

def sectionSixP0RootD971 : Fin 3 -> RationalTetrahedron :=
  let v := sectionSixP0VertexD971
  ![⟨![v 1, v 0, v 4, v 5]⟩, ⟨![v 1, v 0, v 2, v 5]⟩,
    ⟨![v 1, v 3, v 2, v 5]⟩]

private noncomputable def separatorP_D971 (x : Fin 3 -> Real) : Real :=
  (8501 / 200000) * (x 0 - x 1) -
    (122509 / 1000000) * (x 0 + x 1 - 212499 / 500000)

private noncomputable def separatorQ_D971 (x : Fin 3 -> Real) : Real :=
  (2503 / 500000) * (x 2 - 16249 / 250000) -
    (82507 / 500000) * (16 / 25 - x 0 - 2 * x 1)

private noncomputable def weightsD971 (r : Fin 3) (x : Fin 3 -> Real) :
    Fin 4 -> Real :=
  ![![2 * (x 2 - 16249 / 250000) / (82507 / 500000),
      2 * (180001 / 500000 - x 0 - x 2) / (82507 / 500000),
      separatorP_D971 x / ((82507 / 500000) * (8501 / 200000)),
      (x 0 + x 1 - 212499 / 500000) / (8501 / 200000)],
    ![2 * (x 2 - 16249 / 250000) / (82507 / 500000),
      -2 * separatorQ_D971 x / ((2503 / 500000) * (82507 / 500000)),
      -3 * separatorP_D971 x / ((2503 / 500000) * (122509 / 1000000)),
      (x 0 - x 1) / (122509 / 1000000)],
    ![2 * (16 / 25 - x 0 - 2 * x 1) / (2503 / 500000),
      separatorQ_D971 x / ((2503 / 500000) * (122509 / 1500000)),
      (180001 / 500000 - x 0 - x 2) / (122509 / 1500000),
      (x 0 - x 1) / (122509 / 1000000)]] r

private theorem weights_sum_D971 (r : Fin 3) (x : Fin 3 -> Real) :
    ∑ i, weightsD971 r x i = 1 := by
  fin_cases r <;>
    norm_num [weightsD971, separatorP_D971, separatorQ_D971, Fin.sum_univ_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    ring

private theorem weights_point_D971 (r : Fin 3) (x : Fin 3 -> Real) :
    barycentricPoint3 (sectionSixP0RootD971 r).vertexReal (weightsD971 r x) = x := by
  funext j
  fin_cases r <;> fin_cases j <;>
    simp only [barycentricPoint3, barycentricCoordinate3, RationalTetrahedron.vertexReal,
      sectionSixP0RootD971, sectionSixP0VertexD971, weightsD971,
      separatorP_D971, separatorQ_D971, Fin.sum_univ_succ, Fin.sum_univ_zero,
      show (2 : Fin 6) = ⟨2, by decide⟩ from rfl,
      show (3 : Fin 6) = ⟨3, by decide⟩ from rfl,
      show (4 : Fin 6) = ⟨4, by decide⟩ from rfl,
      show (5 : Fin 6) = ⟨5, by decide⟩ from rfl,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    norm_num <;>
    ring_nf <;> rfl

theorem sectionSixP0Base_subset_roots_D971 :
    {x : Fin 3 -> Real |
      ((x 0, x 1), x 2) ∈ sectionSixFirstLowCentralSmallI5P0RefinedBase} ⊆
        ⋃ r, (sectionSixP0RootD971 r).region := by
  intro x hx
  obtain ⟨hvu, huv, hu2v, hw, huw⟩ :=
    (sectionSixFirstLowCentralSmallI5P0RefinedBase_iff_fiveWalls_D963 _).1 hx
  by_cases hp : 0 ≤ separatorP_D971 x
  · apply Set.mem_iUnion.2
    refine ⟨0, weightsD971 0 x, ?_, weights_sum_D971 0 x, weights_point_D971 0 x⟩
    intro i
    fin_cases i <;>
      simp only [weightsD971] <;>
      apply div_nonneg <;> norm_num <;> linarith
  · have hp' : separatorP_D971 x ≤ 0 := le_of_not_ge hp
    by_cases hq : 0 ≤ separatorQ_D971 x
    · apply Set.mem_iUnion.2
      refine ⟨2, weightsD971 2 x, ?_, weights_sum_D971 2 x, weights_point_D971 2 x⟩
      intro i
      fin_cases i <;>
        simp only [weightsD971] <;>
        apply div_nonneg <;> norm_num <;> linarith
    · have hq' : separatorQ_D971 x ≤ 0 := le_of_not_ge hq
      apply Set.mem_iUnion.2
      refine ⟨1, weightsD971 1 x, ?_, weights_sum_D971 1 x, weights_point_D971 1 x⟩
      intro i
      fin_cases i <;>
        simp only [weightsD971] <;>
        apply div_nonneg <;> norm_num <;> linarith

end PrimesRestrictedDigits
