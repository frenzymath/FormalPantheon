import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronSubdivisionD918
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P2FullOuterFubiniD781
import Mathlib.Tactic.FinCases

/-!
# A three-tetrahedron cover of the native P2 outer carrier

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eqs. (6.12)-(6.13). The native coordinates are
(d,r,s), not the translated affine coordinates.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators

namespace PrimesRestrictedDigits

def sectionSixP2ClosedOuterD974 : Set (Fin 3 -> Real) := {x |
  16249 / 250000 ≤ x 0 ∧ 0 ≤ x 2 ∧ x 2 ≤ x 1 ∧
    2 * x 0 + x 1 + x 2 ≤ 180001 / 500000 ∧
    x 0 + 2 * x 1 ≤ 107501 / 500000}

def sectionSixP2VertexD974 : Fin 6 -> Fin 3 -> Rat :=
  ![![16249 / 250000, 0, 0],
    ![16249 / 250000, 75003 / 1000000, 0],
    ![16249 / 250000, 75003 / 1000000, 75003 / 1000000],
    ![29 / 200, 35001 / 1000000, 35001 / 1000000],
    ![84167 / 500000, 11667 / 500000, 0],
    ![180001 / 1000000, 0, 0]]

def sectionSixP2RootD974 : Fin 3 -> RationalTetrahedron :=
  let v := sectionSixP2VertexD974
  ![⟨![v 0, v 3, v 4, v 5]⟩, ⟨![v 0, v 1, v 3, v 4]⟩,
    ⟨![v 0, v 1, v 2, v 3]⟩]

private noncomputable def separatorP_D974 (x : Fin 3 -> Real) : Real :=
  11667 * (x 0 - 16249 / 250000) - 51669 * x 1 + 25001 * x 2

private noncomputable def separatorQ_D974 (x : Fin 3 -> Real) : Real :=
  35001 * (x 0 - 16249 / 250000) - 80004 * x 2

private noncomputable def weightsD974 (r : Fin 3) (x : Fin 3 -> Real) :
    Fin 4 -> Real :=
  ![![(180001 / 500000 - 2 * x 0 - x 1 - x 2) / (23001 / 100000),
      x 2 / (35001 / 1000000), (x 1 - x 2) / (11667 / 500000),
      separatorP_D974 x / (11667 * (23001 / 200000))],
    ![(107501 / 500000 - x 0 - 2 * x 1) / (75003 / 500000),
      -separatorP_D974 x / (51669 * (75003 / 1000000)),
      x 2 / (35001 / 1000000),
      separatorQ_D974 x / (35001 * (51669 / 500000))],
    ![(107501 / 500000 - x 0 - 2 * x 1) / (75003 / 500000),
      (x 1 - x 2) / (75003 / 1000000),
      -separatorQ_D974 x / (80004 * (75003 / 1000000)),
      (x 0 - 16249 / 250000) / (20001 / 250000)]] r

private theorem weights_sum_D974 (r : Fin 3) (x : Fin 3 -> Real) :
    ∑ i, weightsD974 r x i = 1 := by
  fin_cases r <;>
    norm_num [weightsD974, separatorP_D974, separatorQ_D974, Fin.sum_univ_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    ring

private theorem weights_point_D974 (r : Fin 3) (x : Fin 3 -> Real) :
    barycentricPoint3 (sectionSixP2RootD974 r).vertexReal (weightsD974 r x) = x := by
  funext j
  fin_cases r <;> fin_cases j <;>
    simp only [barycentricPoint3, barycentricCoordinate3, RationalTetrahedron.vertexReal,
      sectionSixP2RootD974, sectionSixP2VertexD974, weightsD974,
      separatorP_D974, separatorQ_D974, Fin.sum_univ_succ, Fin.sum_univ_zero,
      show (2 : Fin 6) = ⟨2, by decide⟩ from rfl,
      show (3 : Fin 6) = ⟨3, by decide⟩ from rfl,
      show (4 : Fin 6) = ⟨4, by decide⟩ from rfl,
      show (5 : Fin 6) = ⟨5, by decide⟩ from rfl,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    norm_num <;>
    ring_nf <;> rfl

theorem sectionSixP2FullOuter_subset_closed_D974 :
    {x : Fin 3 -> Real |
      ((x 0, x 1), x 2) ∈ sectionSixFirstLowCentralSmallI5P2FullOuter} ⊆
        sectionSixP2ClosedOuterD974 := by
  intro x hx
  change sectionSixThetaGap (1 / 1000000 : Real) ≤ x 0 ∧
    x 0 < sectionSixThetaOne (1 / 1000000 : Real) / 2 ∧
    0 < x 1 ∧ 0 < x 2 ∧ x 2 ≤ x 1 ∧
    2 * x 0 + x 1 + x 2 < sectionSixThetaOne (1 / 1000000 : Real) ∧
    2 * x 1 + x 0 < 16 / 25 - sectionSixThetaTwo (1 / 1000000 : Real) ∧
    0 ≤ (1 - sectionSixThetaTwo (1 / 1000000 : Real) -
      3 * x 0 - x 1 - x 2) / 2 at hx
  norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo] at hx
  rcases hx with ⟨hg, _, _, hs, hsr, hlow, hwall, _⟩
  exact ⟨hg, hs.le, hsr, hlow.le, by linarith⟩

theorem sectionSixP2ClosedOuter_subset_roots_D974 :
    sectionSixP2ClosedOuterD974 ⊆ ⋃ r, (sectionSixP2RootD974 r).region := by
  intro x hx
  obtain ⟨hd, hs, hsr, hlow, hwall⟩ := hx
  by_cases hp : 0 ≤ separatorP_D974 x
  · apply Set.mem_iUnion.2
    refine ⟨0, weightsD974 0 x, ?_, weights_sum_D974 0 x, weights_point_D974 0 x⟩
    intro i
    fin_cases i <;>
      simp only [weightsD974] <;>
      apply div_nonneg <;> norm_num <;> linarith
  · have hp' : separatorP_D974 x ≤ 0 := le_of_not_ge hp
    by_cases hq : 0 ≤ separatorQ_D974 x
    · apply Set.mem_iUnion.2
      refine ⟨1, weightsD974 1 x, ?_, weights_sum_D974 1 x, weights_point_D974 1 x⟩
      intro i
      fin_cases i <;>
        simp only [weightsD974] <;>
        apply div_nonneg <;> norm_num <;> linarith
    · have hq' : separatorQ_D974 x ≤ 0 := le_of_not_ge hq
      apply Set.mem_iUnion.2
      refine ⟨2, weightsD974 2 x, ?_, weights_sum_D974 2 x, weights_point_D974 2 x⟩
      intro i
      fin_cases i <;>
        simp only [weightsD974] <;>
        apply div_nonneg <;> norm_num <;> linarith

theorem sectionSixP2FullOuter_subset_roots_D974 :
    {x : Fin 3 -> Real |
      ((x 0, x 1), x 2) ∈ sectionSixFirstLowCentralSmallI5P2FullOuter} ⊆
        ⋃ r, (sectionSixP2RootD974 r).region :=
  sectionSixP2FullOuter_subset_closed_D974.trans sectionSixP2ClosedOuter_subset_roots_D974

end PrimesRestrictedDigits
