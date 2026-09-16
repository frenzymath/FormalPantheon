import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronSubdivisionD918
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6SevenTailFiberGeometryD996

/-!
# The exact ordered-pair root for I6

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p.144, Eq. (6.13). The closed four-wall base is
one rational tetrahedron. Native targets are contained in it; no converse projection or
numerical bound is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators

namespace PrimesRestrictedDigits

def i6D999OrderedPairRoot : RationalTetrahedron :=
  ⟨![![32498 / 500000, 32498 / 500000, 32498 / 500000],
    ![147503 / 500000, 32498 / 500000, 32498 / 500000],
    ![180001 / 1000000, 180001 / 1000000, 32498 / 500000],
    ![180001 / 1000000, 180001 / 1000000, 180001 / 1000000]]⟩

theorem i6D999_mem_orderedPairRoot_iff (x : Fin 3 -> Real) :
    x ∈ i6D999OrderedPairRoot.region ↔
      (32498 / 500000 : Real) <= x 2 ∧ x 2 <= x 1 ∧ x 1 <= x 0 ∧
        x 0 + x 1 <= (180001 / 500000 : Real) := by
  constructor
  · rintro ⟨q, hq, hsum, hpoint⟩
    have hx0 := congrFun hpoint 0
    have hx1 := congrFun hpoint 1
    have hx2 := congrFun hpoint 2
    norm_num [barycentricPoint3, barycentricCoordinate3, i6D999OrderedPairRoot,
      RationalTetrahedron.vertexReal, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail] at hx0 hx1 hx2
    rw [Fin.sum_univ_four] at hsum
    have hq0 := hq 0
    have hq1 := hq 1
    have hq2 := hq 2
    have hq3 := hq 3
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  · rintro ⟨hgap, hwv, hvu, hpair⟩
    let q : Fin 4 -> Real :=
      ![(180001 / 500000 - x 0 - x 1) / (23001 / 100000),
        (x 0 - x 1) / (23001 / 100000),
        2 * (x 1 - x 2) / (23001 / 100000),
        2 * (x 2 - 32498 / 500000) / (23001 / 100000)]
    refine ⟨q, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> dsimp [q] <;> apply div_nonneg <;> norm_num <;> linarith
    · norm_num [q, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.vecHead, Matrix.vecTail]
      ring
    · funext j
      fin_cases j <;>
        norm_num [barycentricPoint3, barycentricCoordinate3, i6D999OrderedPairRoot,
          RationalTetrahedron.vertexReal, q, Fin.sum_univ_four,
          Matrix.cons_val_two, Matrix.cons_val_three,
          Matrix.vecHead, Matrix.vecTail] <;> ring_nf
      all_goals rfl

theorem i6D999NativeTarget_projection_mem (label : i6D691Label)
    {z : (((Real × Real) × Real) × Real)}
    (hz : z ∈ i6D691NativeTarget label) :
    ![z.1.1.1, z.1.1.2, z.1.2] ∈ i6D999OrderedPairRoot.region := by
  apply (i6D999_mem_orderedPairRoot_iff _).2
  change (32498 / 500000 : Real) <= z.1.2 ∧ z.1.2 <= z.1.1.2 ∧
    z.1.1.2 <= z.1.1.1 ∧ z.1.1.1 + z.1.1.2 <= (180001 / 500000 : Real)
  have hregion := hz.1
  change sectionSixThetaGap (1 / 1000000 : Real) < z.2 ∧
    z.2 <= z.1.2 ∧ z.1.2 <= z.1.1.2 ∧ z.1.1.2 <= z.1.1.1 ∧
    z.1.1.1 + z.1.1.2 < sectionSixThetaOne (1 / 1000000 : Real) ∧ _ at hregion
  rcases hregion with ⟨hgap, htw, hwv, hvu, hpair, _⟩
  norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo] at hgap hpair
  norm_num
  exact ⟨hgap.le.trans htw, hwv, hvu, hpair.le⟩

theorem i6D999TailBase_subset_root (rho : Bool) :
    {x : Fin 3 -> Real | ((x 0, x 1), x 2) ∈ i6D996TailBase rho} ⊆
      i6D999OrderedPairRoot.region := by
  intro x hx
  apply (i6D999_mem_orderedPairRoot_iff x).2
  have hz : ((x 0, x 1), x 2) ∈ i6D996TailRootBase := hx.1
  have hgap := hz.2.1
  have hpair := hx.2.2.2.1
  norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo] at hgap hpair
  norm_num
  exact ⟨hgap, hx.2.1, hx.2.2.1, hpair⟩

end PrimesRestrictedDigits
