import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberAffineKernelD1006
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronClosedClipIntegralD1003

/-!
# Integral replay for an I6 affine endpoint chamber

The reciprocal endpoint identity is used on the target only. Whole-leaf caps use the global
positive-part extension and checked denominator signs. Source: `MAYNARD-PRD-PUBLISHED`,
Section 6, p.144, Eq. (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

theorem i6D1006Chamber_kernel_eq (label : i6D691Label) (l h : Fin 7)
    {x : Fin 3 -> Real} (hx : x ∈ i6D1005Chamber label l h) :
    positivePartAffineReciprocalKernel_D967
      (i6D1006Numerator label.2.1 l h) (i6D1006Denominators label.2.1 l h) x =
    (i6D1006BranchCap label.2.1 : Real) / (x 0 * x 1 * x 2) *
      (1 / sectionSixFirstLowBelowI6CellLower (x 0) (x 1) (x 2) label.2.1 label.2.2 -
        1 / sectionSixFirstLowBelowI6CellUpper (x 0) (x 1) (x 2) label.2.1 label.2.2) := by
  let L := sectionSixFirstLowBelowI6CellLower (x 0) (x 1) (x 2) label.2.1 label.2.2
  let H := sectionSixFirstLowBelowI6CellUpper (x 0) (x 1) (x 2) label.2.1 label.2.2
  have hend := i6D1005Chamber_endpoints label l h hx
  have hordered : L ≤ H := (i6D1005Chamber_subset_orderedOuter label l h hx).2
  have hL : 0 < L := by
    have hfloor : sectionSixThetaGap (1 / 1000000) ≤ L := le_max_left _ _
    exact (show (0 : Real) < sectionSixThetaGap (1 / 1000000) by
      norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]).trans_le hfloor
  have hH : 0 < H := hL.trans_le hordered
  have hroot := (i6D999_mem_orderedPairRoot_iff x).mp hx.2.2.1
  have hw : 0 < x 2 := lt_of_lt_of_le (by norm_num) hroot.1
  have hv : 0 < x 1 := hw.trans_le hroot.2.1
  have hu : 0 < x 0 := hv.trans_le hroot.2.2.1
  have hC : 0 ≤ (i6D1006BranchCap label.2.1 : Real) := by
    generalize label.2.1 = b
    fin_cases b <;> norm_num [i6D1006BranchCap]
  have hn : 0 ≤ (i6D1006BranchCap label.2.1 : Real) * (H - L) :=
    mul_nonneg hC (sub_nonneg.mpr hordered)
  unfold positivePartAffineReciprocalKernel_D967
  rw [i6D1006Numerator_eval, hend.1, hend.2, max_eq_right hn]
  simp only [i6D1006Denominators, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, sectionSixP0CoordinateD968_eval,
    hend.1, hend.2, mul_one]
  change (i6D1006BranchCap label.2.1 : Real) * (H - L) *
    ((x 0)⁻¹ * ((x 1)⁻¹ * ((x 2)⁻¹ * (L⁻¹ * H⁻¹)))) =
      (i6D1006BranchCap label.2.1 : Real) / (x 0 * x 1 * x 2) * (1 / L - 1 / H)
  field_simp [hu.ne', hv.ne', hw.ne', hL.ne', hH.ne']

theorem i6D1006Chamber_integral_le_replay (label : i6D691Label) (l h : Fin 7)
    (tree : RationalTetraClipD1002 16 Rat)
    (hv : tree.coverValid (i6D1005ChamberWalls label l h)
      (i6D1006LeafValid label.2.1 l h) i6D999OrderedPairRoot = true) :
    (∫ x in i6D1005Chamber label l h,
      (i6D1006BranchCap label.2.1 : Real) / (x 0 * x 1 * x 2) *
        (1 / sectionSixFirstLowBelowI6CellLower (x 0) (x 1) (x 2) label.2.1 label.2.2 -
          1 / sectionSixFirstLowBelowI6CellUpper (x 0) (x 1) (x 2) label.2.1 label.2.2)) ≤
    (((tree.retainedLeaves (i6D1005ChamberWalls label l h) i6D999OrderedPairRoot).map
      (fun leaf => leaf.1.volumeRat * leaf.2)).sum : Rat) := by
  calc
    _ = ∫ x in i6D1005Chamber label l h,
        positivePartAffineReciprocalKernel_D967
          (i6D1006Numerator label.2.1 l h) (i6D1006Denominators label.2.1 l h) x :=
      setIntegral_congr_fun (i6D1005Chamber_measurable label l h)
        (fun _ hx => (i6D1006Chamber_kernel_eq label l h hx).symm)
    _ ≤ _ := tree.setIntegral_le_leafWeightSum_D1003
      (i6D1005ChamberWalls label l h) (i6D1006LeafValid label.2.1 l h)
      (fun _ q => q) i6D999OrderedPairRoot (i6D1005Chamber label l h) _
      (i6D1005Chamber_measurable label l h) (fun _ hx => hx.2.2.1)
      (fun _ hx => hx.2.2.2) hv
      (i6D1006Leaf_integrable label.2.1 l h)
      (fun T q hq _ hx => i6D1006Leaf_nonneg label.2.1 l h T q hq hx)
      (i6D1006Leaf_integral_le label.2.1 l h)

end PrimesRestrictedDigits
