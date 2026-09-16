import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6FixedDeltaRegularity
import PrimesRestrictedDigits.BasicEstimates.BuchstabTailEnvelope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# One fixed tail-cell payload for the low-below I6 integral

This file certifies one exact rational cell inside the weak I6 carrier at `delta = 1 /
1000000`. It is a local payload only; no global cover or I6 numerical cap is claimed here.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13) and region `R_4`.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

/-- A native nested rational cell lying in the tail branch of the fixed I6 carrier. -/
def sectionSixFirstLowBelowI6TailCell :
    Set (((Real × Real) × Real) × Real) :=
  ((Icc (1794 / 10000 : Real) (1796 / 10000) ×ˢ
      Icc (1789 / 10000 : Real) (1791 / 10000)) ×ˢ
    Icc (169 / 1000 : Real) (171 / 1000)) ×ˢ
    Icc (114 / 1000 : Real) (116 / 1000)

theorem sectionSixFirstLowBelowI6TailCell_measurable :
    MeasurableSet sectionSixFirstLowBelowI6TailCell := by
  exact ((measurableSet_Icc.prod measurableSet_Icc).prod
    measurableSet_Icc).prod measurableSet_Icc

theorem sectionSixFirstLowBelowI6TailCell_finite :
    volume sectionSixFirstLowBelowI6TailCell ≠ ⊤ := by
  exact (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
    isCompact_Icc).measure_ne_top

/-- The exact four-dimensional volume of the fixed I6 tail cell. -/
theorem sectionSixFirstLowBelowI6TailCell_volume_real :
    volume.real sectionSixFirstLowBelowI6TailCell =
      (1 : Real) / 6250000000000 := by
  rw [show sectionSixFirstLowBelowI6TailCell =
      ((Icc (1794 / 10000 : Real) (1796 / 10000) ×ˢ
        Icc (1789 / 10000 : Real) (1791 / 10000)) ×ˢ
      Icc (169 / 1000 : Real) (171 / 1000)) ×ˢ
      Icc (114 / 1000 : Real) (116 / 1000) by rfl]
  change (((volume.prod volume).prod volume).prod volume).real
      (((Icc (1794 / 10000 : Real) (1796 / 10000) ×ˢ
        Icc (1789 / 10000 : Real) (1791 / 10000)) ×ˢ
      Icc (169 / 1000 : Real) (171 / 1000)) ×ˢ
      Icc (114 / 1000 : Real) (116 / 1000)) = _
  rw [MeasureTheory.measureReal_prod_prod,
    MeasureTheory.measureReal_prod_prod,
    MeasureTheory.measureReal_prod_prod]
  repeat' rw [Real.volume_real_Icc_of_le] <;> norm_num

/-- Every point of the fixed cell lies in the weak exact I6 carrier. -/
theorem sectionSixFirstLowBelowI6TailCell_subset_delta6Region :
    sectionSixFirstLowBelowI6TailCell ⊆
      sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000) := by
  intro x hx
  rcases hx with ⟨⟨⟨⟨hu, huUpper⟩, ⟨hv, hvUpper⟩⟩,
    ⟨hw, hwUpper⟩⟩, ⟨ht, htUpper⟩⟩
  have hgap : sectionSixThetaGap (1 / 1000000 : Real) < x.2 := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo] at ht ⊢
    linarith
  have htw : x.2 <= x.1.2 := by linarith
  have hwv : x.1.2 <= x.1.1.2 := by linarith
  have hvu : x.1.1.2 <= x.1.1.1 := by linarith
  have hpair : x.1.1.1 + x.1.1.2 <
      sectionSixThetaOne (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaOne] at huUpper hvUpper ⊢
    linarith
  have htriple1 : sectionSixThetaTwo (1 / 1000000 : Real) <
      x.1.1.1 + x.1.1.2 + x.1.2 := by
    norm_num [sectionSixThetaTwo] at hu hv hw ⊢
    linarith
  have htriple2 : sectionSixThetaTwo (1 / 1000000 : Real) <
      x.1.1.1 + x.1.1.2 + x.2 := by
    norm_num [sectionSixThetaTwo] at hu hv ht ⊢
    linarith
  have htriple3 : sectionSixThetaTwo (1 / 1000000 : Real) <
      x.1.1.1 + x.1.2 + x.2 := by
    norm_num [sectionSixThetaTwo] at hu hw ht ⊢
    linarith
  have htriple4 : sectionSixThetaTwo (1 / 1000000 : Real) <
      x.1.1.2 + x.1.2 + x.2 := by
    norm_num [sectionSixThetaTwo] at hv hw ht ⊢
    linarith
  have hfull : sectionSixThetaTwo (1 / 1000000 : Real) <
      x.1.1.1 + x.1.1.2 + x.1.2 + x.2 := by
    norm_num [sectionSixThetaTwo] at hu hv hw ht ⊢
    linarith
  have hreflected : 1 - sectionSixThetaOne (1 / 1000000 : Real) <
      x.1.1.1 + x.1.1.2 + x.1.2 + x.2 := by
    norm_num [sectionSixThetaOne] at hu hv hw ht ⊢
    linarith
  refine ⟨hgap, htw, hwv, hvu, hpair, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; linarith [h.2, htriple1]
  · intro h; linarith [h.2, htriple2]
  · intro h; linarith [h.2, htriple3]
  · intro h; linarith [h.2, htriple4]
  · intro h; linarith [h.2, hfull]
  · intro h; linarith [h.2, hreflected]

/-- The fixed cell lies entirely on the weak Buchstab tail side. -/
theorem sectionSixFirstLowBelowI6TailCell_tail_wall
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstLowBelowI6TailCell) :
    4 * x.2 <= 1 - x.1.1.1 - x.1.1.2 - x.1.2 := by
  rcases hx with ⟨⟨⟨⟨hu, huUpper⟩, ⟨hv, hvUpper⟩⟩,
    ⟨hw, hwUpper⟩⟩, ⟨ht, htUpper⟩⟩
  norm_num at huUpper hvUpper hwUpper htUpper ⊢
  linarith

/-- The exact low-below kernel is at most `8100` throughout the fixed cell. -/
theorem sectionSixFirstLowBelowI6TailCell_kernel_le
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstLowBelowI6TailCell) :
    sectionSixFirstLowBelowQuadrupleKernel x <= 8100 := by
  rcases hx with ⟨⟨⟨⟨hu, huUpper⟩, ⟨hv, hvUpper⟩⟩,
    ⟨hw, hwUpper⟩⟩, ⟨ht, htUpper⟩⟩
  have huPos : 0 < x.1.1.1 := by linarith
  have hvPos : 0 < x.1.1.2 := by linarith
  have hwPos : 0 < x.1.2 := by linarith
  have htPos : 0 < x.2 := by linarith
  have harg : 3 <=
      (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
    rw [le_div_iff₀ htPos]
    linarith [sectionSixFirstLowBelowI6TailCell_tail_wall
      ⟨⟨⟨⟨hu, huUpper⟩, ⟨hv, hvUpper⟩⟩, ⟨hw, hwUpper⟩⟩,
        ⟨ht, htUpper⟩⟩]
  have htail := buchstabFunction_le_tailEnvelope harg
  have hden : 0 < x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat) := by
    positivity
  have hdenLower :
      (1794 / 10000 : Real) * (1789 / 10000) *
          (169 / 1000) * (114 / 1000) ^ (2 : Nat) <=
        x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ (2 : Nat) := by
    gcongr
  rw [sectionSixFirstLowBelowQuadrupleKernel]
  apply (div_le_iff₀ hden).2
  have hnum :
      buchstabFunction
          ((1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2) <=
        (564383 / 1000000 : Real) := htail
  have hrough :
      (564383 / 1000000 : Real) <= 8100 *
        ((1794 / 10000 : Real) * (1789 / 10000) *
          (169 / 1000) * (114 / 1000) ^ (2 : Nat)) := by
    norm_num
  nlinarith

/-- The contribution of the fixed tail cell is at most `81 / 62500000000`. -/
theorem sectionSixFirstLowBelowI6TailCell_integral_le :
    (∫ x in sectionSixFirstLowBelowI6TailCell,
      sectionSixFirstLowBelowQuadrupleKernel x) <=
      (81 : Real) / 62500000000 := by
  have hf : IntegrableOn sectionSixFirstLowBelowQuadrupleKernel
      sectionSixFirstLowBelowI6TailCell volume :=
    sectionSixFirstLowBelowQuadrupleKernel_integrable_delta5.mono_set
      sectionSixFirstLowBelowI6TailCell_subset_delta6Region
  let cells : Finset (Fin 1) := Finset.univ
  let cell : Fin 1 → Set (((Real × Real) × Real) × Real) :=
    fun _ => sectionSixFirstLowBelowI6TailCell
  let upper : Fin 1 → Real := fun _ => 8100
  have h := setIntegral_le_finset_measureReal_mul_of_cover volume cells
    sectionSixFirstLowBelowI6TailCell cell
    sectionSixFirstLowBelowQuadrupleKernel upper
    sectionSixFirstLowBelowI6TailCell_measurable
    (by intro i hi; exact sectionSixFirstLowBelowI6TailCell_measurable)
    (by intro i hi; exact sectionSixFirstLowBelowI6TailCell_finite) hf
    (by intro i hi; norm_num) (by
      intro x hx
      refine Set.mem_iUnion.2 ⟨(0 : Fin 1), ?_⟩
      refine Set.mem_iUnion.2 ⟨Finset.mem_univ _, ?_⟩
      simpa [cell] using hx)
    (by
      intro i hi x hx
      exact sectionSixFirstLowBelowI6TailCell_kernel_le hx.2)
  norm_num [cells, cell, upper,
    sectionSixFirstLowBelowI6TailCell_volume_real] at h ⊢
  exact h

end

end PrimesRestrictedDigits
