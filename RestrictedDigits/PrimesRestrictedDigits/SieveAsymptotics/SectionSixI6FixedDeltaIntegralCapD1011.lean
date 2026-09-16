import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6LabelReplayD1011T0
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6LabelReplayD1011T1
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6LabelReplayD1011T2
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6LabelReplayD1011F00000
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6LabelReplayD1011F00010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6LabelReplayD1011T00010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6LabelReplayD1011T10010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6LabelReplayD1011T11010
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6LabelReplayD1011T11110
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6LabelReplayD1011T11111
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6NativeLabelCandidateCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6FixedDeltaTransfer

/-!
# Uniform I6 cap from the closed chamber certificates

The ten native targets cover the original fixed-delta region. Overlap is allowed because the
kernel is nonnegative on every target. Source: `MAYNARD-PRD-PUBLISHED`, p.144, Eq. (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

open SectionSixI6CertificateD1011

def i6D1011Labels : Fin 10 -> i6D691Label :=
  ![T0.label, T1.label, T2.label, F00000.label, F00010.label,
    T00010.label, T10010.label, T11010.label, T11110.label, T11111.label]

def i6D1011Caps : Fin 10 -> Rat :=
  ![T0.total, T1.total, T2.total, F00000.total, F00010.total,
    T00010.total, T10010.total, T11010.total, T11110.total, T11111.total]

theorem i6D1011_candidateLabels_subset_range (label : i6D691Label)
    (hlabel : label ∈ i6D731CandidateLabels) :
    ∃ i : Fin 10, i6D1011Labels i = label := by
  classical
  simp only [i6D731CandidateLabels, Finset.mem_insert, Finset.mem_singleton] at hlabel
  rcases hlabel with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩

theorem i6D1011NativeTarget_integral_le (i : Fin 10) :
    (∫ x in i6D691NativeTarget (i6D1011Labels i),
      sectionSixFirstLowBelowQuadrupleKernel x) ≤ (i6D1011Caps i : Real) := by
  fin_cases i
  · simpa [i6D1011Labels, i6D1011Caps] using T0.native_integral_le
  · simpa [i6D1011Labels, i6D1011Caps] using T1.native_integral_le
  · simpa [i6D1011Labels, i6D1011Caps] using T2.native_integral_le
  · simpa [i6D1011Labels, i6D1011Caps] using F00000.native_integral_le
  · simpa [i6D1011Labels, i6D1011Caps] using F00010.native_integral_le
  · simpa [i6D1011Labels, i6D1011Caps] using T00010.native_integral_le
  · simpa [i6D1011Labels, i6D1011Caps] using T10010.native_integral_le
  · simpa [i6D1011Labels, i6D1011Caps] using T11010.native_integral_le
  · simpa [i6D1011Labels, i6D1011Caps] using T11110.native_integral_le
  · simpa [i6D1011Labels, i6D1011Caps] using T11111.native_integral_le

theorem i6D1011_cap_sum :
    ∑ i, i6D1011Caps i = (6661907277539 / 100000000000000 : Rat) := by
  decide +kernel

theorem i6D1011FixedDelta_integral_le :
    (∫ x in sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real),
      sectionSixFirstLowBelowQuadrupleKernel x) ≤
        (6661907277539 / 100000000000000 : Real) := by
  let target := fun i : Fin 10 => i6D691NativeTarget (i6D1011Labels i)
  have hcover : sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real) ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin 10)), target i := by
    intro x hx
    obtain ⟨label, hlabel⟩ := Set.mem_iUnion.mp
      (sectionSixFirstLowBelowI6_candidateLabel_exactRegion_subset_iUnion_nativeTarget hx)
    obtain ⟨i, hi⟩ := i6D1011_candidateLabels_subset_range label.1 label.2
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
      ⟨Finset.mem_univ i, by simpa only [target, hi] using hlabel⟩⟩
  have hbound := setIntegral_le_finset_setIntegral_of_cover volume
    (Finset.univ : Finset (Fin 10))
    (sectionSixFirstLowBelowQuadrupleRegion (1 / 1000000 : Real))
    target sectionSixFirstLowBelowQuadrupleKernel
    sectionSixFirstLowBelowQuadrupleRegion_delta5_measurable
    (fun i _ => i6D691NativeTarget_measurable (i6D1011Labels i))
    (fun _ _ => sectionSixFirstLowBelowQuadrupleKernel_integrable_delta5.mono_set
      (fun _ hx => hx.1))
    (fun _ _ _ hx => sectionSixFirstLowBelowQuadrupleKernel_nonneg_delta5 hx.1) hcover
  calc
    _ ≤ ∑ i, ∫ x in target i, sectionSixFirstLowBelowQuadrupleKernel x := hbound
    _ ≤ ∑ i, (i6D1011Caps i : Real) :=
      Finset.sum_le_sum (fun i _ => i6D1011NativeTarget_integral_le i)
    _ = (6661907277539 / 100000000000000 : Real) := by
      rw [← Rat.cast_sum, i6D1011_cap_sum]
      norm_num

theorem sectionSixFirstLowBelowQuadrupleIntegral_lt_D1011 {epsilon : Real}
    (hepsilonUpper : epsilon ≤ 1 / 1000000) :
    sectionSixFirstLowBelowQuadrupleIntegral epsilon < (167 : Real) / 2500 :=
  ((sectionSixFirstLowBelowQuadrupleIntegral_le_delta5 hepsilonUpper).trans
    i6D1011FixedDelta_integral_le).trans_lt (by norm_num)

end PrimesRestrictedDigits
