import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1WeightedSectionAreaBridgeD832
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece12MiddleOrTailEnvelopeD822
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1TransformedKernelRegularityD809
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1P1SelectedProvenanceD828
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1SelectedRowBridgeD838 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# selected P1 row/slab kernel-to-weighted-section adapter

This fixed-delta module covers zero-based Piece1 row index 1 (the second 1/256 d-slab). It
proves endpoint and scalar arithmetic and the weighted-section/area rewrite. The
four-dimensional Fubini identity and pointwise fiber envelope remain explicit theorem
hypotheses. There is no source, Jacobian, aggregate, or cap claim.
-/

def sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower : Real :=
  18571667 / 128000000

def sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper : Real :=
  9291667 / 64000000

def sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab : Set Real :=
  Set.Icc sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower
    sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper

def sectionSixFirstLowCentralSmallI5P1D838P1Row1Set : Set SectionSixP1AffineT :=
  sectionSixFirstLowCentralSmallI5P1D807Piece1 ∩
    {z | z.1.1.1 ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab}

def sectionSixFirstLowCentralSmallI5P1D838P1Row1Fiber (d : Real) : Real :=
  ∫ r in (0 : Real)..sectionSixFirstLowCentralSmallI5P1D807H d,
    ∫ s in (0 : Real)..
      min r (sectionSixFirstLowCentralSmallI5P1D807L d - r),
      ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
        (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
        sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)

def sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor : Real :=
  (70893 / 125000 : Real) /
      (sectionSixFirstLowCentralSmallI5P1D807Beta -
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper) *
    (1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
      1 / (sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper -
        sectionSixFirstLowCentralSmallI5P1D807Gap))

def sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight (d : Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor *
    sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower d

theorem sectionSixFirstLowCentralSmallI5P1D838_p1Row1_lower_eq_anchor :
    sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower =
      sectionSixFirstLowCentralSmallI5P1D828P1SelectedAnchor := by
  rw [sectionSixFirstLowCentralSmallI5P1D828_p1SelectedAnchor_value]
  norm_num [sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower]

theorem sectionSixFirstLowCentralSmallI5P1D838_p1Row1_subdivision_endpoints :
    sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower =
        sectionSixFirstLowCentralSmallI5P1D807Ds +
          (sectionSixFirstLowCentralSmallI5P1D807Dr -
            sectionSixFirstLowCentralSmallI5P1D807Ds) / 256 ∧
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper =
        sectionSixFirstLowCentralSmallI5P1D807Ds +
          2 * (sectionSixFirstLowCentralSmallI5P1D807Dr -
            sectionSixFirstLowCentralSmallI5P1D807Ds) / 256 := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
  constructor
  · rw [hDs, hDr]
    norm_num [sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower]
  · rw [hDs, hDr]
    norm_num [sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper]

theorem sectionSixFirstLowCentralSmallI5P1D838_p1Row1_endpoints :
    sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower <
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper ∧
      sectionSixFirstLowCentralSmallI5P1D807Ds ≤
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower ∧
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper ≤
        sectionSixFirstLowCentralSmallI5P1D807Dr := by
  constructor
  · norm_num [sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower,
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper]
  constructor
  · rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
    rw [hDs]
    norm_num [sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower]
  · rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
    rw [hDr]
    norm_num [sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper]

theorem sectionSixFirstLowCentralSmallI5P1D838_p1Row1_slab_subset_piece_interval
    {d : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab) :
    d ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807Ds
      sectionSixFirstLowCentralSmallI5P1D807Dr := by
  exact ⟨sectionSixFirstLowCentralSmallI5P1D838_p1Row1_endpoints.2.1.trans hd.1,
    hd.2.trans sectionSixFirstLowCentralSmallI5P1D838_p1Row1_endpoints.2.2⟩

theorem sectionSixFirstLowCentralSmallI5P1D838_p1Row1_area_eq_weighted
    {d : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab) :
    sectionSixFirstLowCentralSmallI5P1D831P1Case1WeightedSection
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower d =
      sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower d := by
  apply sectionSixFirstLowCentralSmallI5P1D832_p1Case1_weightedSection_eq_area
  · norm_num [sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower]
  · exact sectionSixFirstLowCentralSmallI5P1D838_p1Row1_slab_subset_piece_interval hd

theorem sectionSixFirstLowCentralSmallI5P1D838_p1Row1_factor_nonneg :
    0 ≤ sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor := by
  unfold sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
  have hbeta :
      0 < sectionSixFirstLowCentralSmallI5P1D807Beta -
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper := by
    rw [hBeta]
    norm_num [sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper]
  have hgap : 0 < sectionSixFirstLowCentralSmallI5P1D807Gap := by
    rw [hGap]
    norm_num
  have htail :
      0 ≤ 1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
        1 / (sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper -
          sectionSixFirstLowCentralSmallI5P1D807Gap) := by
    have hupper :
        0 < sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper -
          sectionSixFirstLowCentralSmallI5P1D807Gap := by
      rw [hGap]
      norm_num [sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper]
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le hgap (by
      rw [hGap]
      norm_num [sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper])
  have hcoef :
      0 ≤ (70893 / 125000 : Real) /
        (sectionSixFirstLowCentralSmallI5P1D807Beta -
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper) :=
    div_nonneg (by norm_num) hbeta.le
  exact mul_nonneg hcoef htail

theorem sectionSixFirstLowCentralSmallI5P1D838_p1Row1_factor_certificate :
    sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor *
      (20901274411415090963021081184957859172730724165545747937088826220595894014305156081 /
        9852343078046258963662659787589504772175787752396093440011826404545659812524851200000000 : Real) <
      (13 / 1000000 : Real) := by
  unfold sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
  rw [hBeta, hGap]
  norm_num [sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper]

/- The Fubini identity, row envelope, and outer area certificate are explicit
   hypotheses rather than project axioms. -/
theorem sectionSixFirstLowCentralSmallI5P1D838_p1Row1_kernel_to_area
    (hIter :
      (∫ z in sectionSixFirstLowCentralSmallI5P1D838P1Row1Set,
        sectionSixFirstLowCentralSmallI5P1D809Kernel z
        ∂(volume : Measure SectionSixP1AffineT)) =
        ∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Fiber d)
    (hFiber :
      ∀ d ∈ sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab,
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Fiber d ≤
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight d)
    (hFiberInt :
      IntervalIntegrable
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Fiber volume
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper)
    (hWeightInt :
      IntervalIntegrable
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight volume
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper)
    (hAreaIntegral :
      (∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
        sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower d) <
        (20901274411415090963021081184957859172730724165545747937088826220595894014305156081 /
          9852343078046258963662659787589504772175787752396093440011826404545659812524851200000000 : Real)) :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D838P1Row1Set,
      sectionSixFirstLowCentralSmallI5P1D809Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) <
      (13 / 1000000 : Real) := by
  rw [hIter]
  have hab :
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower ≤
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper :=
    sectionSixFirstLowCentralSmallI5P1D838_p1Row1_endpoints.1.le
  have hmono := intervalIntegral.integral_mono_on
    (μ := (volume : Measure Real)) hab hFiberInt hWeightInt hFiber
  have hweight :
      (∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight d) =
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor *
          (∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
              sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
            sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
              sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower d) := by
    unfold sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight
    rw [intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro d hd
    rw [sectionSixFirstLowCentralSmallI5P1D838_p1Row1_area_eq_weighted]
    simpa [sectionSixFirstLowCentralSmallI5P1D838P1Row1Slab,
      Set.uIcc_of_le hab] using hd
  calc
    (∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
        sectionSixFirstLowCentralSmallI5P1D838P1Row1Fiber d) ≤
        ∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Weight d := hmono
    _ = sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor *
        (∫ d in sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower..
            sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper,
          sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
            sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower d) := hweight
    _ < (13 / 1000000 : Real) := by
      have hfac : 0 <
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor := by
        unfold sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor
        rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
          ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
        rw [hBeta, hGap]
        norm_num [sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper]
      have hscaled := mul_lt_mul_of_pos_left hAreaIntegral hfac
      exact hscaled.trans_le
        (le_of_lt sectionSixFirstLowCentralSmallI5P1D838_p1Row1_factor_certificate)


end
end PrimesRestrictedDigits
