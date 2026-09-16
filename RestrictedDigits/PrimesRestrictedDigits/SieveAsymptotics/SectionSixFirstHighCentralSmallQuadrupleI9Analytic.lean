import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleI9FiberReduction
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstHighCentralSmallQuadrupleI9Analytic -/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstHighCentralSmallI9TailConstant : Real :=
  564383 / 1000000

def sectionSixFirstHighCentralSmallI9MiddleConstant : Real :=
  70893 / 125000

def sectionSixFirstHighCentralSmallI9MiddleExcess : Real :=
  sectionSixFirstHighCentralSmallI9MiddleConstant -
    sectionSixFirstHighCentralSmallI9TailConstant

def sectionSixFirstHighCentralSmallI9W (u : Real) : Real :=
  (1 - u) / 6

def sectionSixFirstHighCentralSmallI9W3 (u v : Real) : Real :=
  (1 - u - v) / 5

def sectionSixFirstHighCentralSmallI9T (u v w : Real) : Real :=
  (1 - u - v - w) / 4

def sectionSixFirstHighCentralSmallI9MiddleBox :
    Set (((Real × Real) × Real) × Real) :=
  {x | x.1.1.1 ∈ Icc sectionSixFirstHighCentralSmallI9Beta
      sectionSixFirstHighCentralSmallI9Seam ∧
    sectionSixFirstHighCentralSmallI9W x.1.1.1 ≤ x.1.1.2 ∧
      x.1.1.2 ≤ sectionSixFirstHighCentralSmallI9VUpper x.1.1.1 ∧
    sectionSixFirstHighCentralSmallI9W3 x.1.1.1 x.1.1.2 ≤ x.1.2 ∧
      x.1.2 ≤ x.1.1.2 ∧
    sectionSixFirstHighCentralSmallI9T x.1.1.1 x.1.1.2 x.1.2 ≤ x.2 ∧
      x.2 ≤ x.1.2}

def sectionSixFirstHighCentralSmallI9USet : Set Real :=
  Icc sectionSixFirstHighCentralSmallI9Beta
    sectionSixFirstHighCentralSmallI9Seam

def sectionSixFirstHighCentralSmallI9UVSet : Set (Real × Real) :=
  closedIccFiberCell sectionSixFirstHighCentralSmallI9USet
    sectionSixFirstHighCentralSmallI9W
    (fun u => sectionSixFirstHighCentralSmallI9VUpper u)

def sectionSixFirstHighCentralSmallI9UVWSet :
    Set ((Real × Real) × Real) :=
  closedIccFiberCell sectionSixFirstHighCentralSmallI9UVSet
    (fun z => sectionSixFirstHighCentralSmallI9W3 z.1 z.2)
    (fun z => z.2)

def sectionSixFirstHighCentralSmallI9NestedBox :
    Set (((Real × Real) × Real) × Real) :=
  closedIccFiberCell sectionSixFirstHighCentralSmallI9UVWSet
    (fun z => sectionSixFirstHighCentralSmallI9T z.1.1 z.1.2 z.2)
    (fun z => z.2)

theorem sectionSixFirstHighCentralSmallI9_nestedBox_eq_middleBox :
    sectionSixFirstHighCentralSmallI9NestedBox =
      sectionSixFirstHighCentralSmallI9MiddleBox := by
  ext x
  simp only [sectionSixFirstHighCentralSmallI9NestedBox,
    sectionSixFirstHighCentralSmallI9UVWSet,
    sectionSixFirstHighCentralSmallI9UVSet,
    sectionSixFirstHighCentralSmallI9USet,
    closedIccFiberCell,
    sectionSixFirstHighCentralSmallI9MiddleBox]
  constructor
  · rintro ⟨⟨⟨hu, hv⟩, hw⟩, ht⟩
    exact ⟨hu, hv.1, hv.2, hw.1, hw.2, ht.1, ht.2⟩
  · rintro ⟨hu, hvL, hvU, hwL, hwU, htL, htU⟩
    exact ⟨⟨⟨hu, ⟨hvL, hvU⟩⟩, ⟨hwL, hwU⟩⟩, ⟨htL, htU⟩⟩

def sectionSixFirstHighCentralSmallI9TailOuterF (u : Real) : Real :=
  Real.log (sectionSixFirstHighCentralSmallI9VUpper u /
      sectionSixFirstHighCentralSmallI9Gamma) ^ 2 /
      (2 * sectionSixFirstHighCentralSmallI9Gamma) +
    1 / sectionSixFirstHighCentralSmallI9Gamma -
      1 / sectionSixFirstHighCentralSmallI9VUpper u -
    Real.log (sectionSixFirstHighCentralSmallI9VUpper u /
      sectionSixFirstHighCentralSmallI9Gamma) /
      sectionSixFirstHighCentralSmallI9Gamma

def sectionSixFirstHighCentralSmallI9TailOuterMajorant (u : Real) : Real :=
  sectionSixFirstHighCentralSmallI9TailConstant / u *
    sectionSixFirstHighCentralSmallI9TailOuterF u

theorem sectionSixFirstHighCentralSmallI9_constants_numeric :
    0 < sectionSixFirstHighCentralSmallI9TailConstant ∧
    0 < sectionSixFirstHighCentralSmallI9MiddleExcess ∧
    sectionSixFirstHighCentralSmallI9MiddleExcess = 2761 / 1000000 := by
  constructor
  · norm_num [sectionSixFirstHighCentralSmallI9TailConstant]
  constructor
  · norm_num [sectionSixFirstHighCentralSmallI9MiddleExcess,
      sectionSixFirstHighCentralSmallI9MiddleConstant,
      sectionSixFirstHighCentralSmallI9TailConstant]
  · norm_num [sectionSixFirstHighCentralSmallI9MiddleExcess,
      sectionSixFirstHighCentralSmallI9MiddleConstant,
      sectionSixFirstHighCentralSmallI9TailConstant]

theorem sectionSixFirstHighCentralSmallI9_middleBox_measurable :
    MeasurableSet sectionSixFirstHighCentralSmallI9MiddleBox := by
  unfold sectionSixFirstHighCentralSmallI9MiddleBox
  simp only [sectionSixFirstHighCentralSmallI9W,
    sectionSixFirstHighCentralSmallI9VUpper,
    sectionSixFirstHighCentralSmallI9W3,
    sectionSixFirstHighCentralSmallI9T]
  measurability

theorem sectionSixFirstHighCentralSmallI9_middleBox_subset
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstHighCentralSmallI9MiddleCarrier) :
    x ∈ sectionSixFirstHighCentralSmallI9MiddleBox := by
  rcases hx with ⟨hcarrier, htwo, hthree⟩
  rcases sectionSixFirstHighCentralSmallI9_carrier_facts hcarrier with
    ⟨huL, huU, huPos, hvPos, hwPos, htPos, htL, htw, hwv, hcap⟩
  have hnum : 2 * x.2 ≤
      1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2 := htwo
  have hT : sectionSixFirstHighCentralSmallI9T
      x.1.1.1 x.1.1.2 x.1.2 ≤ x.2 := by
    dsimp [sectionSixFirstHighCentralSmallI9T]
    linarith [hthree]
  have hW3 : sectionSixFirstHighCentralSmallI9W3
      x.1.1.1 x.1.1.2 ≤ x.1.2 := by
    dsimp [sectionSixFirstHighCentralSmallI9W3]
    linarith [hT, htw]
  have hW : sectionSixFirstHighCentralSmallI9W x.1.1.1 ≤ x.1.1.2 := by
    dsimp [sectionSixFirstHighCentralSmallI9W]
    linarith [hW3, hwv]
  have huSeam : x.1.1.1 ≤ sectionSixFirstHighCentralSmallI9Seam := by
    dsimp [sectionSixFirstHighCentralSmallI9W,
      sectionSixFirstHighCentralSmallI9VUpper] at hW hcap ⊢
    norm_num [sectionSixFirstHighCentralSmallI9CarrierCap,
      sectionSixFirstHighCentralSmallI9Seam] at hW hcap ⊢
    linarith
  have hvU : x.1.1.2 ≤
      sectionSixFirstHighCentralSmallI9VUpper x.1.1.1 := by
    dsimp [sectionSixFirstHighCentralSmallI9VUpper]
    linarith [hcap]
  refine ⟨⟨huL, huSeam⟩, hW, hvU, hW3, hwv, hT, htw⟩

theorem sectionSixFirstHighCentralSmallI9_middleBox_widths
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstHighCentralSmallI9MiddleBox) :
    0 ≤ sectionSixFirstHighCentralSmallI9Seam -
        sectionSixFirstHighCentralSmallI9Beta ∧
    0 ≤ sectionSixFirstHighCentralSmallI9VUpper x.1.1.1 -
        sectionSixFirstHighCentralSmallI9W x.1.1.1 ∧
    sectionSixFirstHighCentralSmallI9VUpper x.1.1.1 -
        sectionSixFirstHighCentralSmallI9W x.1.1.1 ≤
      sectionSixFirstHighCentralSmallI9Width / 6 ∧
    0 ≤ x.1.1.2 - sectionSixFirstHighCentralSmallI9W3
        x.1.1.1 x.1.1.2 ∧
    x.1.1.2 - sectionSixFirstHighCentralSmallI9W3
        x.1.1.1 x.1.1.2 ≤ sectionSixFirstHighCentralSmallI9Width / 5 ∧
    0 ≤ x.1.2 - sectionSixFirstHighCentralSmallI9T
        x.1.1.1 x.1.1.2 x.1.2 ∧
    x.1.2 - sectionSixFirstHighCentralSmallI9T
        x.1.1.1 x.1.1.2 x.1.2 ≤ sectionSixFirstHighCentralSmallI9Width / 4 := by
  rcases hx with ⟨hu, hW, hvU, hW3, hwv, hT, htw⟩
  rcases hu with ⟨huL, huU⟩
  norm_num [sectionSixFirstHighCentralSmallI9VUpper,
    sectionSixFirstHighCentralSmallI9W,
    sectionSixFirstHighCentralSmallI9W3,
    sectionSixFirstHighCentralSmallI9T,
    sectionSixFirstHighCentralSmallI9CarrierCap,
    sectionSixFirstHighCentralSmallI9Beta,
    sectionSixFirstHighCentralSmallI9Seam,
    sectionSixFirstHighCentralSmallI9Width] at hW hvU hW3 hT htw huL huU
  have hA : 0 ≤ sectionSixFirstHighCentralSmallI9Seam -
      sectionSixFirstHighCentralSmallI9Beta := by
    norm_num [sectionSixFirstHighCentralSmallI9Seam,
      sectionSixFirstHighCentralSmallI9Beta]
  have hB : 0 ≤ sectionSixFirstHighCentralSmallI9VUpper x.1.1.1 -
      sectionSixFirstHighCentralSmallI9W x.1.1.1 := by
    norm_num [sectionSixFirstHighCentralSmallI9VUpper,
      sectionSixFirstHighCentralSmallI9W,
      sectionSixFirstHighCentralSmallI9CarrierCap]
    linarith [huU]
  have hC : sectionSixFirstHighCentralSmallI9VUpper x.1.1.1 -
      sectionSixFirstHighCentralSmallI9W x.1.1.1 ≤
      sectionSixFirstHighCentralSmallI9Width / 6 := by
    norm_num [sectionSixFirstHighCentralSmallI9VUpper,
      sectionSixFirstHighCentralSmallI9W,
      sectionSixFirstHighCentralSmallI9Width,
      sectionSixFirstHighCentralSmallI9CarrierCap]
    linarith [huL]
  have hD : 0 ≤ x.1.1.2 -
      sectionSixFirstHighCentralSmallI9W3 x.1.1.1 x.1.1.2 := by
    dsimp [sectionSixFirstHighCentralSmallI9W3]
    linarith [hW3]
  have hE : x.1.1.2 -
      sectionSixFirstHighCentralSmallI9W3 x.1.1.1 x.1.1.2 ≤
      sectionSixFirstHighCentralSmallI9Width / 5 := by
    norm_num [sectionSixFirstHighCentralSmallI9W3,
      sectionSixFirstHighCentralSmallI9Width]
    linarith [hvU, huL]
  have hF : 0 ≤ x.1.2 -
      sectionSixFirstHighCentralSmallI9T x.1.1.1 x.1.1.2 x.1.2 := by
    dsimp [sectionSixFirstHighCentralSmallI9T]
    linarith [hT]
  have hG : x.1.2 -
      sectionSixFirstHighCentralSmallI9T x.1.1.1 x.1.1.2 x.1.2 ≤
      sectionSixFirstHighCentralSmallI9Width / 4 := by
    norm_num [sectionSixFirstHighCentralSmallI9T,
      sectionSixFirstHighCentralSmallI9Width]
    linarith [hT, htw, hwv, hvU, huL]
  exact ⟨hA, hB, hC, hD, hE, hF, hG⟩

theorem sectionSixFirstHighCentralSmallI9_middleBox_coordinate_lower
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstHighCentralSmallI9MiddleBox) :
    (9 / 100 : Real) ≤ x.1.1.2 ∧
    (9 / 100 : Real) ≤ x.1.2 ∧
    (9 / 100 : Real) ≤ x.2 := by
  rcases hx with ⟨⟨huL, huU⟩, hW, hvU, hW3, hwv, hT, htw⟩
  dsimp [sectionSixFirstHighCentralSmallI9W,
    sectionSixFirstHighCentralSmallI9W3,
    sectionSixFirstHighCentralSmallI9T] at hW hW3 hT ⊢
  norm_num [sectionSixFirstHighCentralSmallI9Seam,
    sectionSixFirstHighCentralSmallI9VUpper,
    sectionSixFirstHighCentralSmallI9CarrierCap] at huU hvU hW hW3 hT ⊢
  constructor
  · linarith
  constructor
  · linarith [hW3, hvU, huU]
  · linarith [hT, hwv, hvU, huU]

theorem sectionSixFirstHighCentralSmallI9_middleBox_kernel_excess_pointwise
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstHighCentralSmallI9MiddleBox) :
    sectionSixFirstHighCentralSmallI9MiddleExcess /
        (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ 2) ≤
      sectionSixFirstHighCentralSmallI9MiddleExcess /
        (sectionSixFirstHighCentralSmallI9Beta * (9 / 100 : Real) ^ 4) := by
  change x.1.1.1 ∈ Icc sectionSixFirstHighCentralSmallI9Beta
      sectionSixFirstHighCentralSmallI9Seam ∧ _ at hx
  have hden := sectionSixFirstHighCentralSmallI9_middleBox_coordinate_lower hx
  have hc := sectionSixFirstHighCentralSmallI9_constants_numeric
  have hpos : 0 < sectionSixFirstHighCentralSmallI9MiddleExcess := hc.2.1
  have hβ : 0 < sectionSixFirstHighCentralSmallI9Beta := by
    norm_num [sectionSixFirstHighCentralSmallI9Beta]
  have hdenPos : 0 <
      x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ 2 := by
    have huPos : 0 < x.1.1.1 :=
      lt_of_lt_of_le hβ hx.1.1
    have hvPos : 0 < x.1.1.2 := by linarith [hden.1]
    have hwPos : 0 < x.1.2 := by linarith [hden.2.1]
    have htPos : 0 < x.2 := by linarith [hden.2.2]
    positivity
  have hlowPos : 0 < sectionSixFirstHighCentralSmallI9Beta *
      (9 / 100 : Real) ^ 4 := by positivity
  have hdenLower : sectionSixFirstHighCentralSmallI9Beta *
      (9 / 100 : Real) ^ 4 ≤
      x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ 2 := by
    have hb : (0 : Real) ≤ 9 / 100 := by norm_num
    have hβ0 : (0 : Real) ≤ sectionSixFirstHighCentralSmallI9Beta := hβ.le
    have hu0 : (0 : Real) ≤ x.1.1.1 := by linarith [hβ, hx.1.1]
    have hv0 : (0 : Real) ≤ x.1.1.2 := by linarith [hden.1]
    have hw0 : (0 : Real) ≤ x.1.2 := by linarith [hden.2.1]
    have ht0 : (0 : Real) ≤ x.2 := by linarith [hden.2.2]
    have huv := mul_le_mul hx.1.1 hden.1 hb hu0
    have huvW := mul_le_mul huv hden.2.1 hb (mul_nonneg hu0 hv0)
    have hsq : (9 / 100 : Real) ^ 2 ≤ x.2 ^ 2 :=
      (sq_le_sq₀ hb ht0).2 hden.2.2
    have hall := mul_le_mul huvW hsq (sq_nonneg (9 / 100 : Real))
      (mul_nonneg (mul_nonneg hu0 hv0) hw0)
    nlinarith [hall]
  exact div_le_div_of_nonneg_left hpos.le hlowPos hdenLower

end

end PrimesRestrictedDigits
