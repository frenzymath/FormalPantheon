import PrimesRestrictedDigits.BasicEstimates.BuchstabBounds
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralSmallQuadrupleRegions
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstUniformIntegralRegions
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-! # SectionSixFirstHighCentralSmallQuadrupleI9FiberReduction -/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

/-!
The I9 replay uses a closed carrier obtained from the mixed outer inclusion.
The carrier is deliberately larger than the source polytope: source-only pair
walls are never used as an equality in the numerical upper bound.
-/

def sectionSixFirstHighCentralSmallI9Delta : Real := 1 / 1000000000

def sectionSixFirstHighCentralSmallI9Beta : Real :=
  212499999 / 500000000

def sectionSixFirstHighCentralSmallI9Gamma : Real :=
  16249999 / 250000000

def sectionSixFirstHighCentralSmallI9CarrierCap : Real := 16 / 25

def sectionSixFirstHighCentralSmallI9Seam : Real := 23 / 50

def sectionSixFirstHighCentralSmallI9Width : Real :=
  17500001 / 250000000

def sectionSixFirstHighCentralSmallI9VUpper (u : Real) : Real :=
  (sectionSixFirstHighCentralSmallI9CarrierCap - u) / 2

def sectionSixFirstHighCentralSmallI9Carrier :
    Set (((Real × Real) × Real) × Real) :=
  {x | sectionSixFirstHighCentralSmallI9Beta ≤ x.1.1.1 ∧
    x.1.1.1 ≤ (1 / 2 : Real) ∧
    sectionSixFirstHighCentralSmallI9Gamma ≤ x.2 ∧
    x.2 ≤ x.1.2 ∧
    x.1.2 ≤ x.1.1.2 ∧
    x.1.1.1 + 2 * x.1.1.2 ≤
      sectionSixFirstHighCentralSmallI9CarrierCap}

def sectionSixFirstHighCentralSmallI9VFiber (u : Real) : Set Real :=
  Icc sectionSixFirstHighCentralSmallI9Gamma
    (sectionSixFirstHighCentralSmallI9VUpper u)

def sectionSixFirstHighCentralSmallI9WFiber (v : Real) : Set Real :=
  Icc sectionSixFirstHighCentralSmallI9Gamma v

def sectionSixFirstHighCentralSmallI9TFiber (w : Real) : Set Real :=
  Icc sectionSixFirstHighCentralSmallI9Gamma w

def sectionSixFirstHighCentralSmallI9TailCarrier :
    Set (((Real × Real) × Real) × Real) :=
  {x ∈ sectionSixFirstHighCentralSmallI9Carrier |
    3 * x.2 ≤ 1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2}

def sectionSixFirstHighCentralSmallI9MiddleCarrier :
    Set (((Real × Real) × Real) × Real) :=
  {x ∈ sectionSixFirstHighCentralSmallI9Carrier |
    2 * x.2 ≤ 1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2 ∧
      1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2 ≤ 3 * x.2}

def sectionSixFirstHighCentralSmallI9Kernel
    (x : (((Real × Real) × Real) × Real)) : Real :=
  buchstabFunction
      ((1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2) /
    (x.1.1.1 * x.1.1.2 * x.1.2 * x.2 ^ 2)

theorem sectionSixFirstHighCentralSmallI9_constants :
    0 < sectionSixFirstHighCentralSmallI9Gamma ∧
    sectionSixFirstHighCentralSmallI9Gamma ≤
      sectionSixFirstHighCentralSmallI9Beta ∧
    (2 / 5 : Real) < sectionSixFirstHighCentralSmallI9Beta ∧
    sectionSixFirstHighCentralSmallI9Beta ≤ (1 / 2 : Real) ∧
    sectionSixFirstHighCentralSmallI9Beta ≤
      sectionSixFirstHighCentralSmallI9Seam ∧
    sectionSixFirstHighCentralSmallI9Seam ≤ (1 / 2 : Real) ∧
    0 < sectionSixFirstHighCentralSmallI9Width := by
  norm_num [sectionSixFirstHighCentralSmallI9Gamma,
    sectionSixFirstHighCentralSmallI9Beta,
    sectionSixFirstHighCentralSmallI9Seam,
    sectionSixFirstHighCentralSmallI9Width]

theorem sectionSixFirstHighCentralSmallI9_width_identity :
    sectionSixFirstHighCentralSmallI9Width =
      23 / 25 - 2 * sectionSixFirstHighCentralSmallI9Beta := by
  norm_num [sectionSixFirstHighCentralSmallI9Width,
    sectionSixFirstHighCentralSmallI9Beta]

theorem sectionSixFirstHighCentralSmallI9_vupper_facts
    {u : Real} (hu : u ∈ Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2)) :
    0 < sectionSixFirstHighCentralSmallI9VUpper u ∧
    sectionSixFirstHighCentralSmallI9Gamma ≤
      sectionSixFirstHighCentralSmallI9VUpper u ∧
    sectionSixFirstHighCentralSmallI9VUpper u ≤ (1 / 2 : Real) := by
  rcases hu with ⟨huL, huU⟩
  norm_num [sectionSixFirstHighCentralSmallI9VUpper,
    sectionSixFirstHighCentralSmallI9CarrierCap,
    sectionSixFirstHighCentralSmallI9Gamma,
    sectionSixFirstHighCentralSmallI9Beta] at huL huU ⊢
  constructor
  · linarith
  constructor <;> linarith

theorem sectionSixFirstHighCentralSmallI9_carrier_measurable :
    MeasurableSet sectionSixFirstHighCentralSmallI9Carrier := by
  unfold sectionSixFirstHighCentralSmallI9Carrier
  measurability

theorem sectionSixFirstHighCentralSmallI9_carrier_fiber_iff
    {x : (((Real × Real) × Real) × Real)} :
    x ∈ sectionSixFirstHighCentralSmallI9Carrier ↔
      x.1.1.1 ∈ Icc sectionSixFirstHighCentralSmallI9Beta (1 / 2) ∧
      x.1.1.2 ∈ sectionSixFirstHighCentralSmallI9VFiber x.1.1.1 ∧
      x.1.2 ∈ sectionSixFirstHighCentralSmallI9WFiber x.1.1.2 ∧
      x.2 ∈ sectionSixFirstHighCentralSmallI9TFiber x.1.2 := by
  constructor
  · intro hx
    rcases hx with ⟨huL, huU, htL, htw, hwv, hcap⟩
    have hvL : sectionSixFirstHighCentralSmallI9Gamma ≤ x.1.1.2 :=
      htL.trans (htw.trans hwv)
    have hvU : x.1.1.2 ≤
        sectionSixFirstHighCentralSmallI9VUpper x.1.1.1 := by
      dsimp [sectionSixFirstHighCentralSmallI9VUpper]
      linarith
    exact ⟨⟨huL, huU⟩, ⟨hvL, hvU⟩, ⟨htL.trans htw, hwv⟩,
      ⟨htL, htw⟩⟩
  · rintro ⟨hu, hv, hw, ht⟩
    rcases hu with ⟨huL, huU⟩
    rcases hv with ⟨hvL, hvU⟩
    rcases hw with ⟨hwL, hwU⟩
    rcases ht with ⟨htL, htU⟩
    refine ⟨huL, huU, htL, htU, hwU, ?_⟩
    dsimp [sectionSixFirstHighCentralSmallI9VUpper] at hvU
    linarith

theorem sectionSixFirstHighCentralSmallI9_carrier_facts
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstHighCentralSmallI9Carrier) :
    sectionSixFirstHighCentralSmallI9Beta ≤ x.1.1.1 ∧
    x.1.1.1 ≤ (1 / 2 : Real) ∧
    0 < x.1.1.1 ∧
    0 < x.1.1.2 ∧
    0 < x.1.2 ∧
    0 < x.2 ∧
    sectionSixFirstHighCentralSmallI9Gamma ≤ x.2 ∧
    x.2 ≤ x.1.2 ∧
    x.1.2 ≤ x.1.1.2 ∧
    x.1.1.1 + 2 * x.1.1.2 ≤
      sectionSixFirstHighCentralSmallI9CarrierCap := by
  rcases hx with ⟨huL, huU, htL, htw, hwv, hcap⟩
  have hc := sectionSixFirstHighCentralSmallI9_constants
  have hvL : sectionSixFirstHighCentralSmallI9Gamma ≤ x.1.1.2 := by
    exact htL.trans (htw.trans hwv)
  have huPos : 0 < x.1.1.1 :=
    lt_of_lt_of_le hc.1 (hc.2.1.trans huL)
  have hvPos : 0 < x.1.1.2 := lt_of_lt_of_le hc.1 hvL
  have hwPos : 0 < x.1.2 := lt_of_lt_of_le hc.1 (htL.trans htw)
  have htPos : 0 < x.2 := lt_of_lt_of_le hc.1 htL
  exact ⟨huL, huU, huPos, hvPos, hwPos, htPos,
    htL, htw, hwv, hcap⟩

theorem sectionSixFirstHighCentralSmallI9_argument_ge_two
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstHighCentralSmallI9Carrier) :
    (2 : Real) ≤
      (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
  rcases sectionSixFirstHighCentralSmallI9_carrier_facts hx with
    ⟨huL, huU, huPos, hvPos, hwPos, htPos, htL, htw, hwv, hcap⟩
  rw [le_div_iff₀ htPos]
  have huLower : (2 / 5 : Real) < x.1.1.1 :=
    (sectionSixFirstHighCentralSmallI9_constants.2.2.1).trans_le huL
  norm_num [sectionSixFirstHighCentralSmallI9CarrierCap] at hcap huLower ⊢
  linarith [hcap, htw, hwv]

theorem sectionSixFirstHighCentralSmallI9_kernel_nonneg
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstHighCentralSmallI9Carrier) :
    0 ≤ sectionSixFirstHighCentralSmallI9Kernel x := by
  have harg := sectionSixFirstHighCentralSmallI9_argument_ge_two hx
  have hargOne : (1 : Real) ≤
      (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 :=
    (by linarith : (1 : Real) ≤ 2).trans harg
  have hω := buchstabFunction_mem_Icc hargOne
  rcases sectionSixFirstHighCentralSmallI9_carrier_facts hx with
    ⟨_, _, hu, hv, hw, ht, _, _, _, _⟩
  unfold sectionSixFirstHighCentralSmallI9Kernel
  exact div_nonneg (by linarith [hω.1])
    (mul_nonneg (mul_nonneg (mul_nonneg hu.le hv.le) hw.le)
      (sq_nonneg _))

theorem sectionSixFirstHighCentralSmallI9_carrier_middle_or_tail
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstHighCentralSmallI9Carrier) :
    x ∈ sectionSixFirstHighCentralSmallI9TailCarrier ∨
      x ∈ sectionSixFirstHighCentralSmallI9MiddleCarrier := by
  have harg := sectionSixFirstHighCentralSmallI9_argument_ge_two hx
  rcases sectionSixFirstHighCentralSmallI9_carrier_facts hx with
    ⟨_, _, _, _, _, htPos, _, _, _, _⟩
  by_cases htail :
      3 * x.2 ≤ 1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2
  · exact Or.inl ⟨hx, htail⟩
  · right
    refine ⟨hx, ?_, ?_⟩
    · exact (le_div_iff₀ htPos).mp harg
    · exact le_of_not_ge htail

/- The exact weak region is covered by this carrier under the two hypotheses
   required by the existing mixed monotonicity bridge. -/
theorem sectionSixFirstHighCentralSmallI9_exact_subset_carrier
    {epsilon : Real}
    (hepsilonNonneg : 0 ≤ epsilon)
    (hepsilonUpper : epsilon ≤ sectionSixFirstHighCentralSmallI9Delta) :
    sectionSixFirstHighCentralSmallQuadrupleRegion epsilon ⊆
      sectionSixFirstHighCentralSmallI9Carrier := by
  intro x hx
  have houter := sectionSixFirstHighCentralSmallQuadrupleRegion_subset_uniformOuterRegion
    hepsilonNonneg hepsilonUpper hx
  rcases houter with ⟨ht, htw, hwv, hu, huHalf, hcap⟩
  rw [sectionSixThetaGap_eq] at ht
  norm_num [sectionSixFirstHighCentralSmallI9Delta,
    sectionSixThetaTwo,
    sectionSixFirstHighCentralSmallI9Beta,
    sectionSixFirstHighCentralSmallI9Gamma,
    sectionSixFirstHighCentralSmallI9CarrierCap] at ht hu hcap ⊢
  exact ⟨le_of_lt hu, huHalf, le_of_lt ht, htw, hwv, le_of_lt hcap⟩

theorem sectionSixFirstHighCentralSmallI9_exact_kernel_eq
    {x : (((Real × Real) × Real) × Real)} :
    sectionSixFirstHighCentralSmallI9Kernel x =
      sectionSixFirstHighCentralSmallQuadrupleKernel x := rfl

end

end PrimesRestrictedDigits
