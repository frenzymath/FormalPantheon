import PrimesRestrictedDigits.ExceptionalMinorArcs.LineNormalizedSecondMomentCarrier
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination

/-!
# Cross coefficients for normalized second-moment data

This derives the exact cross relation used in the small-height estimate of
`MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 211--212. It starts from the two original integer
relations and does not use the defective normalized display.
-/

namespace PrimesRestrictedDigits

/-- The four source-ordered coefficients after eliminating the common first
member from two normalized relations. -/
structure LineNormalizedCrossData where
  /-- Coefficient of the unprimed second member. -/
  b1 : Int
  /-- Coefficient of the primed second member. -/
  b2 : Int
  /-- Coefficient of the decimal scale. -/
  b3 : Int
  /-- Constant coefficient. -/
  b4 : Int
  deriving DecidableEq

/-- Exact cross coefficients attached to one normalized datum. -/
def lineNormalizedCrossData {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    LineNormalizedCrossData :=
  { b1 := data.uPrime * data.v2
    b2 := -(data.u * data.v2Prime)
    b3 := data.uPrime * data.v3 - data.u * data.v3Prime
    b4 := data.uPrime * data.v4 - data.u * data.v4Prime }

/-- Cross-multiplication cancels the common first member exactly. -/
theorem LineNormalizedSecondMomentData.IsValid.cross_relation
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    {data : LineNormalizedSecondMomentData X}
    (hdata : data.IsValid C D V) :
    let cross := lineNormalizedCrossData data
    cross.b1 * (data.a2.val : Int) +
      cross.b2 * (data.a2Prime.val : Int) +
      cross.b3 * (X : Int) + cross.b4 = 0 := by
  dsimp only [lineNormalizedCrossData]
  linear_combination data.uPrime * hdata.relation -
    data.u * hdata.relationPrime

theorem LineNormalizedSecondMomentData.IsValid.cross_b1_ne
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    {data : LineNormalizedSecondMomentData X}
    (hdata : data.IsValid C D V) :
    (lineNormalizedCrossData data).b1 ≠ 0 := by
  exact mul_ne_zero hdata.uPrime_ne hdata.v2_ne

theorem LineNormalizedSecondMomentData.IsValid.cross_b2_ne
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    {data : LineNormalizedSecondMomentData X}
    (hdata : data.IsValid C D V) :
    (lineNormalizedCrossData data).b2 ≠ 0 := by
  exact neg_ne_zero.mpr (mul_ne_zero hdata.u_ne hdata.v2Prime_ne)

theorem LineNormalizedSecondMomentData.u_abs_le_primitiveHeight
    {X : Nat} (data : LineNormalizedSecondMomentData X) :
    abs ((data.u : Int) : Real) ≤ (data.primitiveHeight : Real) := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  exact_mod_cast le_max_left data.u.natAbs data.uPrime.natAbs

theorem LineNormalizedSecondMomentData.uPrime_abs_le_primitiveHeight
    {X : Nat} (data : LineNormalizedSecondMomentData X) :
    abs ((data.uPrime : Int) : Real) ≤
      (data.primitiveHeight : Real) := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  exact_mod_cast le_max_right data.u.natAbs data.uPrime.natAbs

/-- Every cross coefficient lies in the common source-scale box. The first
two coefficients obey a sharper bound, but the common radius simplifies the
finite outer carrier. -/
theorem mem_orientedLineNormalizedSecondMomentClass_cross_mem_boxes
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {data : LineNormalizedSecondMomentData (10 ^ length)}
    (hdata : data ∈ orientedLineNormalizedSecondMomentClass
      length C D V j) (hV : 1 ≤ V) :
    let cross := lineNormalizedCrossData data
    let U : Real := ((10 ^ j.val : Nat) : Real)
    cross.b1 ∈ lineCoefficientBox (2 * U * V) ∧
      cross.b2 ∈ lineCoefficientBox (2 * U * V) ∧
      cross.b3 ∈ lineCoefficientBox (2 * U * V) ∧
      cross.b4 ∈ lineCoefficientBox (2 * U * V) := by
  have hfull := (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
  have hvalid := mem_lineNormalizedSecondMomentClass_isValid hfull
  have hband := mem_lineNormalizedSecondMomentClass_band hfull
  let U : Real := ((10 ^ j.val : Nat) : Real)
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hprimitiveU : (data.primitiveHeight : Real) ≤ U := by
    simpa only [U] using hband.2.1
  have huU : abs ((data.u : Int) : Real) ≤ U :=
    data.u_abs_le_primitiveHeight.trans hprimitiveU
  have huPrimeU : abs ((data.uPrime : Int) : Real) ≤ U :=
    data.uPrime_abs_le_primitiveHeight.trans hprimitiveU
  have hVNonneg : 0 ≤ V := zero_le_one.trans hV
  have hb1 :
      abs (((lineNormalizedCrossData data).b1 : Int) : Real) ≤
        2 * U * V := by
    dsimp only [lineNormalizedCrossData]
    rw [Int.cast_mul, abs_mul]
    calc
      abs (data.uPrime : Real) * abs (data.v2 : Real) ≤ U * V := by
        exact mul_le_mul huPrimeU hvalid.v2_abs_le (abs_nonneg _) hU
      _ ≤ 2 * U * V := by nlinarith [mul_nonneg hU hVNonneg]
  have hb2 :
      abs (((lineNormalizedCrossData data).b2 : Int) : Real) ≤
        2 * U * V := by
    dsimp only [lineNormalizedCrossData]
    rw [Int.cast_neg, abs_neg, Int.cast_mul, abs_mul]
    calc
      abs (data.u : Real) * abs (data.v2Prime : Real) ≤ U * V := by
        exact mul_le_mul huU hvalid.v2Prime_abs_le (abs_nonneg _) hU
      _ ≤ 2 * U * V := by nlinarith [mul_nonneg hU hVNonneg]
  have hb3 :
      abs (((lineNormalizedCrossData data).b3 : Int) : Real) ≤
        2 * U * V := by
    dsimp only [lineNormalizedCrossData]
    push_cast
    calc
      abs ((data.uPrime : Real) * data.v3 -
          (data.u : Real) * data.v3Prime) ≤
          abs ((data.uPrime : Real) * data.v3) +
            abs ((data.u : Real) * data.v3Prime) := abs_sub _ _
      _ = abs (data.uPrime : Real) * abs (data.v3 : Real) +
          abs (data.u : Real) * abs (data.v3Prime : Real) := by
        rw [abs_mul, abs_mul]
      _ ≤ U * V + U * V := by
        exact add_le_add
          (mul_le_mul huPrimeU hvalid.v3_abs_le (abs_nonneg _) hU)
          (mul_le_mul huU hvalid.v3Prime_abs_le (abs_nonneg _) hU)
      _ = 2 * U * V := by ring
  have hb4 :
      abs (((lineNormalizedCrossData data).b4 : Int) : Real) ≤
        2 * U * V := by
    dsimp only [lineNormalizedCrossData]
    push_cast
    calc
      abs ((data.uPrime : Real) * data.v4 -
          (data.u : Real) * data.v4Prime) ≤
          abs ((data.uPrime : Real) * data.v4) +
            abs ((data.u : Real) * data.v4Prime) := abs_sub _ _
      _ = abs (data.uPrime : Real) * abs (data.v4 : Real) +
          abs (data.u : Real) * abs (data.v4Prime : Real) := by
        rw [abs_mul, abs_mul]
      _ ≤ U * V + U * V := by
        exact add_le_add
          (mul_le_mul huPrimeU hvalid.v4_abs_le (abs_nonneg _) hU)
          (mul_le_mul huU hvalid.v4Prime_abs_le (abs_nonneg _) hU)
      _ = 2 * U * V := by ring
  dsimp only
  exact ⟨(mem_lineCoefficientBox_iff (by positivity)).2 hb1,
    (mem_lineCoefficientBox_iff (by positivity)).2 hb2,
    (mem_lineCoefficientBox_iff (by positivity)).2 hb3,
    (mem_lineCoefficientBox_iff (by positivity)).2 hb4⟩

end PrimesRestrictedDigits
