import PrimesRestrictedDigits.ExceptionalMinorArcs.ComparableMagnitudeBand
import PrimesRestrictedDigits.GenericMinorArcs.GenericFrequencyBounds
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Log

/-!
# Canonical exceptional Fourier-magnitude bands

The source's raw terminal comparable band is not contained in the exceptional carrier. These
disjoint fibers retain that intersection explicitly.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The largest decimal-power index below `floor (1/F(a))`. -/
noncomputable def exceptionalMagnitudeBandIndex
    (digit : Fin 10) (length : Nat) (a : Fin (10 ^ length)) : Nat :=
  Nat.log 10
    (Nat.floor
      (1 / normalizedPaddedDigitFourierMagnitude digit length a.val))

/-- The corresponding real power-of-ten upper parameter in the source
comparable-magnitude convention. -/
noncomputable def exceptionalMagnitudeBandScale
    (digit : Fin 10) (length : Nat) (a : Fin (10 ^ length)) : Real :=
  (10 ^ exceptionalMagnitudeBandIndex digit length a : Nat)

/-- The exact exceptional frequencies assigned to one canonical magnitude
index. -/
noncomputable def exceptionalMagnitudeBandFrequencies
    (digit : Fin 10) (length j : Nat) : Finset (Fin (10 ^ length)) := by
  classical
  exact (genericExceptionalFrequencies digit length).filter fun a =>
    exceptionalMagnitudeBandIndex digit length a = j

@[simp]
theorem mem_exceptionalMagnitudeBandFrequencies_iff
    {digit : Fin 10} {length j : Nat} {a : Fin (10 ^ length)} :
    a ∈ exceptionalMagnitudeBandFrequencies digit length j ↔
      a ∈ genericExceptionalFrequencies digit length ∧
        exceptionalMagnitudeBandIndex digit length a = j := by
  simp [exceptionalMagnitudeBandFrequencies]

private theorem exceptionalMagnitude_pos
    {digit : Fin 10} {length : Nat} {a : Fin (10 ^ length)}
    (ha : a ∈ genericExceptionalFrequencies digit length) :
    0 < normalizedPaddedDigitFourierMagnitude digit length a.val := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 0 < X := by dsimp only [X]; positivity
  have hlower := mem_genericExceptionalFrequencies.mp ha
  exact (Real.rpow_pos_of_pos hX (-(23 / 80 : Real))).trans_le hlower

private theorem one_le_inv_exceptionalMagnitude
    {digit : Fin 10} {length : Nat} {a : Fin (10 ^ length)}
    (ha : a ∈ genericExceptionalFrequencies digit length) :
    1 <= 1 / normalizedPaddedDigitFourierMagnitude digit length a.val := by
  have hF := exceptionalMagnitude_pos ha
  apply (le_div_iff₀ hF).2
  simpa using normalizedPaddedDigitFourierMagnitude_le_one
    digit length a.val

private theorem exceptionalMagnitudeBandScale_bounds
    {digit : Fin 10} {length : Nat} {a : Fin (10 ^ length)}
    (ha : a ∈ genericExceptionalFrequencies digit length) :
    exceptionalMagnitudeBandScale digit length a <=
        1 / normalizedPaddedDigitFourierMagnitude digit length a.val ∧
      1 / normalizedPaddedDigitFourierMagnitude digit length a.val <
        10 * exceptionalMagnitudeBandScale digit length a := by
  let F := normalizedPaddedDigitFourierMagnitude digit length a.val
  let n := Nat.floor (1 / F)
  let j := Nat.log 10 n
  let B : Nat := 10 ^ j
  have hinv : 1 <= 1 / F := one_le_inv_exceptionalMagnitude ha
  have hnPos : 0 < n := by
    rw [Nat.floor_pos]
    exact hinv
  have hBLower : B <= n := by
    exact Nat.pow_log_le_self 10 hnPos.ne'
  have hnUpper : n < 10 * B := by
    have hpow := Nat.lt_pow_succ_log_self (by norm_num : 1 < 10) n
    simpa [B, j, pow_succ, Nat.mul_comm] using hpow
  have hfloorLower : (n : Real) <= 1 / F := by
    exact Nat.floor_le (by positivity [hinv])
  have hfloorUpper : 1 / F < (n : Real) + 1 := Nat.lt_floor_add_one _
  have hsuccUpper : (n : Real) + 1 <= 10 * B := by
    exact_mod_cast (Nat.succ_le_iff.mpr hnUpper)
  have hBLowerReal : (B : Real) <= n := by
    exact_mod_cast hBLower
  change (B : Real) <= 1 / F ∧ 1 / F < 10 * (B : Real)
  constructor
  · exact hBLowerReal.trans hfloorLower
  · exact lt_of_lt_of_le hfloorUpper hsuccUpper

/-- Every canonical fiber lies in the source's strict-lower, weak-upper
comparable band. -/
theorem exceptionalMagnitudeBandFrequencies_subset_comparable
    {digit : Fin 10} {length j : Nat} :
    exceptionalMagnitudeBandFrequencies digit length j ⊆
      comparableMagnitudeFrequencies digit length (10 ^ j : Nat) := by
  intro a ha
  have hdata := mem_exceptionalMagnitudeBandFrequencies_iff.mp ha
  have hF := exceptionalMagnitude_pos hdata.1
  have hB : (0 : Real) < (10 ^ j : Nat) := by positivity
  have hscale := exceptionalMagnitudeBandScale_bounds hdata.1
  simp only [exceptionalMagnitudeBandScale, hdata.2] at hscale
  apply mem_comparableMagnitudeFrequencies.mpr
  constructor
  · apply (div_lt_iff₀ (mul_pos (by norm_num) hB)).2
    have hinv := (div_lt_iff₀ hF).1 hscale.2
    nlinarith
  · apply (le_div_iff₀ hB).2
    have hinv := (le_div_iff₀ hF).1 hscale.1
    nlinarith

private theorem exceptionalMagnitudeBandScale_le_sourceLimit
    {digit : Fin 10} {length : Nat} {a : Fin (10 ^ length)}
    (ha : a ∈ genericExceptionalFrequencies digit length) :
    exceptionalMagnitudeBandScale digit length a <=
      (((10 ^ length : Nat) : Real) ^ (23 / 80 : Real)) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let F := normalizedPaddedDigitFourierMagnitude digit length a.val
  have hX : 0 < X := by dsimp only [X]; positivity
  have hF : 0 < F := exceptionalMagnitude_pos ha
  have hlower : X ^ (-(23 / 80 : Real)) <= F := by
    simpa only [X, F] using mem_genericExceptionalFrequencies.mp ha
  have hinv : 1 / F <= X ^ (23 / 80 : Real) := by
    apply (div_le_iff₀ hF).2
    calc
      1 = X ^ (23 / 80 : Real) * X ^ (-(23 / 80 : Real)) := by
        rw [← Real.rpow_add hX]
        norm_num
      _ <= X ^ (23 / 80 : Real) * F := by
        exact mul_le_mul_of_nonneg_left hlower (Real.rpow_nonneg hX.le _)
  exact (exceptionalMagnitudeBandScale_bounds ha).1.trans hinv

/-- The canonical scale of any member of the `j`th exceptional fiber is at
most the terminal source scale `X^(23/80)`. -/
theorem exceptionalMagnitudeBandScale_le_sourceLimit_of_mem
    {digit : Fin 10} {length j : Nat} {a : Fin (10 ^ length)}
    (ha : a ∈ exceptionalMagnitudeBandFrequencies digit length j) :
    ((10 ^ j : Nat) : Real) <=
      (((10 ^ length : Nat) : Real) ^ (23 / 80 : Real)) := by
  have hdata := mem_exceptionalMagnitudeBandFrequencies_iff.mp ha
  have hbound := exceptionalMagnitudeBandScale_le_sourceLimit hdata.1
  simpa only [exceptionalMagnitudeBandScale, hdata.2] using hbound

/-- Every exceptional frequency has a canonical index below `length` when
the decimal length is positive. -/
theorem exceptionalMagnitudeBandIndex_lt
    {digit : Fin 10} {length : Nat} (hlength : 0 < length)
    {a : Fin (10 ^ length)}
    (ha : a ∈ genericExceptionalFrequencies digit length) :
    exceptionalMagnitudeBandIndex digit length a < length := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hXOne : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow hlength.ne' (by norm_num : 1 < 10)
  have hscaleLimit := exceptionalMagnitudeBandScale_le_sourceLimit ha
  have hpower : X ^ (23 / 80 : Real) < X := by
    calc
      X ^ (23 / 80 : Real) < X ^ (1 : Real) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        · exact hXOne
        · norm_num
      _ = X := Real.rpow_one X
  have hreal :
      ((10 ^ exceptionalMagnitudeBandIndex digit length a : Nat) : Real) <
        ((10 ^ length : Nat) : Real) := by
    simpa only [exceptionalMagnitudeBandScale, X] using
      hscaleLimit.trans_lt hpower
  have hnat :
      10 ^ exceptionalMagnitudeBandIndex digit length a < 10 ^ length := by
    exact_mod_cast hreal
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 10)).mp hnat

/-- The canonical fibers give an exact disjoint sum decomposition of the
exceptional carrier. -/
theorem sum_exceptionalMagnitudeBandFrequencies
    {M : Type*} [AddCommMonoid M]
    (digit : Fin 10) {length : Nat} (hlength : 0 < length)
    (f : Fin (10 ^ length) -> M) :
    (∑ j ∈ Finset.range length,
      ∑ a ∈ exceptionalMagnitudeBandFrequencies digit length j, f a) =
      ∑ a ∈ genericExceptionalFrequencies digit length, f a := by
  classical
  apply Finset.sum_fiberwise_of_maps_to
  intro a ha
  exact Finset.mem_range.mpr
    (exceptionalMagnitudeBandIndex_lt hlength ha)

end PrimesRestrictedDigits
