import PrimesRestrictedDigits.SieveDecomposition.SectionSixCutoffs
import PrimesRestrictedDigits.SieveDecomposition.SectionSixPrimeRecurrence

/-!
# First Section 6 factor threshold

This file defines the factor-reduction threshold in the first Section 6 decomposition and
proves the two finite comparisons used by the exact ledger.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 139--140, Eqs. (6.4)--(6.5).
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The first factor-reduction threshold `min(p, sqrt(X/p))` at a decimal
power-of-ten scale. -/
def sectionSixFirstFactorThreshold (length p : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  min (p : Real) (Real.sqrt (X / (p : Real)))

private theorem sectionSixZOne_le_firstFactorThreshold_aux
    {epsilon X : Real} (hepsilon : 0 < epsilon) (hX : 1 < X)
    {p : Nat}
    (hp : p ∈ sievePrimeInterval (sectionSixZOne epsilon X)
      (sectionSixZFour X)) :
    sectionSixZOne epsilon X <=
      min (p : Real) (Real.sqrt (X / (p : Real))) := by
  have hpData := mem_sievePrimeInterval.mp hp
  have hXPos : 0 < X := zero_lt_one.trans hX
  have hXNonneg : 0 <= X := hXPos.le
  have hpPos : (0 : Real) < (p : Real) := by
    exact_mod_cast hpData.1.pos
  have hgapQuarter : sectionSixThetaGap epsilon <= (1 / 4 : Real) := by
    rw [sectionSixThetaGap_eq]
    linarith
  have hz1Quarter :
      sectionSixZOne epsilon X <= X ^ (1 / 4 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hX.le hgapQuarter
  have hpUpper : (p : Real) <= X ^ (1 / 2 : Real) := by
    simpa only [sectionSixZFour_eq_rpow] using hpData.2.2
  have hhalfMul : X ^ (1 / 2 : Real) * (p : Real) <= X := by
    calc
      X ^ (1 / 2 : Real) * (p : Real) <=
          X ^ (1 / 2 : Real) * X ^ (1 / 2 : Real) :=
        mul_le_mul_of_nonneg_left hpUpper (Real.rpow_nonneg hXNonneg _)
      _ = X ^ ((1 / 2 : Real) + (1 / 2 : Real)) := by
        rw [Real.rpow_add hXPos]
      _ = X := by norm_num
  have hhalfDiv : X ^ (1 / 2 : Real) <= X / (p : Real) :=
    (le_div_iff₀ hpPos).2 hhalfMul
  have hsqrtDiv :
      X ^ (1 / 4 : Real) <= Real.sqrt (X / (p : Real)) := by
    have hsqrt := Real.sqrt_le_sqrt hhalfDiv
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow] at hsqrt
    have hquarter :
        (X ^ (1 / 2 : Real)) ^ (1 / 2 : Real) =
          X ^ (1 / 4 : Real) := by
      rw [← Real.rpow_mul hXNonneg]
      congr 1
      norm_num
    simpa only [Real.sqrt_eq_rpow, hquarter] using hsqrt
  exact le_min hpData.2.1.le (hz1Quarter.trans hsqrtDiv)

/-- Every outer prime in `(z1,z4]` has factor threshold at least `z1`. Only
positivity of epsilon is needed for the exponent comparison. -/
theorem sectionSixZOne_le_firstFactorThreshold_of_mem
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {length p : Nat} (hlength : 1 <= length)
    (hp : p ∈ sievePrimeInterval
      (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
      (sectionSixZFour ((10 ^ length : Nat) : Real))) :
    sectionSixZOne epsilon ((10 ^ length : Nat) : Real) <=
      sectionSixFirstFactorThreshold length p := by
  have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  simpa only [sectionSixFirstFactorThreshold] using
    (sectionSixZOne_le_firstFactorThreshold_aux hepsilon hX hp)

/-- In the high outer range, `p>X^theta2` and `theta2>1/3`, so the minimum is
the square-root factor threshold appearing in the second sum of Eq. (6.5). -/
theorem sectionSixFirstFactorThreshold_eq_sqrt_of_mem_high
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length p : Nat} (hlength : 1 <= length)
    (hp : p ∈ sievePrimeInterval
      (sectionSixZThree epsilon ((10 ^ length : Nat) : Real))
      (sectionSixZFour ((10 ^ length : Nat) : Real))) :
    sectionSixFirstFactorThreshold length p =
      Real.sqrt (((10 ^ length : Nat) : Real) / (p : Real)) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hXPos : 0 < X := zero_lt_one.trans hX
  have hXNonneg : 0 <= X := hXPos.le
  have hpData := mem_sievePrimeInterval.mp hp
  have hpPos : (0 : Real) < (p : Real) := by
    exact_mod_cast hpData.1.pos
  have hthirdTheta : (1 / 3 : Real) < sectionSixThetaTwo epsilon := by
    simp only [sectionSixThetaTwo]
    linarith
  have hthirdP : X ^ (1 / 3 : Real) < (p : Real) := by
    calc
      X ^ (1 / 3 : Real) < X ^ sectionSixThetaTwo epsilon :=
        Real.rpow_lt_rpow_of_exponent_lt hX hthirdTheta
      _ = sectionSixZThree epsilon X := rfl
      _ < (p : Real) := by simpa only [X] using hpData.2.1
  have hthirdCube : (X ^ (1 / 3 : Real)) ^ (3 : Nat) = X := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXNonneg]
    norm_num
  have hcube : X < (p : Real) ^ (3 : Nat) := by
    rw [← hthirdCube]
    exact pow_lt_pow_left₀ hthirdP (Real.rpow_nonneg hXNonneg _) (by norm_num)
  have hdivSq : X / (p : Real) < (p : Real) ^ (2 : Nat) := by
    rw [div_lt_iff₀ hpPos]
    nlinarith
  have hsqrt : Real.sqrt (X / (p : Real)) < (p : Real) :=
    (Real.sqrt_lt' hpPos).2 hdivSq
  unfold sectionSixFirstFactorThreshold
  simpa only [X] using min_eq_right hsqrt.le

end

end PrimesRestrictedDigits
