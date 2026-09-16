import PrimesRestrictedDigits.Fourier.ContinuousTransformProperties
import PrimesRestrictedDigits.Fourier.ReducedFractionCarrier
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Finset.Interval

/-!
# Aligned integer-grid carriers for hybrid bounds

These finite carriers encode the real aligned perturbations in `MAYNARD-PRD-PUBLISHED`, Lemma
10.6, pp. 178--180.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- Integer numerators `b` for which `b / 10^length` lies in the closed
`E / 10^length` window about `x`. The ceiling occurs only in the finite
ambient interval; membership retains the exact real window. -/
noncomputable def alignedGridWindow
    (length : Nat) (E x : Real) : Finset Int := by
  classical
  let Y : Nat := 10 ^ length
  let B : Nat := Nat.ceil E
  exact (Finset.Icc (-(B : Int)) ((Y : Int) + B)).filter fun b =>
    |(b : Real) / Y - x| <= E / Y

theorem mem_alignedGridWindow_iff
    {length : Nat} {E x : Real} {b : Int} :
    b ∈ alignedGridWindow length E x ↔
      -(Nat.ceil E : Int) <= b ∧
      b <= ((10 ^ length : Nat) : Int) + Nat.ceil E ∧
      |(b : Real) / ((10 ^ length : Nat) : Real) - x| <=
        E / ((10 ^ length : Nat) : Real) := by
  classical
  simp only [alignedGridWindow, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- For a base in `[0,1]`, the finite ceiling envelope loses no aligned grid
points. -/
theorem mem_alignedGridWindow_iff_of_mem_Icc
    {length : Nat} {E x : Real} (hE : 0 <= E) (hx : x ∈ Set.Icc (0 : Real) 1)
    {b : Int} :
    b ∈ alignedGridWindow length E x ↔
      |(b : Real) / ((10 ^ length : Nat) : Real) - x| <=
        E / ((10 ^ length : Nat) : Real) := by
  let Y : Real := ((10 ^ length : Nat) : Real)
  have hY : 0 < Y := by
    dsimp [Y]
    positivity
  have hceil : E <= (Nat.ceil E : Real) := Nat.le_ceil E
  rw [mem_alignedGridWindow_iff]
  constructor
  · exact fun h => h.2.2
  · intro hwindow
    have habs := abs_le.mp hwindow
    have hdivLower : -E / Y <= (b : Real) / Y := by
      calc
        -E / Y <= (b : Real) / Y - x := by
          simpa only [neg_div] using habs.1
        _ <= (b : Real) / Y := by linarith [hx.1]
    have hbLowerReal : (-(Nat.ceil E : Int) : Real) <= (b : Real) := by
      have hnumerator : -E <= (b : Real) :=
        (div_le_div_iff_of_pos_right hY).mp (by simpa only [neg_div] using hdivLower)
      norm_num only [Int.cast_neg, Int.cast_natCast]
      linarith
    have hdivUpper : (b : Real) / Y <= 1 + E / Y := by
      calc
        (b : Real) / Y <= x + E / Y := by linarith [habs.2]
        _ <= 1 + E / Y := by linarith [hx.2]
    have hbUpperReal : (b : Real) <=
        (((10 ^ length : Nat) : Int) + Nat.ceil E : Int) := by
      have hquotient : (b : Real) / Y <= (Y + E) / Y := by
        calc
          (b : Real) / Y <= 1 + E / Y := hdivUpper
          _ = (Y + E) / Y := by field_simp
      have hnumerator : (b : Real) <= Y + E :=
        (div_le_div_iff_of_pos_right hY).mp hquotient
      norm_num only [Int.cast_add, Int.cast_natCast]
      dsimp [Y] at hnumerator ⊢
      linarith
    exact ⟨by exact_mod_cast hbLowerReal,
      by exact_mod_cast hbUpperReal, hwindow⟩

/-- The weighted aligned-grid sum that replaces the source's real `eta`
summation. -/
noncomputable def alignedGridSum
    (digit : Fin 10) (length : Nat) (E x : Real) : Real :=
  ∑ b ∈ alignedGridWindow length E x,
    normalizedPaddedDigitFourierMagnitudeAt digit length
      ((b : Real) / ((10 ^ length : Nat) : Real))

theorem alignedGridSum_nonneg
    (digit : Fin 10) (length : Nat) (E x : Real) :
    0 <= alignedGridSum digit length E x := by
  classical
  exact Finset.sum_nonneg fun b _ =>
    normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length _

/-- Canonical reduced fractions with the source's strict real denominator
cutoff and the divisibility restriction. -/
noncomputable def strictDivisibleReducedFractionCarrier
    (Q : Real) (d : Nat) : Finset (Nat × Nat) := by
  classical
  exact (divisibleReducedFractionCarrier (Nat.floor Q) d).filter fun pair =>
    (pair.1 : Real) < Q

theorem mem_strictDivisibleReducedFractionCarrier_iff
    {Q : Real} {d : Nat} {pair : Nat × Nat} :
    pair ∈ strictDivisibleReducedFractionCarrier Q d ↔
      pair ∈ reducedFractionCarrier (Nat.floor Q) ∧
      d ∣ pair.1 ∧ (pair.1 : Real) < Q := by
  classical
  simp [strictDivisibleReducedFractionCarrier,
    mem_divisibleReducedFractionCarrier_iff, and_assoc]

/-- The literal fraction carrier in the second conclusion of published Lemma
10.6. It retains `0 <= a <= q`; coprimality leaves two exceptional endpoints
when `q = 1`. -/
noncomputable def strictDivisibleReducedFractionSourceCarrier
    (Q : Real) (d : Nat) : Finset (Nat × Nat) := by
  classical
  let N := Nat.floor Q
  exact ((Finset.Icc 1 N).product (Finset.range (N + 1))).filter fun pair =>
    (pair.1 : Real) < Q ∧ d ∣ pair.1 ∧
      pair.2 <= pair.1 ∧ pair.2.Coprime pair.1

theorem mem_strictDivisibleReducedFractionSourceCarrier_iff
    {Q : Real} {d : Nat} {pair : Nat × Nat} :
    pair ∈ strictDivisibleReducedFractionSourceCarrier Q d ↔
      1 <= pair.1 ∧ pair.1 <= Nat.floor Q ∧
      (pair.1 : Real) < Q ∧ d ∣ pair.1 ∧
      pair.2 <= pair.1 ∧ pair.2.Coprime pair.1 := by
  classical
  constructor
  · intro hpair
    rcases Finset.mem_filter.mp hpair with ⟨hproduct, hconditions⟩
    rcases Finset.mem_product.mp hproduct with ⟨hdenominator, hnumerator⟩
    rw [Finset.mem_Icc] at hdenominator
    exact ⟨hdenominator.1, hdenominator.2, hconditions.1,
      hconditions.2.1, hconditions.2.2.1, hconditions.2.2.2⟩
  · rintro ⟨hq1, hqQ, hqStrict, hdq, haq, hcoprime⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hq1, hqQ⟩,
        Finset.mem_range.mpr
          ((haq.trans hqQ).trans_lt (Nat.lt_succ_self _))⟩
    · exact ⟨hqStrict, hdq, haq, hcoprime⟩

end

end PrimesRestrictedDigits
