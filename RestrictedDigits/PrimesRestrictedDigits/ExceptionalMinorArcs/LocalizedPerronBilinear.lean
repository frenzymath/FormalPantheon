import PrimesRestrictedDigits.ExceptionalMinorArcs.LocalizedRationalCellScales
import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearMain

/-!
# Fixed-height Perron insertion into the exceptional bilinear bound

This is the fixed-height part of the proof of published Proposition 9.3. It restores the
complex powers omitted from the printed display, normalizes the prime-product coefficients,
and applies repaired Lemma 13.1 on an active canonical cell.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The localized split-prime sum with both Perron complex powers present. -/
def localizedSplitPrimePerronBilinearSum
    (digit : Fin 10) (length : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (S : Finset (Fin (10 ^ length)))
    (bandKey productKey : Nat × Nat) (s : Complex)
    (gamma : Fin (10 ^ length) → Complex) : Complex :=
  localizedExceptionalBilinearSum digit length S bandKey productKey
    (fun n =>
      (selectedProjectedPrimeWeightAtProduct
        (10 ^ length) a delta I n : Complex) / (n : Complex) ^ s)
    (fun m =>
      (complementaryLastPrimeWeightAtProduct
        (10 ^ length) a delta eta I m : Complex) / (m : Complex) ^ s)
    gamma

/-- The same sum after dividing the two prime weights by their explicit
factorial-logarithm caps. -/
def localizedNormalizedSplitPrimePerronBilinearSum
    (digit : Fin 10) (length : Nat) {k : Nat} (a : Fin k → Real)
    (delta eta : Real) (I : Finset (Fin k))
    (S : Finset (Fin (10 ^ length)))
    (bandKey productKey : Nat × Nat) (s : Complex)
    (gamma : Fin (10 ^ length) → Complex) : Complex :=
  localizedExceptionalBilinearSum digit length S bandKey productKey
    (normalizedPerronCoefficient
      (selectedProjectedPrimeWeightAtProduct
        (10 ^ length) a delta I)
      (selectedPrimePerronCoefficientCap (10 ^ length) I) s)
    (normalizedPerronCoefficient
      (complementaryLastPrimeWeightAtProduct
        (10 ^ length) a delta eta I)
      (complementaryPrimePerronCoefficientCap (10 ^ length) I) s)
    gamma

private theorem localizedExceptionalBilinearSum_mul_coefficients
    (digit : Fin 10) (length : Nat)
    (S : Finset (Fin (10 ^ length))) (bandKey productKey : Nat × Nat)
    (A B : Complex) (alpha beta : Nat → Complex)
    (gamma : Fin (10 ^ length) → Complex) :
    localizedExceptionalBilinearSum digit length S bandKey productKey
        (fun n => A * alpha n) (fun m => B * beta m) gamma =
      (A * B) * localizedExceptionalBilinearSum
        digit length S bandKey productKey alpha beta gamma := by
  unfold localizedExceptionalBilinearSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Restoring both coefficient caps converts the normalized localized sum
into the literal fixed-height Perron sum. -/
theorem localizedSplitPrimePerronBilinearSum_eq_caps_mul
    {digit : Fin 10} {length k : Nat} {a : Fin k → Real}
    {delta eta : Real} {I : Finset (Fin k)}
    {S : Finset (Fin (10 ^ length))} {bandKey productKey : Nat × Nat}
    {s : Complex} {gamma : Fin (10 ^ length) → Complex}
    (hlength : 0 < length) :
    localizedSplitPrimePerronBilinearSum digit length a delta eta I S
        bandKey productKey s gamma =
      ((selectedPrimePerronCoefficientCap (10 ^ length) I : Real) : Complex) *
        (complementaryPrimePerronCoefficientCap
          (10 ^ length) I : Complex) *
        localizedNormalizedSplitPrimePerronBilinearSum digit length a
          delta eta I S bandKey productKey s gamma := by
  have hX : 1 < 10 ^ length :=
    Nat.one_lt_pow hlength.ne' (by norm_num)
  let A := selectedPrimePerronCoefficientCap (10 ^ length) I
  let B := complementaryPrimePerronCoefficientCap (10 ^ length) I
  have hA : 0 < A := selectedPrimePerronCoefficientCap_pos hX I
  have hB : 0 < B := complementaryPrimePerronCoefficientCap_pos hX I
  have halpha : (fun n =>
      (selectedProjectedPrimeWeightAtProduct
        (10 ^ length) a delta I n : Complex) / (n : Complex) ^ s) =
      fun n => (A : Complex) * normalizedPerronCoefficient
        (selectedProjectedPrimeWeightAtProduct
          (10 ^ length) a delta I) A s n := by
    funext n
    exact (bound_mul_normalizedPerronCoefficient (n := n) hA).symm
  have hbeta : (fun m =>
      (complementaryLastPrimeWeightAtProduct
        (10 ^ length) a delta eta I m : Complex) / (m : Complex) ^ s) =
      fun m => (B : Complex) * normalizedPerronCoefficient
        (complementaryLastPrimeWeightAtProduct
          (10 ^ length) a delta eta I) B s m := by
    funext m
    exact (bound_mul_normalizedPerronCoefficient (n := m) hB).symm
  rw [localizedSplitPrimePerronBilinearSum,
    localizedNormalizedSplitPrimePerronBilinearSum, halpha, hbeta]
  simpa only [A, B, mul_assoc] using
    localizedExceptionalBilinearSum_mul_coefficients
      digit length S bandKey productKey (A : Complex) (B : Complex)
        (normalizedPerronCoefficient
          (selectedProjectedPrimeWeightAtProduct
            (10 ^ length) a delta I) A s)
        (normalizedPerronCoefficient
          (complementaryLastPrimeWeightAtProduct
            (10 ^ length) a delta eta I) B s) gamma

/-- Repaired Lemma 13.1 applied to one active split-prime cell at a fixed
Perron height. The constants and saving are uniform in every later
parameter. -/
theorem exists_localizedSplitPrimePerronBilinearBound :
    ∃ C : Real, 0 < C ∧ ∃ logLoss length0 : Nat,
      ∀ length : Nat, length0 ≤ length →
      ∀ (digit : Fin 10) (k : Nat) (a : Fin k → Real)
        (delta eta mu : Real) (I : Finset (Fin k))
        (S : Finset (Fin (10 ^ length)))
        (bandKey productKey : Nat × Nat) (s : Complex)
        (gamma : Fin (10 ^ length) → Complex),
        let X : Real := ((10 ^ length : Nat) : Real)
        let Q := exceptionalDirichletDenominatorScaleAt
          (10 ^ length) bandKey.1
        let E := exceptionalDirichletErrorScaleAt
          (10 ^ length) bandKey.2
        0 ≤ delta →
        ((k + 1 : Nat) : Real) * delta + 1 / (length : Real) ≤ mu →
        ((∑ i ∈ I, a i) ∈
            Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
          (∑ i ∈ I, a i) ∈
            Set.Icc (23 / 40 + mu) (16 / 25 - mu)) →
        S ⊆ genericExceptionalFrequencies digit length →
        IsActiveSplitPrimeCell length a delta eta I productKey →
        0 ≤ s.re →
        (∀ h, ‖gamma h‖ ≤ 1) →
        ‖localizedSplitPrimePerronBilinearSum digit length a delta eta I S
          bandKey productKey s gamma‖ ≤
          selectedPrimePerronCoefficientCap (10 ^ length) I *
            complementaryPrimePerronCoefficientCap (10 ^ length) I *
            (C * X * Real.log X ^ logLoss /
              (Q + E) ^ (latticeSumSaving / 10)) := by
  obtain ⟨C, hC, logLoss, sourceLength, hsource⟩ :=
    exists_exceptionalBilinearSumBound
  refine ⟨C, hC, logLoss, max sourceLength 1, ?_⟩
  intro length hlength digit k a delta eta mu I S bandKey productKey s gamma
  dsimp only
  intro hdelta hmargin ht hS hactive hs hgamma
  have hsourceLength : sourceLength ≤ length :=
    (le_max_left sourceLength 1).trans hlength
  have hlengthOne : 1 ≤ length :=
    (le_max_right sourceLength 1).trans hlength
  have hlengthPos : 0 < length := Nat.zero_lt_of_lt hlengthOne
  let X : Real := ((10 ^ length : Nat) : Real)
  let Q := exceptionalDirichletDenominatorScaleAt
    (10 ^ length) bandKey.1
  let E := exceptionalDirichletErrorScaleAt
    (10 ^ length) bandKey.2
  let A := selectedPrimePerronCoefficientCap (10 ^ length) I
  let B := complementaryPrimePerronCoefficientCap (10 ^ length) I
  have hXOne : 1 < 10 ^ length :=
    Nat.one_lt_pow hlengthPos.ne' (by norm_num)
  have hA : 0 < A := selectedPrimePerronCoefficientCap_pos hXOne I
  have hB : 0 < B := complementaryPrimePerronCoefficientCap_pos hXOne I
  by_cases hfreq : (exceptionalDirichletBandFiber S bandKey).Nonempty
  · have hscales := exceptionalDirichletBandFiber_scale_bounds
      hlengthPos hfreq
    dsimp only [X, Q, E] at hscales
    have hconvenient := activeSplitPrimeCell_convenient_dichotomy
      hlengthPos hdelta hmargin ht hactive
    have hNM := activeSplitPrimeCell_scaleProduct_le_thousand
      hlengthPos hactive
    let alpha := normalizedPerronCoefficient
      (selectedProjectedPrimeWeightAtProduct
        (10 ^ length) a delta I) A s
    let beta := normalizedPerronCoefficient
      (complementaryLastPrimeWeightAtProduct
        (10 ^ length) a delta eta I) B s
    have halpha (n : Nat)
        (hn : n ∈ splitProductCoordinateFiber length productKey.1) :
        ‖alpha n‖ ≤ 1 := by
      exact norm_normalizedSelectedPrimePerronCoefficient_le_one
        hlengthPos hn hs
    have hbeta (m : Nat)
        (hm : m ∈ splitProductCoordinateFiber length productKey.2) :
        ‖beta m‖ ≤ 1 := by
      exact norm_normalizedComplementaryPrimePerronCoefficient_le_one
        hlengthPos hm hs
    have hmaskedGamma (h : Fin (10 ^ length)) :
        ‖exceptionalDirichletBandMask S bandKey gamma h‖ ≤ 1 :=
      norm_exceptionalDirichletBandMask_le_one
        (fun h hh => hgamma h) h
    have hnormalized :
        ‖localizedNormalizedSplitPrimePerronBilinearSum digit length a
          delta eta I S bandKey productKey s gamma‖ ≤
          C * X * Real.log X ^ logLoss /
            (Q + E) ^ (latticeSumSaving / 10) := by
      rcases hconvenient with hfirst | hsecond
      · rw [localizedNormalizedSplitPrimePerronBilinearSum,
          localizedExceptionalBilinearSum_eq_exceptionalBilinearSum
            hlengthPos hS]
        exact hsource length hsourceLength digit
          (splitProductScaleAt productKey.1)
          (splitProductScaleAt productKey.2) Q E
          (splitProductCoordinateMask length productKey.1 alpha)
          (splitProductCoordinateMask length productKey.2 beta)
          (exceptionalDirichletBandMask S bandKey gamma)
          (one_le_splitProductScaleAt _)
          (one_le_splitProductScaleAt _) hscales.1 hscales.2.2.1
          hfirst.1 hfirst.2 hscales.2.1 hNM hscales.2.2.2.1
          hscales.2.2.2.2
          (norm_splitProductCoordinateMask_le_one halpha)
          (norm_splitProductCoordinateMask_le_one hbeta)
          hmaskedGamma
      · rw [localizedNormalizedSplitPrimePerronBilinearSum,
          localizedExceptionalBilinearSum_swap,
          localizedExceptionalBilinearSum_eq_exceptionalBilinearSum
            hlengthPos hS]
        have hNM' : splitProductScaleAt productKey.2 *
            splitProductScaleAt productKey.1 ≤ 1000 * X := by
          simpa only [mul_comm] using hNM
        exact hsource length hsourceLength digit
          (splitProductScaleAt productKey.2)
          (splitProductScaleAt productKey.1) Q E
          (splitProductCoordinateMask length productKey.2 beta)
          (splitProductCoordinateMask length productKey.1 alpha)
          (exceptionalDirichletBandMask S bandKey gamma)
          (one_le_splitProductScaleAt _)
          (one_le_splitProductScaleAt _) hscales.1 hscales.2.2.1
          hsecond.1 hsecond.2 hscales.2.1 hNM' hscales.2.2.2.1
          hscales.2.2.2.2
          (norm_splitProductCoordinateMask_le_one hbeta)
          (norm_splitProductCoordinateMask_le_one halpha)
          hmaskedGamma
    rw [localizedSplitPrimePerronBilinearSum_eq_caps_mul hlengthPos,
      norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hA.le, Real.norm_of_nonneg hB.le]
    exact mul_le_mul_of_nonneg_left hnormalized (mul_nonneg hA.le hB.le)
  · have hempty : exceptionalDirichletBandFiber S bandKey = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hfreq
    rw [localizedSplitPrimePerronBilinearSum,
      localizedExceptionalBilinearSum]
    simp only [hempty, Finset.sum_empty, norm_zero]
    have hQ : 0 ≤ Q := by
      dsimp only [Q, exceptionalDirichletDenominatorScaleAt]
      exact le_min (by positivity) (Real.sqrt_nonneg _)
    have hE : 0 ≤ E := by
      dsimp only [E]
      cases bandKey.2 <;>
        simp [exceptionalDirichletErrorScaleAt]; positivity
    have hlog : 0 ≤ Real.log X := by
      apply (Real.log_pos ?_).le
      dsimp only [X]
      exact_mod_cast hXOne
    exact mul_nonneg (mul_nonneg hA.le hB.le)
      (div_nonneg
        (mul_nonneg (mul_nonneg hC.le (by positivity))
          (pow_nonneg hlog logLoss))
        (Real.rpow_nonneg (add_nonneg hQ hE) _))

end

end PrimesRestrictedDigits
