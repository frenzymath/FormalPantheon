import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearCauchy
import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearEnergy
import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearSum
import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearWeights

/-!
# Cauchy reduction of the exceptional bilinear sum

This file rearranges the literal source sum, checks the conjugation sign, and reduces its norm
to the nonnegative Fourier-weighted pair energy.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The exceptional bilinear expression restricted to an arbitrary finite
frequency carrier. -/
noncomputable def exceptionalBilinearSumOver
    (digit : Fin 10) (length : Nat)
    (A : Finset (Fin (10 ^ length))) (N M : Real)
    (alpha beta : Nat -> Complex)
    (gamma : Fin (10 ^ length) -> Complex) : Complex :=
  ∑ a ∈ A,
    ∑ n ∈ sourceFactorTenNaturalInterval N,
      ∑ m ∈ sourceFactorTenNaturalInterval M,
        (normalizedPaddedDigitFourierMagnitude
            digit length a.val : Complex) *
          alpha n * beta m * gamma a *
            majorArcPhase
              (-((a.val : Real) * (n : Real) * (m : Real) /
                ((10 ^ length : Nat) : Real)))

@[simp]
theorem exceptionalBilinearSumOver_exceptionalRationalFrequencies
    (digit : Fin 10) (length : Nat) (N M Q E : Real)
    (alpha beta : Nat -> Complex)
    (gamma : Fin (10 ^ length) -> Complex) :
    exceptionalBilinearSumOver digit length
        (exceptionalRationalFrequencies digit length Q E)
        N M alpha beta gamma =
      exceptionalBilinearSum digit length N M Q E alpha beta gamma :=
  rfl

/-- The frequency-pair energy after discarding one-bounded coefficients. -/
noncomputable def bilinearWeightedPairEnergy
    (digit : Fin 10) (length : Nat)
    (A : Finset (Fin (10 ^ length))) (N : Real) : Real :=
  ∑ pair ∈ A.product A,
    bilinearPairFourierWeight digit length pair *
      bilinearPairEnergy N pair.1 pair.2

theorem bilinearWeightedPairEnergy_nonneg
    (digit : Fin 10) (length : Nat)
    (A : Finset (Fin (10 ^ length))) {N : Real} (hN : 0 < N) :
    0 <= bilinearWeightedPairEnergy digit length A N := by
  apply Finset.sum_nonneg
  intro pair hpair
  exact mul_nonneg
    (bilinearPairFourierWeight_nonneg digit length pair)
    (bilinearPairEnergy_nonneg hN pair.1 pair.2)

private theorem exceptionalBilinearSumOver_eq_m_sum
    (digit : Fin 10) (length : Nat)
    (A : Finset (Fin (10 ^ length))) (N M : Real)
    (alpha beta : Nat -> Complex)
    (gamma : Fin (10 ^ length) -> Complex) :
    exceptionalBilinearSumOver digit length A N M alpha beta gamma =
      ∑ m ∈ sourceFactorTenNaturalInterval M, beta m *
        ∑ pair ∈ A.product (sourceFactorTenNaturalInterval N),
          ((normalizedPaddedDigitFourierMagnitude
              digit length pair.1.val : Complex) *
            alpha pair.2 * gamma pair.1) *
              majorArcPhase ((m : Real) *
                (-((pair.1.val : Real) * (pair.2 : Real) /
                  ((10 ^ length : Nat) : Real)))) := by
  rw [exceptionalBilinearSumOver, ← Finset.sum_product', Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pair hpair
  have hphase :
      (m : Real) *
          (-((pair.1.val : Real) * (pair.2 : Real) /
            ((10 ^ length : Nat) : Real))) =
        -((pair.1.val : Real) * (pair.2 : Real) * (m : Real) /
          ((10 ^ length : Nat) : Real)) := by ring
  rw [hphase]
  ring

private theorem bilinearCauchyCoefficient_norm_le
    (digit : Fin 10) (length : Nat)
    (alpha : Nat -> Complex)
    (gamma : Fin (10 ^ length) -> Complex)
    (halpha : ∀ n, ‖alpha n‖ <= 1)
    (hgamma : ∀ a, ‖gamma a‖ <= 1)
    (pair : Fin (10 ^ length) × Nat) :
    ‖(normalizedPaddedDigitFourierMagnitude
          digit length pair.1.val : Complex) *
        alpha pair.2 * gamma pair.1‖ <=
      normalizedPaddedDigitFourierMagnitude digit length pair.1.val := by
  let F := normalizedPaddedDigitFourierMagnitude digit length pair.1.val
  have hF : 0 <= F :=
    normalizedPaddedDigitFourierMagnitude_nonneg digit length pair.1.val
  change ‖(F : Complex) * alpha pair.2 * gamma pair.1‖ <= F
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hF]
  calc
    F * ‖alpha pair.2‖ * ‖gamma pair.1‖ <= F * 1 * 1 := by
      gcongr
      · exact halpha pair.2
      · exact hgamma pair.1
    _ = F := by ring

private theorem bilinearCauchyPhase_sub
    {length : Nat}
    (first second : Fin (10 ^ length) × Nat) :
    (-((second.1.val : Real) * (second.2 : Real) /
          ((10 ^ length : Nat) : Real))) -
        (-((first.1.val : Real) * (first.2 : Real) /
          ((10 ^ length : Nat) : Real))) =
      bilinearPairPhase first.1 second.1 first.2 second.2 := by
  rw [bilinearPairPhase, bilinearRelationPhase]
  ring

private theorem sum_bilinearPairKernel_eq_weightedPairEnergy
    (digit : Fin 10) (length : Nat)
    (A : Finset (Fin (10 ^ length))) (N : Real) :
    (∑ first ∈ A.product (sourceFactorTenNaturalInterval N),
      ∑ second ∈ A.product (sourceFactorTenNaturalInterval N),
        normalizedPaddedDigitFourierMagnitude digit length first.1.val *
          normalizedPaddedDigitFourierMagnitude digit length second.1.val *
          cappedNearestIntegerKernel
            (((10 ^ length : Nat) : Real) / N)
            (bilinearPairPhase first.1 second.1 first.2 second.2)) =
      bilinearWeightedPairEnergy digit length A N := by
  let I := sourceFactorTenNaturalInterval N
  let F : Fin (10 ^ length) -> Real := fun a =>
    normalizedPaddedDigitFourierMagnitude digit length a.val
  let W : Fin (10 ^ length) -> Fin (10 ^ length) -> Nat -> Nat -> Real :=
    fun a1 a2 n1 n2 =>
      cappedNearestIntegerKernel
        (((10 ^ length : Nat) : Real) / N)
        (bilinearPairPhase a1 a2 n1 n2)
  change (∑ first ∈ A.product I, ∑ second ∈ A.product I,
    F first.1 * F second.1 * W first.1 second.1 first.2 second.2) = _
  calc
    (∑ first ∈ A.product I, ∑ second ∈ A.product I,
        F first.1 * F second.1 *
          W first.1 second.1 first.2 second.2) =
        ∑ a1 ∈ A, ∑ n1 ∈ I, ∑ second ∈ A.product I,
          F a1 * F second.1 * W a1 second.1 n1 second.2 := by
      exact Finset.sum_product A I _
    _ = ∑ a1 ∈ A, ∑ n1 ∈ I, ∑ a2 ∈ A, ∑ n2 ∈ I,
        F a1 * F a2 * W a1 a2 n1 n2 := by
      apply Finset.sum_congr rfl
      intro a1 ha1
      apply Finset.sum_congr rfl
      intro n1 hn1
      exact Finset.sum_product A I _
    _ = ∑ a1 ∈ A, ∑ a2 ∈ A, ∑ n1 ∈ I, ∑ n2 ∈ I,
        F a1 * F a2 * W a1 a2 n1 n2 := by
      apply Finset.sum_congr rfl
      intro a1 ha1
      exact Finset.sum_comm
    _ = ∑ a1 ∈ A, ∑ a2 ∈ A,
        F a1 * F a2 * (∑ n1 ∈ I, ∑ n2 ∈ I, W a1 a2 n1 n2) := by
      apply Finset.sum_congr rfl
      intro a1 ha1
      apply Finset.sum_congr rfl
      intro a2 ha2
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n1 hn1
      rw [Finset.mul_sum]
    _ = ∑ pair ∈ A.product A,
        F pair.1 * F pair.2 *
          (∑ n1 ∈ I, ∑ n2 ∈ I, W pair.1 pair.2 n1 n2) := by
      exact (Finset.sum_product A A (fun pair =>
        F pair.1 * F pair.2 *
          (∑ n1 ∈ I, ∑ n2 ∈ I, W pair.1 pair.2 n1 n2))).symm
    _ = bilinearWeightedPairEnergy digit length A N := by
      rfl

private theorem bilinearSecondMoment_le_weightedPairEnergy
    (digit : Fin 10) (length : Nat)
    (A : Finset (Fin (10 ^ length))) {N M : Real}
    (hN : 1 <= N) (hM : 0 <= M)
    (hNM : N * M <= 1000 * ((10 ^ length : Nat) : Real))
    (alpha : Nat -> Complex)
    (gamma : Fin (10 ^ length) -> Complex)
    (halpha : ∀ n, ‖alpha n‖ <= 1)
    (hgamma : ∀ a, ‖gamma a‖ <= 1) :
    (∑ m ∈ sourceFactorTenNaturalInterval M,
      ‖∑ pair ∈ A.product (sourceFactorTenNaturalInterval N),
        ((normalizedPaddedDigitFourierMagnitude
            digit length pair.1.val : Complex) *
          alpha pair.2 * gamma pair.1) *
            majorArcPhase ((m : Real) *
              (-((pair.1.val : Real) * (pair.2 : Real) /
                ((10 ^ length : Nat) : Real))))‖ ^ 2) <=
      1000 * bilinearWeightedPairEnergy digit length A N := by
  let I := sourceFactorTenNaturalInterval N
  let P := A.product I
  let X : Real := ((10 ^ length : Nat) : Real)
  let L : Real := X / N
  let c : (Fin (10 ^ length) × Nat) -> Complex := fun pair =>
    (normalizedPaddedDigitFourierMagnitude
        digit length pair.1.val : Complex) *
      alpha pair.2 * gamma pair.1
  let theta : (Fin (10 ^ length) × Nat) -> Real := fun pair =>
    -((pair.1.val : Real) * (pair.2 : Real) / X)
  have hNPos : 0 < N := zero_lt_one.trans_le hN
  have hX : 0 < X := by dsimp only [X]; positivity
  have hL : 0 < L := div_pos hX hNPos
  have hML : M <= 1000 * L := by
    rw [show 1000 * L = (1000 * X) / N by
      dsimp only [L]
      ring]
    apply (le_div_iff₀ hNPos).2
    dsimp only [X]
    nlinarith
  have hraw := sum_norm_sq_sum_mul_phase_le
    (sourceFactorTenNaturalInterval M) P c theta
  refine hraw.trans ?_
  calc
    (∑ first ∈ P, ∑ second ∈ P,
        ‖c first‖ * ‖c second‖ *
          ‖∑ m ∈ sourceFactorTenNaturalInterval M,
            majorArcPhase ((m : Real) *
              (theta second - theta first))‖) <=
        ∑ first ∈ P, ∑ second ∈ P,
          1000 *
            (normalizedPaddedDigitFourierMagnitude
              digit length first.1.val *
             normalizedPaddedDigitFourierMagnitude
              digit length second.1.val *
             cappedNearestIntegerKernel L
              (bilinearPairPhase first.1 second.1
                first.2 second.2)) := by
      apply Finset.sum_le_sum
      intro first hfirst
      apply Finset.sum_le_sum
      intro second hsecond
      have hcFirst := bilinearCauchyCoefficient_norm_le
        digit length alpha gamma halpha hgamma first
      have hcSecond := bilinearCauchyCoefficient_norm_le
        digit length alpha gamma halpha hgamma second
      have hphase : theta second - theta first =
          bilinearPairPhase first.1 second.1 first.2 second.2 := by
        exact bilinearCauchyPhase_sub first second
      have hkernel := norm_phase_sum_sourceFactorTenNaturalInterval_le_kernel
        hL hM hML
        (theta := bilinearPairPhase first.1 second.1 first.2 second.2)
      rw [hphase]
      have hcFirstNonneg : 0 <= ‖c first‖ := norm_nonneg _
      have hcSecondNonneg : 0 <= ‖c second‖ := norm_nonneg _
      have hkernelNonneg : 0 <= cappedNearestIntegerKernel L
          (bilinearPairPhase first.1 second.1 first.2 second.2) :=
        cappedNearestIntegerKernel_nonneg hL.le _
      have hfirstFNonneg : 0 <= normalizedPaddedDigitFourierMagnitude
          digit length first.1.val :=
        normalizedPaddedDigitFourierMagnitude_nonneg _ _ _
      have hsecondFNonneg : 0 <= normalizedPaddedDigitFourierMagnitude
          digit length second.1.val :=
        normalizedPaddedDigitFourierMagnitude_nonneg _ _ _
      calc
        ‖c first‖ * ‖c second‖ *
            ‖∑ m ∈ sourceFactorTenNaturalInterval M,
              majorArcPhase ((m : Real) *
                bilinearPairPhase first.1 second.1 first.2 second.2)‖ <=
            (normalizedPaddedDigitFourierMagnitude
              digit length first.1.val *
             normalizedPaddedDigitFourierMagnitude
              digit length second.1.val) *
              (1000 * cappedNearestIntegerKernel L
                (bilinearPairPhase first.1 second.1 first.2 second.2)) := by
          calc
            ‖c first‖ * ‖c second‖ *
                ‖∑ m ∈ sourceFactorTenNaturalInterval M,
                  majorArcPhase ((m : Real) *
                    bilinearPairPhase first.1 second.1 first.2 second.2)‖ <=
                (normalizedPaddedDigitFourierMagnitude
                  digit length first.1.val *
                 normalizedPaddedDigitFourierMagnitude
                  digit length second.1.val) *
                  ‖∑ m ∈ sourceFactorTenNaturalInterval M,
                    majorArcPhase ((m : Real) *
                      bilinearPairPhase first.1 second.1 first.2 second.2)‖ := by
              apply mul_le_mul_of_nonneg_right
              · exact mul_le_mul hcFirst hcSecond hcSecondNonneg hfirstFNonneg
              · exact norm_nonneg _
            _ <= (normalizedPaddedDigitFourierMagnitude
                  digit length first.1.val *
                 normalizedPaddedDigitFourierMagnitude
                  digit length second.1.val) *
                (1000 * cappedNearestIntegerKernel L
                  (bilinearPairPhase first.1 second.1 first.2 second.2)) := by
              exact mul_le_mul_of_nonneg_left hkernel
                (mul_nonneg hfirstFNonneg hsecondFNonneg)
        _ = 1000 *
            (normalizedPaddedDigitFourierMagnitude
              digit length first.1.val *
             normalizedPaddedDigitFourierMagnitude
              digit length second.1.val *
             cappedNearestIntegerKernel L
              (bilinearPairPhase first.1 second.1 first.2 second.2)) := by ring
    _ = 1000 * bilinearWeightedPairEnergy digit length A N := by
      simp only [P, I, L, X]
      simp_rw [← Finset.mul_sum]
      rw [sum_bilinearPairKernel_eq_weightedPairEnergy]

/-- Exact interval-cardinality Cauchy bound. -/
theorem norm_exceptionalBilinearSumOver_le_sqrt_card_mul_energy
    (digit : Fin 10) (length : Nat)
    (A : Finset (Fin (10 ^ length))) {N M : Real}
    (hN : 1 <= N) (hM : 0 <= M)
    (hNM : N * M <= 1000 * ((10 ^ length : Nat) : Real))
    (alpha beta : Nat -> Complex)
    (gamma : Fin (10 ^ length) -> Complex)
    (halpha : ∀ n, ‖alpha n‖ <= 1)
    (hbeta : ∀ m, ‖beta m‖ <= 1)
    (hgamma : ∀ a, ‖gamma a‖ <= 1) :
    ‖exceptionalBilinearSumOver
        digit length A N M alpha beta gamma‖ <=
      Real.sqrt ((sourceFactorTenNaturalInterval M).card : Real) *
        Real.sqrt (1000 * bilinearWeightedPairEnergy
          digit length A N) := by
  rw [exceptionalBilinearSumOver_eq_m_sum]
  let innerSum : Nat -> Complex := fun m =>
    ∑ pair ∈ A.product (sourceFactorTenNaturalInterval N),
      ((normalizedPaddedDigitFourierMagnitude
          digit length pair.1.val : Complex) *
        alpha pair.2 * gamma pair.1) *
          majorArcPhase ((m : Real) *
            (-((pair.1.val : Real) * (pair.2 : Real) /
              ((10 ^ length : Nat) : Real))))
  have hcauchy := norm_sum_mul_le_sqrt_mul_sqrt
    (sourceFactorTenNaturalInterval M) beta innerSum
  refine hcauchy.trans ?_
  have hbetaSq :
      (∑ m ∈ sourceFactorTenNaturalInterval M, ‖beta m‖ ^ 2) <=
        ((sourceFactorTenNaturalInterval M).card : Real) := by
    calc
      (∑ m ∈ sourceFactorTenNaturalInterval M, ‖beta m‖ ^ 2) <=
          ∑ _m ∈ sourceFactorTenNaturalInterval M, (1 : Real) := by
        apply Finset.sum_le_sum
        intro m hm
        nlinarith [hbeta m, norm_nonneg (beta m)]
      _ = ((sourceFactorTenNaturalInterval M).card : Real) := by simp
  have hsecond := bilinearSecondMoment_le_weightedPairEnergy
    digit length A hN hM hNM alpha gamma halpha hgamma
  have hsqrtBeta := Real.sqrt_le_sqrt hbetaSq
  have hsqrtSecond := Real.sqrt_le_sqrt hsecond
  exact mul_le_mul hsqrtBeta hsqrtSecond (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

/-- Source-scale Cauchy bound, using `M <= 1000X/N`. -/
theorem norm_exceptionalBilinearSumOver_le_sqrt_scale_mul_energy
    (digit : Fin 10) (length : Nat)
    (A : Finset (Fin (10 ^ length))) {N M : Real}
    (hN : 1 <= N) (hM : 1 <= M)
    (hNM : N * M <= 1000 * ((10 ^ length : Nat) : Real))
    (alpha beta : Nat -> Complex)
    (gamma : Fin (10 ^ length) -> Complex)
    (halpha : ∀ n, ‖alpha n‖ <= 1)
    (hbeta : ∀ m, ‖beta m‖ <= 1)
    (hgamma : ∀ a, ‖gamma a‖ <= 1) :
    ‖exceptionalBilinearSumOver
        digit length A N M alpha beta gamma‖ <=
      Real.sqrt
          (1000 * ((10 ^ length : Nat) : Real) / N) *
        Real.sqrt (1000 * bilinearWeightedPairEnergy
          digit length A N) := by
  have hbase := norm_exceptionalBilinearSumOver_le_sqrt_card_mul_energy
    digit length A hN (zero_le_one.trans hM) hNM
      alpha beta gamma halpha hbeta hgamma
  refine hbase.trans ?_
  have hNPos : 0 < N := zero_lt_one.trans_le hN
  have hcardM : ((sourceFactorTenNaturalInterval M).card : Real) <=
      1000 * ((10 ^ length : Nat) : Real) / N := by
    calc
      ((sourceFactorTenNaturalInterval M).card : Real) <= M :=
        card_sourceFactorTenNaturalInterval_le (zero_le_one.trans hM)
      _ <= 1000 * ((10 ^ length : Nat) : Real) / N := by
        apply (le_div_iff₀ hNPos).2
        nlinarith
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcardM)
    (Real.sqrt_nonneg _)

end PrimesRestrictedDigits
