import BoundedGaps.Maynard.MaynardS1StarredSummandBound

noncomputable section

/-!
# An explicit bound for the S1 cross correction

The exact rough starred sum is restricted to pre-sieved common variables.
Its absolute value then factors into the rough cross tail and the common
reciprocal-totient mean.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance crossCorrectionBoundDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def nontrivialStarredRoughPreSievedAuxiliaryYSum
    (H : Finset ℕ) (R W D : ℕ) (y : (H → ℕ) → ℝ) : ℝ :=
  ∑ s ∈ roughCrossTupleSupport H D R,
    if s ≠ oneCrossMoebiusTuple H then
      crossMoebiusTupleTerm H s *
        ∑ u ∈ preSievedCommonTupleSupport H W R,
          if IsStarredCrossTuple H u s then
            (∏ h : H, (Nat.totient (u h) : ℝ)) *
              leftCrossYFactor H y u s * rightCrossYFactor H y u s
          else 0
    else 0

theorem nontrivialStarredRoughAuxiliaryYSum_eq_preSieved
    {H : Finset ℕ} {R W D : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) :
    nontrivialStarredRoughAuxiliaryYSum H R D y =
      nontrivialStarredRoughPreSievedAuxiliaryYSum H R W D y := by
  classical
  unfold nontrivialStarredRoughAuxiliaryYSum
    nontrivialStarredRoughPreSievedAuxiliaryYSum
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hsNe : s ≠ oneCrossMoebiusTuple H
  · rw [if_pos hsNe, if_pos hsNe]
    congr 1
    apply (Finset.sum_subset
      (preSievedCommonTupleSupport_subset_maynardDivisorTupleBox H W R) ?_).symm
    intro u huBox huNotPreSieved
    by_cases hstar : IsStarredCrossTuple H u s
    · rw [if_pos hstar]
      have hl : leftCrossYFactor H y u s = 0 := by
        by_contra hl
        exact huNotPreSieved
          (preSievedCommonTupleSupport_of_leftYFactor_ne_zero hy huBox hl)
      simp [hl]
    · rw [if_neg hstar]
  · rw [if_neg hsNe, if_neg hsNe]

theorem incompatibleSum_eq_neg_roughPreSievedAuxiliaryYSum
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (hR : 0 < R)
    (hy : IsSupportedMaynardY H R (primorial D) y) :
    incompatibleDivisorPairCommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R (primorial D))
        (maynardCoefficientFromY H R (primorial D) y) =
      -nontrivialStarredRoughPreSievedAuxiliaryYSum
        H R (primorial D) D y := by
  rw [incompatibleSum_eq_neg_starredAuxiliaryYSum hy]
  rw [nontrivialStarredAuxiliaryYSum_eq_rough hR hy]
  rw [nontrivialStarredRoughAuxiliaryYSum_eq_preSieved hy]

theorem nontrivialStarredRoughPreSievedAuxiliaryYSum_eq_erase
    (H : Finset ℕ) (R W D : ℕ) (y : (H → ℕ) → ℝ) :
    nontrivialStarredRoughPreSievedAuxiliaryYSum H R W D y =
      ∑ s ∈ (roughCrossTupleSupport H D R).erase
          (oneCrossMoebiusTuple H),
        crossMoebiusTupleTerm H s *
          ∑ u ∈ preSievedCommonTupleSupport H W R,
            if IsStarredCrossTuple H u s then
              (∏ h : H, (Nat.totient (u h) : ℝ)) *
                leftCrossYFactor H y u s * rightCrossYFactor H y u s
            else 0 := by
  classical
  let f := fun s =>
    if s ≠ oneCrossMoebiusTuple H then
      crossMoebiusTupleTerm H s *
        ∑ u ∈ preSievedCommonTupleSupport H W R,
          if IsStarredCrossTuple H u s then
            (∏ h : H, (Nat.totient (u h) : ℝ)) *
              leftCrossYFactor H y u s * rightCrossYFactor H y u s
          else 0
    else 0
  have hone := oneCrossMoebiusTuple_mem_roughCrossTupleSupport H D R
  have hsplit := Finset.sum_erase_add (s := roughCrossTupleSupport H D R)
    (f := f) hone
  have hfone : f (oneCrossMoebiusTuple H) = 0 := by
    simp [f]
  unfold nontrivialStarredRoughPreSievedAuxiliaryYSum
  rw [hfone, add_zero] at hsplit
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro s hs
  have hsNe := (Finset.mem_erase.mp hs).1
  simp [f, hsNe]

theorem abs_fixedRoughCrossInnerSum_le
    {H : Finset ℕ} {R W D : ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hs : s ∈ roughCrossTupleSupport H D R) :
    |crossMoebiusTupleTerm H s *
        ∑ u ∈ preSievedCommonTupleSupport H W R,
          if IsStarredCrossTuple H u s then
            (∏ h : H, (Nat.totient (u h) : ℝ)) *
              leftCrossYFactor H y u s * rightCrossYFactor H y u s
          else 0| ≤
      B ^ 2 * crossTotientSquareWeight H s *
        commonTupleInvTotientMean H W R := by
  rw [Finset.mul_sum]
  calc
    |∑ u ∈ preSievedCommonTupleSupport H W R,
        crossMoebiusTupleTerm H s *
          (if IsStarredCrossTuple H u s then
            (∏ h : H, (Nat.totient (u h) : ℝ)) *
              leftCrossYFactor H y u s * rightCrossYFactor H y u s
          else 0)| ≤
        ∑ u ∈ preSievedCommonTupleSupport H W R,
          |crossMoebiusTupleTerm H s *
            (if IsStarredCrossTuple H u s then
              (∏ h : H, (Nat.totient (u h) : ℝ)) *
                leftCrossYFactor H y u s * rightCrossYFactor H y u s
            else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ preSievedCommonTupleSupport H W R,
          B ^ 2 * crossTotientSquareWeight H s *
            ((1 : ℝ) / commonTotientProduct H u) := by
      apply Finset.sum_le_sum
      intro u hu
      by_cases hstar : IsStarredCrossTuple H u s
      · rw [if_pos hstar]
        simpa [commonTotientProduct, mul_assoc] using
          abs_starredCrossYSummand_le_separated
            hB hyBound hu hs hstar
      · rw [if_neg hstar]
        rw [mul_zero, abs_zero]
        have hsWeight : 0 ≤ crossTotientSquareWeight H s := by
          unfold crossTotientSquareWeight
          positivity
        have huWeight : 0 ≤
            (1 : ℝ) / commonTotientProduct H u := by positivity
        exact mul_nonneg (mul_nonneg (sq_nonneg B) hsWeight) huWeight
    _ = B ^ 2 * crossTotientSquareWeight H s *
        commonTupleInvTotientMean H W R := by
      unfold commonTupleInvTotientMean
      rw [Finset.mul_sum]

theorem abs_nontrivialStarredRoughPreSievedAuxiliaryYSum_le
    {H : Finset ℕ} {R W D : ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B) :
    |nontrivialStarredRoughPreSievedAuxiliaryYSum H R W D y| ≤
      B ^ 2 * roughCrossTupleTotientSquareTail H D R *
        commonTupleInvTotientMean H W R := by
  rw [nontrivialStarredRoughPreSievedAuxiliaryYSum_eq_erase]
  calc
    |∑ s ∈ (roughCrossTupleSupport H D R).erase
        (oneCrossMoebiusTuple H),
        crossMoebiusTupleTerm H s *
          ∑ u ∈ preSievedCommonTupleSupport H W R,
            if IsStarredCrossTuple H u s then
              (∏ h : H, (Nat.totient (u h) : ℝ)) *
                leftCrossYFactor H y u s * rightCrossYFactor H y u s
            else 0| ≤
        ∑ s ∈ (roughCrossTupleSupport H D R).erase
          (oneCrossMoebiusTuple H),
          |crossMoebiusTupleTerm H s *
            ∑ u ∈ preSievedCommonTupleSupport H W R,
              if IsStarredCrossTuple H u s then
                (∏ h : H, (Nat.totient (u h) : ℝ)) *
                  leftCrossYFactor H y u s * rightCrossYFactor H y u s
              else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ (roughCrossTupleSupport H D R).erase
          (oneCrossMoebiusTuple H),
          B ^ 2 * crossTotientSquareWeight H s *
            commonTupleInvTotientMean H W R := by
      apply Finset.sum_le_sum
      intro s hs
      exact abs_fixedRoughCrossInnerSum_le hB hyBound
        (Finset.mem_of_mem_erase hs)
    _ = B ^ 2 * roughCrossTupleTotientSquareTail H D R *
        commonTupleInvTotientMean H W R := by
      unfold roughCrossTupleTotientSquareTail
      nth_rw 1 [← Finset.sum_mul]
      rw [Finset.mul_sum]

theorem abs_incompatibleSum_le_crossTail_mul_commonMean
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    (hy : IsSupportedMaynardY H R (primorial D) y) :
    |incompatibleDivisorPairCommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R (primorial D))
        (maynardCoefficientFromY H R (primorial D) y)| ≤
      B ^ 2 * roughCrossTupleTotientSquareTail H D R *
        commonTupleInvTotientMean H (primorial D) R := by
  rw [incompatibleSum_eq_neg_roughPreSievedAuxiliaryYSum hR hy, abs_neg]
  exact abs_nontrivialStarredRoughPreSievedAuxiliaryYSum_le hB hyBound

theorem abs_incompatibleSum_le_explicit
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hR : 0 < R) (hD : 0 < D) (hB : 0 ≤ B)
    (hyBound : ∀ r, |y r| ≤ B)
    (hy : IsSupportedMaynardY H R (primorial D) y) :
    |incompatibleDivisorPairCommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R (primorial D))
        (maynardCoefficientFromY H R (primorial D) y)| ≤
      B ^ 2 *
        ((8 * Real.exp 8 / (D : ℝ)) *
          ((offDiagonalPairs H).card : ℝ) *
            (Real.exp 8) ^ ((offDiagonalPairs H).card - 1)) *
        (squarefreeCoprimeInvTotientMean (primorial D) R) ^
          Fintype.card H := by
  calc
    |incompatibleDivisorPairCommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R (primorial D))
        (maynardCoefficientFromY H R (primorial D) y)| ≤
        B ^ 2 * roughCrossTupleTotientSquareTail H D R *
          commonTupleInvTotientMean H (primorial D) R :=
      abs_incompatibleSum_le_crossTail_mul_commonMean hR hB hyBound hy
    _ ≤ B ^ 2 *
        ((8 * Real.exp 8 / (D : ℝ)) *
          ((offDiagonalPairs H).card : ℝ) *
            (Real.exp 8) ^ ((offDiagonalPairs H).card - 1)) *
        (squarefreeCoprimeInvTotientMean (primorial D) R) ^
          Fintype.card H := by
      have hcross := roughCrossTupleTotientSquareTail_le
        (H := H) (Q := R) hD
      have hcommon := commonTupleInvTotientMean_le H (primorial D) R
      have hcommonNonneg : 0 ≤
          commonTupleInvTotientMean H (primorial D) R := by
        unfold commonTupleInvTotientMean
        apply Finset.sum_nonneg
        intro u hu
        positivity
      calc
        B ^ 2 * roughCrossTupleTotientSquareTail H D R *
            commonTupleInvTotientMean H (primorial D) R ≤
            B ^ 2 *
              ((8 * Real.exp 8 / (D : ℝ)) *
                ((offDiagonalPairs H).card : ℝ) *
                  (Real.exp 8) ^ ((offDiagonalPairs H).card - 1)) *
              commonTupleInvTotientMean H (primorial D) R := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcross (sq_nonneg B)) hcommonNonneg
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_left hcommon (by positivity)

theorem abs_incompatibleSum_le_log
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hR : 0 < R) (hD : 0 < D) (hB : 0 ≤ B)
    (hWL : (primorial D : ℝ) ≤ 1 + Real.log R)
    (hyBound : ∀ r, |y r| ≤ B)
    (hy : IsSupportedMaynardY H R (primorial D) y) :
    |incompatibleDivisorPairCommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R (primorial D))
        (maynardCoefficientFromY H R (primorial D) y)| ≤
      B ^ 2 *
        ((8 * Real.exp 8 / (D : ℝ)) *
          ((offDiagonalPairs H).card : ℝ) *
            (Real.exp 8) ^ ((offDiagonalPairs H).card - 1)) *
        (8 * ((Nat.totient (primorial D) : ℝ) / primorial D) *
          (1 + Real.log R)) ^ Fintype.card H := by
  calc
    |incompatibleDivisorPairCommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R (primorial D))
        (maynardCoefficientFromY H R (primorial D) y)| ≤
        B ^ 2 *
          ((8 * Real.exp 8 / (D : ℝ)) *
            ((offDiagonalPairs H).card : ℝ) *
              (Real.exp 8) ^ ((offDiagonalPairs H).card - 1)) *
          (squarefreeCoprimeInvTotientMean (primorial D) R) ^
            Fintype.card H :=
      abs_incompatibleSum_le_explicit hR hD hB hyBound hy
    _ ≤ _ := by
      have hscalar := squarefreeCoprimeInvTotientMean_le_log
        (primorial_pos D) hWL
      have hscalarNonneg : 0 ≤
          squarefreeCoprimeInvTotientMean (primorial D) R := by
        unfold squarefreeCoprimeInvTotientMean
        apply Finset.sum_nonneg
        intro n hn
        split <;> positivity
      have hpow := pow_le_pow_left₀ hscalarNonneg hscalar (Fintype.card H)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)

end BoundedGaps.Maynard
