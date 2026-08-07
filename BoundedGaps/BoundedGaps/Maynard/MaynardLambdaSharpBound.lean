import BoundedGaps.Maynard.MaynardLambdaDivisorEncoding

noncomputable section

/-!
# The sharp logarithmic Maynard coefficient bound

Maynard2013v3, equation `eq:LambdaSize` (source lines 304--316), absorbs the
fixed divisor product into one squarefree `tau_k(u) / phi(u)` sum. This file
completes that reindex and combines it with the logarithmic scalar majorant.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.omega BigOperators
local instance sharpLambdaDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem lambdaQuotientWeightSum_le_squarefreeTauFirstMean
    {H : Finset ℕ} {R W : ℕ} {d : H → ℕ}
    (hH : H.Nonempty) (hd : IsMaynardDivisorTuple H R W d) :
    lambdaQuotientWeightSum H R d ≤
      squarefreeTauFirstMean (Fintype.card H) R := by
  classical
  let k := Fintype.card H
  let T := (lambdaQuotientTupleSupport H R d).image (divisorTupleProduct H)
  let P := lambdaDivisorQuotientProductSupport H R d
  have hk : 1 ≤ k := by
    letI : Nonempty H := hH.to_subtype
    exact Fintype.card_pos
  calc
    lambdaQuotientWeightSum H R d ≤
        ∑ t ∈ T, ((k ^ ω t : ℕ) : ℝ) *
          ((divisorTupleProduct H d : ℝ) /
            (Nat.totient (divisorTupleProduct H d * t) : ℝ)) :=
      lambdaQuotientWeightSum_le_tau_fiber_sum hd
    _ = ∑ t ∈ T, ∑ a ∈ (divisorTupleProduct H d).divisors,
          ((k ^ ω t : ℕ) : ℝ) / (Nat.totient (a * t) : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htData := lambdaQuotientProduct_image_data hd ht
      exact squarefree_coprime_tau_div_totient_expansion hd.2.2
        htData.2.2.1 htData.2.2.2
    _ = ∑ x ∈ P, ((k ^ ω x.1 : ℕ) : ℝ) /
          (Nat.totient (lambdaDivisorQuotientEncoding x) : ℝ) := by
      unfold P lambdaDivisorQuotientProductSupport
      rw [Finset.sum_product]
      rfl
    _ ≤ ∑ x ∈ P, ((k ^ ω (lambdaDivisorQuotientEncoding x) : ℕ) : ℝ) /
          (Nat.totient (lambdaDivisorQuotientEncoding x) : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      exact lambdaDivisorQuotient_tauWeight_le hk hd hx
    _ = ∑ u ∈ P.image lambdaDivisorQuotientEncoding,
          ((k ^ ω u : ℕ) : ℝ) / (Nat.totient u : ℝ) := by
      rw [Finset.sum_image (lambdaDivisorQuotientEncoding_injOn hd)]
    _ = ∑ u ∈ P.image lambdaDivisorQuotientEncoding,
          if Squarefree u then
            ((k ^ ω u : ℕ) : ℝ) / (Nat.totient u : ℝ)
          else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [if_pos (squarefree_of_mem_lambdaDivisorQuotientEncoding_image hd hu)]
    _ ≤ ∑ u ∈ Finset.Icc 1 R,
          if Squarefree u then
            ((k ^ ω u : ℕ) : ℝ) / (Nat.totient u : ℝ)
          else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (lambdaDivisorQuotientEncoding_image_subset_Icc hd)
      intro u hu hnot
      split_ifs <;> positivity
    _ = squarefreeTauFirstMean (Fintype.card H) R := rfl

theorem abs_maynardCoefficient_le_sharp_log
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ)
    (d : H → ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ x, |F x| ≤ B) (hH : H.Nonempty)
    (hd : d ∈ maynardDivisorTupleSupport H R W) :
    |maynardCoefficient H R W F d| ≤
      B * (1 + Real.log R) ^ (2 * (Fintype.card H) ^ 2) := by
  have hk : 1 ≤ Fintype.card H := by
    letI : Nonempty H := hH.to_subtype
    exact Fintype.card_pos
  calc
    |maynardCoefficient H R W F d| ≤
        B * lambdaQuotientWeightSum H R d :=
      abs_maynardCoefficient_le_quotientWeightSum H R W F d B hB hF hd
    _ ≤ B * squarefreeTauFirstMean (Fintype.card H) R :=
      mul_le_mul_of_nonneg_left
        (lambdaQuotientWeightSum_le_squarefreeTauFirstMean hH
          (isMaynardDivisorTuple_of_mem_support hd)) hB
    _ ≤ B * (1 + Real.log R) ^ (2 * (Fintype.card H) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (squarefreeTauFirstMean_le_one_add_log hk) hB

end BoundedGaps.Maynard
