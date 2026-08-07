import BoundedGaps.BombieriVinogradov.Analytic.VaughanConvolutionIdentity

/-!
# Vaughan source reindexing

This file expands the third and fourth convolution terms from SEM-429 into
the exact finite sums displayed in Akbary--Hambrook2013v2, Section 6,
pp. 18--19. It contains no character or analytic estimate.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction ArithmeticFunction.Moebius
  ArithmeticFunction.zeta BigOperators

noncomputable section

/-- Above `V >= 1`, subtracting the cutoff Möbius divisor coefficient from
the convolution unit leaves exactly the negative high-`k` coefficient. -/
theorem one_sub_moebiusLowCutoff_mul_zeta_apply
    {V : ℝ} (hV : 1 ≤ V) (k : ℕ) :
    (((1 : ArithmeticFunction ℝ) -
        arithmeticFunctionLowCutoff V
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) k =
      if V < (k : ℝ) then
        -∑ d ∈ k.divisors.filter (fun d : ℕ ↦ (d : ℝ) ≤ V),
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d
      else 0) := by
  change (1 : ArithmeticFunction ℝ) k -
      (arithmeticFunctionLowCutoff V
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) k = _
  by_cases hk : (k : ℝ) ≤ V
  · rw [moebiusLowCutoff_mul_zeta_apply_of_le hk]
    simp [not_lt_of_ge hk]
  · have hk' : V < (k : ℝ) := lt_of_not_ge hk
    have hk1 : k ≠ 1 := by
      intro hk1
      subst k
      norm_num at hk'
      exact (not_lt_of_ge hV) hk'
    rw [ArithmeticFunction.one_apply_ne hk1,
      arithmeticFunctionLowCutoff_mul_zeta_apply, zero_sub, if_pos hk']

/-- The third convolution term is the source's nested `m*d*r=n` sum. -/
theorem vaughanLambdaThree_apply
    {U V : ℝ} (_hU : 1 ≤ U) (_hV : 1 ≤ V) (n : ℕ) :
    (-(arithmeticFunctionLowCutoff U ArithmeticFunction.vonMangoldt *
        arithmeticFunctionLowCutoff V
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ))) n =
      -∑ tr ∈ n.divisorsAntidiagonal,
        ∑ md ∈ tr.1.divisorsAntidiagonal.filter
          (fun md : ℕ × ℕ ↦
            (md.1 : ℝ) ≤ U ∧ (md.2 : ℝ) ≤ V),
          ArithmeticFunction.vonMangoldt md.1 *
            (ArithmeticFunction.moebius : ArithmeticFunction ℝ) md.2 := by
  rw [ArithmeticFunction.neg_apply, ArithmeticFunction.mul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro tr htr
  have hmem := Nat.mem_divisorsAntidiagonal.mp htr
  have htr2 : tr.2 ≠ 0 := by
    apply right_ne_zero_of_mul
    rw [hmem.1]
    exact hmem.2
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply,
    if_neg htr2, Nat.cast_one, mul_one, ArithmeticFunction.mul_apply]
  simp only [Finset.sum_filter, arithmeticFunctionLowCutoff,
    ArithmeticFunction.coe_mk]
  apply Finset.sum_congr rfl
  intro md _hmd
  by_cases hm : (md.1 : ℝ) ≤ U
  · by_cases hd : (md.2 : ℝ) ≤ V
    · simp [hm, hd]
    · simp [hm, hd]
  · simp [hm]

/-- The fourth convolution term is the source's high-`m`, high-`k` sum. -/
theorem vaughanLambdaFour_apply
    {U V : ℝ} (_hU : 1 ≤ U) (hV : 1 ≤ V) (n : ℕ) :
    (arithmeticFunctionHighCutoff U ArithmeticFunction.vonMangoldt -
        arithmeticFunctionHighCutoff U ArithmeticFunction.vonMangoldt *
          arithmeticFunctionLowCutoff V
            (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n =
      -∑ mk ∈ n.divisorsAntidiagonal.filter
        (fun mk : ℕ × ℕ ↦
          U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ)),
        ArithmeticFunction.vonMangoldt mk.1 *
          ∑ d ∈ mk.2.divisors.filter
            (fun d : ℕ ↦ (d : ℝ) ≤ V),
            (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d := by
  let H := arithmeticFunctionHighCutoff U ArithmeticFunction.vonMangoldt
  let M := arithmeticFunctionLowCutoff V
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
  let Z := (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  have hrearrange : H - H * M * Z = H * (1 - M * Z) := by ring
  change (H - H * M * Z) n = _
  rw [hrearrange, ArithmeticFunction.mul_apply,
    ← Finset.sum_neg_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mk _hmk
  change H mk.1 * ((1 : ArithmeticFunction ℝ) - M * Z) mk.2 = _
  rw [show ((1 : ArithmeticFunction ℝ) - M * Z) mk.2 =
      if V < (mk.2 : ℝ) then
        -∑ d ∈ mk.2.divisors.filter (fun d : ℕ ↦ (d : ℝ) ≤ V),
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d
      else 0 by exact one_sub_moebiusLowCutoff_mul_zeta_apply hV mk.2]
  by_cases hm : U < (mk.1 : ℝ)
  · change arithmeticFunctionHighCutoff U
        ArithmeticFunction.vonMangoldt mk.1 * _ = _
    rw [arithmeticFunctionHighCutoff_apply_of_lt hm]
    by_cases hk : V < (mk.2 : ℝ)
    · simp [hm, hk]
    · simp [hm, hk]
  · have hmle : (mk.1 : ℝ) ≤ U := le_of_not_gt hm
    change arithmeticFunctionHighCutoff U
        ArithmeticFunction.vonMangoldt mk.1 * _ = _
    rw [arithmeticFunctionHighCutoff_apply_of_le hmle]
    simp [hm]

end

end BoundedGaps.Maynard
