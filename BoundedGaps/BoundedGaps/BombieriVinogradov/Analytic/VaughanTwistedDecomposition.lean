import BoundedGaps.BombieriVinogradov.Analytic.CharacterOrthogonality
import BoundedGaps.BombieriVinogradov.Analytic.VaughanSourceReindex

/-!
# Vaughan's character-twisted decomposition

This file lifts the four source-shaped Vaughan coefficients from
Akbary--Hambrook2013v2, Section 6, pp. 18--19 through a complex Dirichlet
character and the finite natural endpoint sum. It contains no character-sum
estimate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt

noncomputable section

/-- The second Vaughan coefficient in the source's `(h,d)` factor order. -/
theorem vaughanLambdaTwo_apply (V : ℝ) (n : ℕ) :
    (arithmeticFunctionLowCutoff V
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
        ArithmeticFunction.log) n =
      ∑ hd ∈ n.divisorsAntidiagonal.filter
        (fun hd : ℕ × ℕ ↦ (hd.2 : ℝ) ≤ V),
        (ArithmeticFunction.moebius hd.2 : ℝ) * Real.log hd.1 := by
  rw [show arithmeticFunctionLowCutoff V
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
          ArithmeticFunction.log =
      ArithmeticFunction.log *
        arithmeticFunctionLowCutoff V
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) by
    rw [mul_comm], ArithmeticFunction.mul_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro hd _hhd
  by_cases hdV : (hd.2 : ℝ) ≤ V
  · simp [arithmeticFunctionLowCutoff, hdV, mul_comm]
  · simp [arithmeticFunctionLowCutoff, hdV]

/-- The first character-twisted Vaughan sum. -/
noncomputable def vaughanTwistedSumOne
    (U : ℝ) (y q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 y).filter (fun n : ℕ ↦ (n : ℝ) ≤ U),
    χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- The second character-twisted Vaughan sum. -/
noncomputable def vaughanTwistedSumTwo
    (V : ℝ) (y q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    χ n *
      ((∑ hd ∈ n.divisorsAntidiagonal.filter
          (fun hd : ℕ × ℕ ↦ (hd.2 : ℝ) ≤ V),
          (ArithmeticFunction.moebius hd.2 : ℝ) * Real.log hd.1 : ℝ) : ℂ)

/-- The third character-twisted Vaughan sum. -/
noncomputable def vaughanTwistedSumThree
    (U V : ℝ) (y q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    χ n *
      ((-∑ tr ∈ n.divisorsAntidiagonal,
          ∑ md ∈ tr.1.divisorsAntidiagonal.filter
            (fun md : ℕ × ℕ ↦
              (md.1 : ℝ) ≤ U ∧ (md.2 : ℝ) ≤ V),
            ArithmeticFunction.vonMangoldt md.1 *
              (ArithmeticFunction.moebius : ArithmeticFunction ℝ) md.2 : ℝ) : ℂ)

/-- The fourth character-twisted Vaughan sum. -/
noncomputable def vaughanTwistedSumFour
    (U V : ℝ) (y q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    χ n *
      ((-∑ mk ∈ n.divisorsAntidiagonal.filter
          (fun mk : ℕ × ℕ ↦
            U < (mk.1 : ℝ) ∧ V < (mk.2 : ℝ)),
          ArithmeticFunction.vonMangoldt mk.1 *
            ∑ d ∈ mk.2.divisors.filter
              (fun d : ℕ ↦ (d : ℝ) ≤ V),
              (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d : ℝ) : ℂ)

/-- A twisted von Mangoldt endpoint sum is the sum of the four source-shaped
Vaughan terms. -/
theorem twistedChebyshevSum_eq_vaughanTwistedSums
    {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (y q : ℕ) (χ : DirichletCharacter ℂ q) :
    twistedChebyshevSum y q χ =
      vaughanTwistedSumOne U y q χ +
      vaughanTwistedSumTwo V y q χ +
      vaughanTwistedSumThree U V y q χ +
      vaughanTwistedSumFour U V y q χ := by
  unfold twistedChebyshevSum vaughanTwistedSumOne
    vaughanTwistedSumTwo vaughanTwistedSumThree vaughanTwistedSumFour
  rw [Finset.sum_filter]
  simp_rw [← vaughanLambdaTwo_apply,
    ← vaughanLambdaThree_apply hU hV,
    ← vaughanLambdaFour_apply hU hV]
  have hS1 :
      (∑ n ∈ Finset.Icc 1 y,
        if (n : ℝ) ≤ U then
          χ n * (ArithmeticFunction.vonMangoldt n : ℂ)
        else 0) =
      ∑ n ∈ Finset.Icc 1 y,
        χ n *
          (arithmeticFunctionLowCutoff U
            ArithmeticFunction.vonMangoldt n : ℂ) := by
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hnU : (n : ℝ) ≤ U
    · rw [if_pos hnU, arithmeticFunctionLowCutoff_apply_of_le hnU]
    · rw [if_neg hnU,
        arithmeticFunctionLowCutoff_apply_of_lt (lt_of_not_ge hnU)]
      simp
  rw [hS1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [← mul_add, ← mul_add, ← mul_add]
  congr 1
  rw [← Complex.ofReal_add, ← Complex.ofReal_add,
    ← Complex.ofReal_add]
  simpa only [sub_eq_add_neg, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply] using
    (congrArg (fun f : ArithmeticFunction ℝ ↦ (f n : ℂ))
      (vaughanConvolutionIdentity U V)).symm

end

end BoundedGaps.Maynard
