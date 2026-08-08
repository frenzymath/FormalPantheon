import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmic sum bound for Chen's second divisor moment

This file formalizes the monotone sum-integral estimate in equation (11) of
Chen's English Lemma 8 [CHEN1964-EN, p. 1553].
-/

namespace Waring.Analytic

open Set intervalIntegral
open scoped BigOperators

noncomputable section

/-- Chen's logarithmic kernel for the second divisor-moment estimate. -/
def secondMomentKernel (n : Nat) (x : Real) : Real :=
  (n : Real) / x * (Real.log n - Real.log x + 1) ^ 2

private lemma secondMomentKernel_antitone (n : Nat) (hn : 1 ≤ n) :
    AntitoneOn (secondMomentKernel n) (Set.Icc 1 n) := by
  intro x hx y hy hxy
  have hn0 : (0 : Real) < n := by positivity
  have hx0 : (0 : Real) < x := lt_of_lt_of_le zero_lt_one hx.1
  have hy0 : (0 : Real) < y := lt_of_lt_of_le zero_lt_one hy.1
  have hdiv : (n : Real) / y ≤ (n : Real) / x := by
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) hx0 hxy
  have hlog : Real.log n - Real.log y + 1 ≤ Real.log n - Real.log x + 1 := by
    have hlogxy := Real.strictMonoOn_log.monotoneOn hx0 hy0 hxy
    linarith
  have hkx : 0 ≤ Real.log n - Real.log x + 1 := by
    have := Real.strictMonoOn_log.monotoneOn hx0 hn0 hx.2
    linarith
  have hky : 0 ≤ Real.log n - Real.log y + 1 := by
    have := Real.strictMonoOn_log.monotoneOn hy0 hn0 hy.2
    linarith
  unfold secondMomentKernel
  exact mul_le_mul hdiv ((sq_le_sq₀ hky hkx).2 hlog) (sq_nonneg _)
    (div_nonneg hn0.le hx0.le)

private lemma secondMomentKernel_integral (n : Nat) (hn : 1 ≤ n) :
    ∫ x in (1 : Real)..n, secondMomentKernel n x =
      (n : Real) / 3 * ((Real.log n + 1) ^ 3 - 1) := by
  let g : Real → Real := fun x ↦ Real.log n - Real.log x + 1
  let F : Real → Real := fun x ↦ -(n : Real) / 3 * (g ^ (3 : Nat)) x
  have hderiv : ∀ x ∈ Set.uIcc (1 : Real) n,
      HasDerivAt F (secondMomentKernel n x) x := by
    intro x hx
    have hinterval : x ∈ Set.Icc (1 : Real) n := by
      simpa [Set.uIcc_of_le (show (1 : Real) ≤ n by exact_mod_cast hn)] using hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hinterval.1)
    have hbase : HasDerivAt g (-x⁻¹) x := by
      dsimp [g]
      simpa only [Pi.sub_apply, zero_sub] using
        ((hasDerivAt_const x (Real.log n)).sub (Real.hasDerivAt_log hx0)).add_const 1
    have hd := (hbase.pow 3).const_mul (-(n : Real) / 3)
    have hdF : HasDerivAt F
        (-(n : Real) / 3 * ((3 : Nat) * g x ^ (3 - 1) * -x⁻¹)) x := by
      simpa only [F] using hd
    apply hdF.congr_deriv
    dsimp [secondMomentKernel, g]
    norm_num [div_eq_mul_inv]
    ring
  have hint : IntervalIntegrable (secondMomentKernel n) MeasureTheory.volume 1 n := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hinterval : x ∈ Set.Icc (1 : Real) n := by
      simpa [Set.uIcc_of_le (show (1 : Real) ≤ n by exact_mod_cast hn)] using hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hinterval.1)
    apply ContinuousAt.continuousWithinAt
    unfold secondMomentKernel
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [F, g]
  have hn0 : (n : Real) ≠ 0 := by positivity
  rw [Real.log_one, sub_zero]
  ring

/-- Chen's monotone sum-integral estimate used in the second divisor moment. -/
theorem sum_secondMomentKernel_le (n : Nat) :
    ∑ d ∈ Finset.Icc 1 n, secondMomentKernel n d ≤
      (n : Real) / 3 * (Real.log n + 2) ^ 3 := by
  by_cases hn0 : n = 0
  · simp [hn0, secondMomentKernel]
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hanti := secondMomentKernel_antitone n hn
  have htail :
      ∑ d ∈ Finset.Ico 1 n, secondMomentKernel n (d + 1) ≤
        ∫ x in (1 : Real)..n, secondMomentKernel n x := by
    have hanti' :
        AntitoneOn (secondMomentKernel n) (Set.Icc ((1 : Nat) : Real) (n : Real)) := by
      simpa only [Nat.cast_one] using hanti
    simpa only [Nat.cast_add, Nat.cast_one] using
      @AntitoneOn.sum_le_integral_Ico 1 n (secondMomentKernel n) hn hanti'
  have hshift :
      ∑ d ∈ Finset.Ico 1 n, secondMomentKernel n (d + 1) =
        ∑ d ∈ Finset.Ioc 1 n, secondMomentKernel n d := by
    apply Finset.sum_bij (fun d _ ↦ d + 1)
    · simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    · intro a₁ _ a₂ _ h
      omega
    · intro b hb
      simp only [Finset.mem_Ioc] at hb
      refine ⟨b - 1, by simp only [Finset.mem_Ico]; omega, by omega⟩
    · intro d _
      simp only [Nat.cast_add, Nat.cast_one]
  have hsum :
      ∑ d ∈ Finset.Icc 1 n, secondMomentKernel n d =
        secondMomentKernel n 1 +
          ∑ d ∈ Finset.Ico 1 n, secondMomentKernel n (d + 1) := by
    rw [Finset.Icc_eq_cons_Ioc hn, Finset.sum_cons, ← hshift]
    norm_num
  rw [hsum]
  calc
    secondMomentKernel n 1 +
          ∑ d ∈ Finset.Ico 1 n, secondMomentKernel n (d + 1) ≤
        secondMomentKernel n 1 +
          ∫ x in (1 : Real)..n, secondMomentKernel n x := by gcongr
    _ = (n : Real) * (Real.log n + 1) ^ 2 +
        (n : Real) / 3 * ((Real.log n + 1) ^ 3 - 1) := by
      rw [secondMomentKernel_integral n hn]
      simp [secondMomentKernel]
    _ ≤ (n : Real) / 3 * (Real.log n + 2) ^ 3 := by
      have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
      have hp : 0 ≤ (n : Real) * (3 * Real.log n + 5) :=
        mul_nonneg (Nat.cast_nonneg n) (by linarith)
      nlinarith

end

end Waring.Analytic
