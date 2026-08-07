import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Vaughan's convolution identity

This file formalizes the finite arithmetic-function core of the four-term
Vaughan decomposition in Akbary--Hambrook2013v2, Section 6, pp. 18--19. The
explicit pair and triple source-index expansions remain separate.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction ArithmeticFunction.Moebius
  ArithmeticFunction.zeta BigOperators

noncomputable section

/-- The part of a real-valued arithmetic function on natural indices at most
a real cutoff. -/
noncomputable def arithmeticFunctionLowCutoff
    (U : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if (n : ℝ) ≤ U then f n else 0, by simp⟩

/-- The complementary part of a real-valued arithmetic function above a real
cutoff. -/
noncomputable def arithmeticFunctionHighCutoff
    (U : ℝ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f - arithmeticFunctionLowCutoff U f

theorem arithmeticFunctionLowCutoff_apply_of_le
    {U : ℝ} {f : ArithmeticFunction ℝ} {n : ℕ}
    (hn : (n : ℝ) ≤ U) :
    arithmeticFunctionLowCutoff U f n = f n := by
  simp [arithmeticFunctionLowCutoff, hn]

theorem arithmeticFunctionLowCutoff_apply_of_lt
    {U : ℝ} {f : ArithmeticFunction ℝ} {n : ℕ}
    (hn : U < (n : ℝ)) :
    arithmeticFunctionLowCutoff U f n = 0 := by
  simp [arithmeticFunctionLowCutoff, not_le_of_gt hn]

theorem arithmeticFunctionHighCutoff_apply_of_le
    {U : ℝ} {f : ArithmeticFunction ℝ} {n : ℕ}
    (hn : (n : ℝ) ≤ U) :
    arithmeticFunctionHighCutoff U f n = 0 := by
  change f n - arithmeticFunctionLowCutoff U f n = 0
  rw [arithmeticFunctionLowCutoff_apply_of_le hn]
  ring

theorem arithmeticFunctionHighCutoff_apply_of_lt
    {U : ℝ} {f : ArithmeticFunction ℝ} {n : ℕ}
    (hn : U < (n : ℝ)) :
    arithmeticFunctionHighCutoff U f n = f n := by
  change f n - arithmeticFunctionLowCutoff U f n = f n
  rw [arithmeticFunctionLowCutoff_apply_of_lt hn]
  ring

theorem arithmeticFunctionLowCutoff_add_highCutoff
    (U : ℝ) (f : ArithmeticFunction ℝ) :
    arithmeticFunctionLowCutoff U f +
      arithmeticFunctionHighCutoff U f = f := by
  unfold arithmeticFunctionHighCutoff
  abel

/-- Convolution of a cutoff with arithmetic zeta is the corresponding
restricted divisor sum. -/
theorem arithmeticFunctionLowCutoff_mul_zeta_apply
    (V : ℝ) (f : ArithmeticFunction ℝ) (k : ℕ) :
    (arithmeticFunctionLowCutoff V f *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) k =
      ∑ d ∈ k.divisors.filter (fun d : ℕ ↦ (d : ℝ) ≤ V), f d := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  simp only [arithmeticFunctionLowCutoff, ArithmeticFunction.coe_mk,
    Finset.sum_filter]

/-- Below the cutoff, the restricted Mobius divisor sum is the
Dirichlet-convolution unit coefficient. -/
theorem moebiusLowCutoff_mul_zeta_apply_of_le
    {V : ℝ} {k : ℕ} (hk : (k : ℝ) ≤ V) :
    (arithmeticFunctionLowCutoff V
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) k =
      (1 : ArithmeticFunction ℝ) k := by
  by_cases hk0 : k = 0
  · subst k
    simp [arithmeticFunctionLowCutoff]
  calc
    (arithmeticFunctionLowCutoff V
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) k =
        ∑ d ∈ k.divisors,
          arithmeticFunctionLowCutoff V
            (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d :=
      ArithmeticFunction.coe_mul_zeta_apply
    _ = ∑ d ∈ k.divisors,
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) d := by
      apply Finset.sum_congr rfl
      intro d hd
      apply arithmeticFunctionLowCutoff_apply_of_le
      exact (Nat.cast_le.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0)
        (Nat.mem_divisors.mp hd).1)).trans hk
    _ = ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) k :=
      ArithmeticFunction.coe_mul_zeta_apply.symm
    _ = (1 : ArithmeticFunction ℝ) k := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]

/-- The arithmetic-function convolution core of Vaughan's four-term
decomposition. -/
theorem vaughanConvolutionIdentity (U V : ℝ) :
    arithmeticFunctionLowCutoff U ArithmeticFunction.vonMangoldt +
        arithmeticFunctionLowCutoff V
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
            ArithmeticFunction.log -
        arithmeticFunctionLowCutoff U ArithmeticFunction.vonMangoldt *
          arithmeticFunctionLowCutoff V
            (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) +
      (arithmeticFunctionHighCutoff U ArithmeticFunction.vonMangoldt -
        arithmeticFunctionHighCutoff U ArithmeticFunction.vonMangoldt *
          arithmeticFunctionLowCutoff V
            (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) =
      ArithmeticFunction.vonMangoldt := by
  rw [← ArithmeticFunction.vonMangoldt_mul_zeta]
  unfold arithmeticFunctionHighCutoff
  ring

end

end BoundedGaps.Maynard
