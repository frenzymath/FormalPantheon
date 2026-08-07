import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthTermDyadic
import Mathlib.NumberTheory.Chebyshev

/-!
# Von Mangoldt energy for Vaughan's fourth term

This file proves the first coefficient-energy estimate used in
Akbary--Hambrook's treatment of the fourth Vaughan term.  The source-facing
theorem accepts an explicit global Chebyshev majorant.  Its unconditional
specialization uses Mathlib's verified constant `log 4 + 4`.

Source: `AkbaryHambrook2013v2`, Section 6, p. 23, preceding equation (6.15).
Semantic review: `SEM-458`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt

noncomputable section

/-- The von Mangoldt square energy on a fourth-term dyadic block, assuming a
global Chebyshev bound `psi(z) <= A * z`. -/
theorem sum_norm_sq_vonMangoldt_vaughanFourthDyadic_le_of_psi
    {A U V : ℝ} (_hA : 0 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    (x alpha : ℕ) :
    (∑ m ∈ vaughanFourthDyadicMIndices U V x alpha,
      ‖((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)‖ ^ 2) ≤
      2 * A * (2 ^ alpha : ℕ) *
        Real.log (2 * ((2 ^ alpha : ℕ) : ℝ)) := by
  let M : ℕ := 2 ^ alpha
  have hMpos : 0 < M := by
    dsimp only [M]
    positivity
  have hMnonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hlogNonneg : 0 ≤ Real.log (2 * (M : ℝ)) := by
    apply Real.log_nonneg
    have hMoneNat : 1 ≤ M := by omega
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hMoneNat
    nlinarith
  have hsupport (m : ℕ)
      (hm : m ∈ vaughanFourthDyadicMIndices U V x alpha) :
      0 < m ∧ m ≤ 2 * M := by
    rcases Finset.mem_filter.mp hm with ⟨hmBlock, _hmCutoffs⟩
    rcases Finset.mem_Ioc.mp hmBlock with ⟨hMlt, hmUpper⟩
    refine ⟨hMpos.trans hMlt, ?_⟩
    simpa only [M, dyadicBlock, pow_succ, Nat.succ_eq_add_one,
      Nat.mul_comm] using hmUpper
  have hpoint (m : ℕ)
      (hm : m ∈ vaughanFourthDyadicMIndices U V x alpha) :
      ‖((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)‖ ^ 2 ≤
        ArithmeticFunction.vonMangoldt m * Real.log (2 * (M : ℝ)) := by
    have hmBounds := hsupport m hm
    have hmPosReal : 0 < (m : ℝ) := by exact_mod_cast hmBounds.1
    have hmUpperReal : (m : ℝ) ≤ 2 * (M : ℝ) := by
      exact_mod_cast hmBounds.2
    simp only [Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, pow_two]
    apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hmPosReal hmUpperReal)
  have hprefix :
      (∑ m ∈ vaughanFourthDyadicMIndices U V x alpha,
        ArithmeticFunction.vonMangoldt m) ≤
        Chebyshev.psi ((2 * M : ℕ) : ℝ) := by
    rw [Chebyshev.psi, Nat.floor_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      exact Finset.mem_Ioc.mpr (hsupport m hm)
    · intro m _hm _hmNot
      exact ArithmeticFunction.vonMangoldt_nonneg
  calc
    (∑ m ∈ vaughanFourthDyadicMIndices U V x alpha,
        ‖((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)‖ ^ 2) ≤
        ∑ m ∈ vaughanFourthDyadicMIndices U V x alpha,
          ArithmeticFunction.vonMangoldt m * Real.log (2 * (M : ℝ)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact hpoint m hm
    _ = (∑ m ∈ vaughanFourthDyadicMIndices U V x alpha,
          ArithmeticFunction.vonMangoldt m) * Real.log (2 * (M : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ Chebyshev.psi ((2 * M : ℕ) : ℝ) *
        Real.log (2 * (M : ℝ)) :=
      mul_le_mul_of_nonneg_right hprefix hlogNonneg
    _ ≤ (A * ((2 * M : ℕ) : ℝ)) * Real.log (2 * (M : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hlogNonneg
      exact hpsi _ (by positivity)
    _ = 2 * A * (M : ℝ) * Real.log (2 * (M : ℝ)) := by
      push_cast
      ring
    _ = 2 * A * (2 ^ alpha : ℕ) *
        Real.log (2 * ((2 ^ alpha : ℕ) : ℝ)) := by
      rfl

/-- Square-root form of the generic von Mangoldt energy estimate. -/
theorem sqrt_sum_norm_sq_vonMangoldt_vaughanFourthDyadic_le_of_psi
    {A U V : ℝ} (hA : 0 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    (x alpha : ℕ) :
    Real.sqrt (∑ m ∈ vaughanFourthDyadicMIndices U V x alpha,
      ‖((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)‖ ^ 2) ≤
      Real.sqrt 2 * Real.sqrt A * Real.sqrt ((2 ^ alpha : ℕ) : ℝ) *
        Real.sqrt (Real.log (2 * ((2 ^ alpha : ℕ) : ℝ))) := by
  let M : ℕ := 2 ^ alpha
  have hMnonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have henergy :=
    sum_norm_sq_vonMangoldt_vaughanFourthDyadic_le_of_psi
      (A := A) (U := U) (V := V) hA hpsi x alpha
  change Real.sqrt (∑ m ∈ vaughanFourthDyadicMIndices U V x alpha,
      ‖((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)‖ ^ 2) ≤
    Real.sqrt 2 * Real.sqrt A * Real.sqrt (M : ℝ) *
      Real.sqrt (Real.log (2 * (M : ℝ)))
  change (∑ m ∈ vaughanFourthDyadicMIndices U V x alpha,
      ‖((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)‖ ^ 2) ≤
    2 * A * (M : ℝ) * Real.log (2 * (M : ℝ)) at henergy
  calc
    Real.sqrt (∑ m ∈ vaughanFourthDyadicMIndices U V x alpha,
        ‖((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)‖ ^ 2) ≤
        Real.sqrt (2 * A * (M : ℝ) * Real.log (2 * (M : ℝ))) :=
      Real.sqrt_le_sqrt henergy
    _ = Real.sqrt (2 * (A * ((M : ℝ) * Real.log (2 * (M : ℝ))))) := by
      congr 1
      ring
    _ = Real.sqrt 2 * Real.sqrt (A *
        ((M : ℝ) * Real.log (2 * (M : ℝ)))) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = Real.sqrt 2 * (Real.sqrt A *
        Real.sqrt ((M : ℝ) * Real.log (2 * (M : ℝ)))) := by
      rw [Real.sqrt_mul hA]
    _ = Real.sqrt 2 * Real.sqrt A * Real.sqrt (M : ℝ) *
        Real.sqrt (Real.log (2 * (M : ℝ))) := by
      rw [Real.sqrt_mul hMnonneg]
      ring

/-- Unconditional specialization using Mathlib's verified global Chebyshev
constant `log 4 + 4`. -/
theorem sum_norm_sq_vonMangoldt_vaughanFourthDyadic_le
    (U V : ℝ) (x alpha : ℕ) :
    (∑ m ∈ vaughanFourthDyadicMIndices U V x alpha,
      ‖((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ)‖ ^ 2) ≤
      2 * (Real.log 4 + 4) * (2 ^ alpha : ℕ) *
        Real.log (2 * ((2 ^ alpha : ℕ) : ℝ)) := by
  apply sum_norm_sq_vonMangoldt_vaughanFourthDyadic_le_of_psi
  · positivity
  · intro z hz
    exact Chebyshev.psi_le_const_mul_self hz

end

end BoundedGaps.Maynard
