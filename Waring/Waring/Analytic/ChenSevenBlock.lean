import Waring.Analytic.ChenSevenPhase
import Waring.Analytic.FourierCoefficientSum

/-!
# Bounded rational-phase blocks in Chen's Lemma 7

This file connects natural-indexed fifth-power character sums to the
integer-interval convention of `shortPowerSum`, then combines Chen's Lemma 6
completion bound with the perturbation-phase variation estimate.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The rational fifth-power character on the block starting at `M`. -/
noncomputable def rationalFifthBlock {q : Nat} [NeZero q]
    (a : ZMod q) (M i : Nat) : Complex :=
  ZMod.stdAddChar (a * ((M + i : Nat) : ZMod q) ^ 5)

/-- For a natural numerator, the rational character times Chen's perturbation
is exactly the exponential with frequency `a/q + z`. -/
theorem exp_fifthPerturbationPhase_mul_rationalFifthBlock_natCast
    (q : Nat) [NeZero q] (a M i : Nat) (z : Real) :
    Complex.exp (Complex.I * fifthPerturbationPhase z M i) *
        rationalFifthBlock (a : ZMod q) M i =
      Complex.exp
        (2 * Real.pi * Complex.I *
          (((a : Real) / q + z) * (((M + i : Nat) : Real) ^ 5))) := by
  have hchar :
      rationalFifthBlock (a : ZMod q) M i =
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a * (M + i) ^ 5 : Nat) : Int) : Complex) / q) := by
    unfold rationalFifthBlock
    convert ZMod.stdAddChar_coe
      (N := q) (((a * (M + i) ^ 5 : Nat) : Int)) using 1
    · push_cast
      ring
  rw [hchar, ← Complex.exp_add]
  congr 1
  unfold fifthPerturbationPhase
  push_cast
  ring

/-- A natural-indexed block is the integer interval
`(M : Int) - 1 < x ≤ (M : Int) - 1 + n` used by `shortPowerSum`. -/
theorem sum_range_rationalFifthBlock_eq_shortPowerSum
    (q : Nat) [NeZero q] (a : ZMod q) (M n : Nat) :
    (∑ i ∈ Finset.range n, rationalFifthBlock a M i) =
      shortPowerSum a ((M : Int) - 1) n := by
  unfold rationalFifthBlock shortPowerSum
  rw [Int.Ioc_eq_finset_map]
  have hdiff :
      ((M : Int) - 1 + (n : Int) - ((M : Int) - 1)) = (n : Int) := by
    ring
  rw [hdiff, Int.toNat_natCast, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  · push_cast
    ring

/-- Lemma 6 bounds a rational fifth-power block of length at most `q`. -/
theorem norm_sum_range_rationalFifthBlock_le_log_of_complete_bound
    (q : Nat) [NeZero q] (a : ZMod q) (M n : Nat) (B : Real)
    (hnq : n ≤ q)
    (hcomplete : ∀ h : ZMod q,
      ‖polynomialCompleteSum a 0 0 0 h‖ ≤ B) :
    ‖∑ i ∈ Finset.range n, rationalFifthBlock a M i‖ ≤
      (Real.log q + 1) * B := by
  rw [sum_range_rationalFifthBlock_eq_shortPowerSum]
  exact norm_shortPowerSum_le_log_of_complete_bound
    q a ((M : Int) - 1) n B hnq hcomplete

/-- The preceding bound holds uniformly for every initial segment of a block
of length at most `q`. -/
theorem norm_partialSum_rationalFifthBlock_le_log_of_complete_bound
    (q : Nat) [NeZero q] (a : ZMod q) (M n : Nat) (B : Real)
    (hnq : n ≤ q)
    (hcomplete : ∀ h : ZMod q,
      ‖polynomialCompleteSum a 0 0 0 h‖ ≤ B) :
    ∀ k, k ≤ n →
      ‖∑ i ∈ Finset.range k, rationalFifthBlock a M i‖ ≤
        (Real.log q + 1) * B := by
  intro k hkn
  exact norm_sum_range_rationalFifthBlock_le_log_of_complete_bound
    q a M k B (hkn.trans hnq) hcomplete

/-- Chen's bounded perturbed-block estimate.  Lemma 6 supplies the rational
partial-sum bound and the `n-1` phase increments cost the factor `4`. -/
theorem norm_perturbedRationalFifthBlock_le
    (q : Nat) [NeZero q] (a : ZMod q) (z : Real)
    (M n P : Nat) (B : Real) (hn : 0 < n) (hP : 0 < P)
    (hMP : M + n ≤ P + 1) (hhalf : 2 * (n - 1) ≤ q)
    (hz : |z| ≤
      1 / (10 * (q : Real) * (P : Real) ^ 4))
    (hcomplete : ∀ h : ZMod q,
      ‖polynomialCompleteSum a 0 0 0 h‖ ≤ B) :
    ‖∑ i ∈ Finset.range n,
        Complex.exp (Complex.I * fifthPerturbationPhase z M i) *
          rationalFifthBlock a M i‖ ≤
      4 * (Real.log q + 1) * B := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hnq : n ≤ q := by omega
  have hpartial :=
    norm_partialSum_rationalFifthBlock_le_log_of_complete_bound
      q a M n B hnq hcomplete
  have hphase :=
    sum_abs_fifthPerturbationPhase_sub_le_three_of_block_length
      z M n P q hn hP hq hMP hhalf hz
  calc
    ‖∑ i ∈ Finset.range n,
        Complex.exp (Complex.I * fifthPerturbationPhase z M i) *
          rationalFifthBlock a M i‖ ≤
        4 * ((Real.log q + 1) * B) :=
      norm_sum_range_exp_I_mul_le_four_of_phase_variation
        (fifthPerturbationPhase z M) (rationalFifthBlock a M) n
          ((Real.log q + 1) * B) hpartial hphase
    _ = 4 * (Real.log q + 1) * B := by ring

/-- Source form of the perturbed-block estimate for a natural numerator
`a`, with the rational and perturbation phases combined into one exponential.
-/
theorem norm_sum_range_exp_fifth_rational_add_perturbation_le
    (q : Nat) [NeZero q] (a : Nat) (z : Real)
    (M n P : Nat) (B : Real) (hn : 0 < n) (hP : 0 < P)
    (hMP : M + n ≤ P + 1) (hhalf : 2 * (n - 1) ≤ q)
    (hz : |z| ≤
      1 / (10 * (q : Real) * (P : Real) ^ 4))
    (hcomplete : ∀ h : ZMod q,
      ‖polynomialCompleteSum (a : ZMod q) 0 0 0 h‖ ≤ B) :
    ‖∑ i ∈ Finset.range n,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) *
              (((M + i : Nat) : Real) ^ 5)))‖ ≤
      4 * (Real.log q + 1) * B := by
  have hsum :
      (∑ i ∈ Finset.range n,
          Complex.exp
            (2 * Real.pi * Complex.I *
              (((a : Real) / q + z) *
                (((M + i : Nat) : Real) ^ 5)))) =
        ∑ i ∈ Finset.range n,
          Complex.exp (Complex.I * fifthPerturbationPhase z M i) *
            rationalFifthBlock (a : ZMod q) M i := by
    apply Finset.sum_congr rfl
    intro i _
    exact
      (exp_fifthPerturbationPhase_mul_rationalFifthBlock_natCast
        q a M i z).symm
  rw [hsum]
  exact norm_perturbedRationalFifthBlock_le
    q (a : ZMod q) z M n P B hn hP hMP hhalf hz hcomplete

end Waring.Analytic
