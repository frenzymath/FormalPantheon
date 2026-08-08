import Waring.Analytic.ChenFourCriticalBlocks
import Waring.Analytic.ChenFourValuation

/-!
# Conditional induction aggregation in Chen's Lemma 4

This file packages the final derivative-root weight summation. The hypotheses
expose, rather than assume globally, the still-pending bound for each translated
critical block.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- If every critical block has Chen's normalized weight and its exponent is
bounded by root multiplicity plus one, then the complete sum has bound `B`. -/
theorem norm_integerPolynomialCompleteSum_le_of_criticalBlock_bounds
    (p s : Nat) [Fact p.Prime] [NeZero p] [NeZero s] (hp : 11 ≤ p)
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
      (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
      (a₄ : ZMod p) ≠ 0)
    (B : Real) (hB : 0 ≤ B) (sigma : ZMod p → Nat)
    (hsigma :
      ∀ x ∈ fifthDerivativeRoots
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p),
        sigma x ≤ fifthDerivativeMultiplicity
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p) x + 1)
    (hblocks :
      ∀ x ∈ fifthDerivativeRoots
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p),
        (p : Real) *
            ‖fifthCriticalBlockSum (q := p * (p * s)) p s (x.val : Int)
              a₀ a₁ a₂ a₃ a₄‖ ≤
          B * (p : Real) ^ ((sigma x : Real) / 5 - 1)) :
    ‖integerPolynomialCompleteSum (q := p * (p * s))
        a₀ a₁ a₂ a₃ a₄‖ ≤ B := by
  let roots := fifthDerivativeRoots
    (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
    (a₃ : ZMod p) (a₄ : ZMod p)
  have hweights :
      ∑ x ∈ roots, (p : Real) ^ ((sigma x : Real) / 5 - 1) ≤ 1 := by
    exact sum_fifthDerivative_stationaryWeight_le_one hp
      (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
      (a₃ : ZMod p) (a₄ : ZMod p) sigma hsigma
  calc
    ‖integerPolynomialCompleteSum (q := p * (p * s))
        a₀ a₁ a₂ a₃ a₄‖ ≤
        (p : Real) * ∑ x ∈ roots,
          ‖fifthCriticalBlockSum (q := p * (p * s)) p s (x.val : Int)
            a₀ a₁ a₂ a₃ a₄‖ :=
      norm_integerPolynomialCompleteSum_le_sum_criticalBlockNorms
        p s hp a₀ a₁ a₂ a₃ a₄ hcoeff
    _ = ∑ x ∈ roots, (p : Real) *
          ‖fifthCriticalBlockSum (q := p * (p * s)) p s (x.val : Int)
            a₀ a₁ a₂ a₃ a₄‖ := by rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ roots,
          B * (p : Real) ^ ((sigma x : Real) / 5 - 1) := by
      apply Finset.sum_le_sum
      intro x hx
      exact hblocks x hx
    _ = B * ∑ x ∈ roots,
          (p : Real) ^ ((sigma x : Real) / 5 - 1) := by rw [Finset.mul_sum]
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left hweights hB
    _ = B := mul_one B

/-- Choosing Chen's exponent to be the `p`-adic valuation of the translated
polynomial content discharges the multiplicity hypothesis in the aggregation
theorem.  Only the per-block quotient estimate remains exposed. -/
theorem norm_integerPolynomialCompleteSum_le_of_valuation_block_bounds
    (p s : Nat) [Fact p.Prime] [NeZero p] [NeZero s] (hp : 11 ≤ p)
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
      (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
      (a₄ : ZMod p) ≠ 0)
    (B : Real) (hB : 0 ≤ B)
    (hblocks :
      ∀ x ∈ fifthDerivativeRoots
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p),
        (p : Real) *
            ‖fifthCriticalBlockSum (q := p * (p * s)) p s (x.val : Int)
              a₀ a₁ a₂ a₃ a₄‖ ≤
          B * (p : Real) ^
            ((padicValInt p
              (fifthCriticalTranslate p (x.val : Int)
                a₀ a₁ a₂ a₃ a₄).content : Real) / 5 - 1)) :
    ‖integerPolynomialCompleteSum (q := p * (p * s))
        a₀ a₁ a₂ a₃ a₄‖ ≤ B := by
  apply norm_integerPolynomialCompleteSum_le_of_criticalBlock_bounds
    p s hp a₀ a₁ a₂ a₃ a₄ hcoeff B hB
    (fun x ↦ padicValInt p
      (fifthCriticalTranslate p (x.val : Int) a₀ a₁ a₂ a₃ a₄).content)
  · intro x _hx
    simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
      padicValInt_content_fifthCriticalTranslate_le_succ_multiplicity
        hp (x.val : Int) a₀ a₁ a₂ a₃ a₄ hcoeff
  · exact hblocks

end Waring.Analytic
