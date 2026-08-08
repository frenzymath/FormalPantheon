import Waring.Analytic.HuaInduction
import Waring.Analytic.ChenFive

/-!
# Hua's small-prime input to Chen's Lemma 5

This file specializes the fixed-degree Hua induction to the initial formal
quintic and discharges the small-prime hypothesis isolated in Chen's Lemma 5.
-/

namespace Waring.Analytic

/-- Hua's degree-five estimate for a primitive integer quintic at every
positive power of a prime below eleven. -/
theorem hua_fifthPolynomialFormal_primePower_bound
    (p l : Nat) [Fact p.Prime] [NeZero p]
    (hpSmall : p < 11) (hl : 0 < l)
    (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
        (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
        (a₄ : ZMod p) ≠ 0) :
    ‖integerFormalPolynomialCompleteSum (q := p ^ l)
      (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄)‖ ≤
      125 * (((p ^ l : Nat) : Real) ^ (4 / 5 : Real)) := by
  let phase :=
    fifthPolynomialHuaPhaseData a₀ a₁ a₂ a₃ a₄ hcoeff
  have hbound := hua_primePower_strong_bound p hpSmall l hl
    (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄) phase
  have hcomplexity : Nat.max 1 phase.complexity ≤ 5 := by
    apply max_le
    · norm_num
    · exact phase.complexity_le_four.trans (by norm_num)
  have hscaleNonneg :
      0 ≤ (p : Real) ^ (((4 * l : Nat) : Real) / 5) :=
    Real.rpow_nonneg (by positivity) _
  calc
    ‖integerFormalPolynomialCompleteSum (q := p ^ l)
      (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄)‖ ≤
      25 * (Nat.max 1 phase.complexity : Nat) *
        (p : Real) ^ (((4 * l : Nat) : Real) / 5) := hbound
    _ ≤ 125 * (p : Real) ^ (((4 * l : Nat) : Real) / 5) := by
      apply mul_le_mul_of_nonneg_right _ hscaleNonneg
      exact_mod_cast (Nat.mul_le_mul_left 25 hcomplexity)
    _ = 125 * (((p ^ l : Nat) : Real) ^ (4 / 5 : Real)) := by
      rw [primePow_rpow_four_fifths]

/-- Bundled five-coefficient form of Hua's small-prime estimate. -/
theorem norm_fivePolynomialCompleteSum_primePower_le_hua
    (p alpha : Nat) (hp : p.Prime) (hAlpha : 0 < alpha)
    (hpSmall : p < 11) (a : FiveCoefficients (p ^ alpha))
    (ha : PrimitiveFiveCoefficients a) :
    ‖@fivePolynomialCompleteSum (p ^ alpha)
        ⟨pow_ne_zero alpha hp.ne_zero⟩ a‖ ≤
      125 * (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real)) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ alpha) := ⟨pow_ne_zero alpha hp.ne_zero⟩
  rw [fivePolynomialCompleteSum_eq_integerRepresentatives]
  rw [← integerFormalPolynomialCompleteSum_fifthPolynomialFormal]
  apply hua_fifthPolynomialFormal_primePower_bound p alpha hpSmall hAlpha
  simpa only [Int.cast_natCast] using
    primitiveFiveCoefficients_representatives_mod_prime
      p alpha hp hAlpha a ha

/-- The previously isolated Hua hypothesis in Chen's Lemma 5 is now proved. -/
theorem chenFiveHuaSmallPrimePowerBound :
    ChenFiveHuaSmallPrimePowerBound := by
  intro p alpha hp hAlpha hpSmall a ha
  exact norm_fivePolynomialCompleteSum_primePower_le_hua
    p alpha hp hAlpha hpSmall a ha

end Waring.Analytic
