import Waring.Analytic.ChenFourQuotient

/-!
# Prime-power critical blocks in Chen's Lemma 4

This file specializes the canonical quotient/repetition identity to powers of
one prime and proves the terminal constant-phase branch omitted in the printed
induction [CHEN1964-EN, p. 1549; CHEN1964-ZH, p. 717].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- When `sigma <= l`, a critical block modulo `p^l` consists of
`p^(sigma-2)` copies of the quotient complete sum modulo `p^(l-sigma)`. -/
theorem fifthCriticalBlockSum_primePower_eq_repeated_quotient
    (p l : Nat) [Fact p.Prime] [NeZero p]
    (x : Int) (a₀ a₁ a₂ a₃ a₄ : Int)
    (htwo : 2 ≤ fifthCriticalExponent p x a₀ a₁ a₂ a₃ a₄)
    (hle : fifthCriticalExponent p x a₀ a₁ a₂ a₃ a₄ ≤ l) :
    fifthCriticalBlockSum (q := p ^ l) p (p ^ (l - 2)) x
        a₀ a₁ a₂ a₃ a₄ =
      (p ^ (fifthCriticalExponent p x a₀ a₁ a₂ a₃ a₄ - 2) : Complex) *
        integerPolynomialCompleteSum
          (q := p ^ (l - fifthCriticalExponent p x a₀ a₁ a₂ a₃ a₄))
          ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 5)
          ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 4)
          ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 3)
          ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 2)
          ((fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄).coeff 1) := by
  let sigma := fifthCriticalExponent p x a₀ a₁ a₂ a₃ a₄
  have hlength : p ^ (sigma - 2) * p ^ (l - sigma) = p ^ (l - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hmodulus : p ^ (l - sigma) * p ^ sigma = p ^ l := by
    rw [← pow_add]
    congr 1
    omega
  have hrepeat := fifthCriticalBlockSum_eq_repeated_quotient
    p (p ^ (sigma - 2)) (p ^ (l - sigma)) x a₀ a₁ a₂ a₃ a₄
  simpa only [sigma, hlength, hmodulus, Nat.cast_pow] using hrepeat

/-- If the translated content exponent reaches the modulus exponent, every
phase in the critical block is zero modulo `p^l`. -/
theorem fifthCriticalBlockSum_primePower_eq_card_of_le_exponent
    (p l : Nat) [Fact p.Prime] [NeZero p]
    (x : Int) (a₀ a₁ a₂ a₃ a₄ : Int)
    (hle : l ≤ fifthCriticalExponent p x a₀ a₁ a₂ a₃ a₄) :
    fifthCriticalBlockSum (q := p ^ l) p (p ^ (l - 2)) x
        a₀ a₁ a₂ a₃ a₄ = (p ^ (l - 2) : Complex) := by
  let sigma := fifthCriticalExponent p x a₀ a₁ a₂ a₃ a₄
  let G := fifthCriticalQuotient p x a₀ a₁ a₂ a₃ a₄
  have hfactor := fifthCriticalTranslate_eq_C_pow_mul_fifthCriticalQuotient
    p x a₀ a₁ a₂ a₃ a₄
  rw [fifthCriticalBlockSum]
  calc
    (∑ k : Fin (p ^ (l - 2)),
        ZMod.stdAddChar
          (((fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).eval
            (k.val : Int) : Int) : ZMod (p ^ l))) =
        ∑ _k : Fin (p ^ (l - 2)), (1 : Complex) := by
      apply Finset.sum_congr rfl
      intro k _
      have heval := congrArg
        (fun F : Polynomial Int ↦ F.eval (k.val : Int)) hfactor
      have heval' :
          (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).eval
              (k.val : Int) =
            (p : Int) ^ sigma * G.eval (k.val : Int) := by
        simpa only [Polynomial.eval_mul, Polynomial.eval_C] using heval
      have hpow : (p : Int) ^ l ∣ (p : Int) ^ sigma :=
        pow_dvd_pow (p : Int) hle
      have hdvd : (p : Int) ^ l ∣
          (fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).eval
            (k.val : Int) := by
        rw [heval']
        exact dvd_mul_of_dvd_left hpow _
      have hcast :
          (((fifthCriticalTranslate p x a₀ a₁ a₂ a₃ a₄).eval
            (k.val : Int) : Int) : ZMod (p ^ l)) = 0 := by
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
      rw [hcast]
      simp
    _ = (p ^ (l - 2) : Complex) := by simp

/-- Norm form of the terminal constant-phase critical block. -/
theorem norm_fifthCriticalBlockSum_primePower_of_le_exponent
    (p l : Nat) [Fact p.Prime] [NeZero p]
    (x : Int) (a₀ a₁ a₂ a₃ a₄ : Int)
    (hle : l ≤ fifthCriticalExponent p x a₀ a₁ a₂ a₃ a₄) :
    ‖fifthCriticalBlockSum (q := p ^ l) p (p ^ (l - 2)) x
        a₀ a₁ a₂ a₃ a₄‖ = (p ^ (l - 2) : Real) := by
  rw [fifthCriticalBlockSum_primePower_eq_card_of_le_exponent
    p l x a₀ a₁ a₂ a₃ a₄ hle]
  simp

-- Primality is part of the reviewed prime-power block contract and is kept
-- uniform with the adjacent recursion results, even in this terminal case.
attribute [nolint unusedArguments]
  fifthCriticalBlockSum_primePower_eq_card_of_le_exponent

end Waring.Analytic
