import Waring.Analytic.ChenFourInduction
import Waring.Analytic.ChenFourPrimePowerBlocks

/-!
# Conditional prime-power induction in Chen's Lemma 4

This file packages Chen's induction from a primitive prime-field estimate to
all positive powers of the same prime [CHEN1964-EN, pp. 1549-1550;
CHEN1964-ZH, p. 717].  The prime-field estimate remains an explicit input.
-/

namespace Waring.Analytic

/-- Chen's local constant in Lemma 4. -/
noncomputable def chenFourPrimeFactor (p : Nat) : Real :=
  max 1 (min ((p : Real) ^ (1 / 5 : Real))
    (5 * (p : Real) ^ (-(3 / 10) : Real)))

/-- The local Chen constant is at least one. -/
theorem one_le_chenFourPrimeFactor (p : Nat) :
    1 ≤ chenFourPrimeFactor p :=
  le_max_left _ _

/-- The still-open prime-field input to Chen's Lemma 4, parameterized by its
constant. -/
def ChenFourPrimeFieldBound (p : Nat) [NeZero p] (K : Real) : Prop :=
  ∀ a₀ a₁ a₂ a₃ a₄ : Int,
    (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
      (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
      (a₄ : ZMod p) ≠ 0 →
    ‖integerPolynomialCompleteSum (q := p) a₀ a₁ a₂ a₃ a₄‖ ≤
      K * (p : Real) ^ (4 / 5 : Real)

/-- The valuation-block aggregation theorem in the direct modulus shape
`p^l`, for `l >= 2`. -/
theorem norm_integerPolynomialCompleteSum_primePower_le_of_valuation_blocks
    (p l : Nat) [Fact p.Prime] [NeZero p] (hp : 11 ≤ p) (hl : 2 ≤ l)
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
            ‖fifthCriticalBlockSum (q := p ^ l) p (p ^ (l - 2))
              (x.val : Int) a₀ a₁ a₂ a₃ a₄‖ ≤
          B * (p : Real) ^
            ((fifthCriticalExponent p (x.val : Int)
              a₀ a₁ a₂ a₃ a₄ : Real) / 5 - 1)) :
    ‖integerPolynomialCompleteSum (q := p ^ l)
        a₀ a₁ a₂ a₃ a₄‖ ≤ B := by
  have hmodulus : p * (p * p ^ (l - 2)) = p ^ l := by
    calc
      p * (p * p ^ (l - 2)) = p ^ 2 * p ^ (l - 2) := by ring
      _ = p ^ (2 + (l - 2)) := by rw [pow_add]
      _ = p ^ l := by congr 1; omega
  have h := norm_integerPolynomialCompleteSum_le_of_valuation_block_bounds
    p (p ^ (l - 2)) hp a₀ a₁ a₂ a₃ a₄ hcoeff B hB
  have hblocks' :
      ∀ x ∈ fifthDerivativeRoots
          (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
          (a₃ : ZMod p) (a₄ : ZMod p),
        (p : Real) *
            ‖fifthCriticalBlockSum
              (q := p * (p * p ^ (l - 2))) p (p ^ (l - 2))
              (x.val : Int) a₀ a₁ a₂ a₃ a₄‖ ≤
          B * (p : Real) ^
            ((padicValInt p
              (fifthCriticalTranslate p (x.val : Int)
                a₀ a₁ a₂ a₃ a₄).content : Real) / 5 - 1) := by
    intro x hx
    simpa only [hmodulus, fifthCriticalExponent] using hblocks x hx
  simpa only [hmodulus] using h hblocks'

/-- Exact scaling identity for a nonterminal critical block. -/
theorem chenFour_nonterminal_scale_identity
    (p l sigma : Nat) (K : Real) (hp : p.Prime)
    (htwo : 2 ≤ sigma) (hle : sigma ≤ l) :
    (p : Real) * (p ^ (sigma - 2) : Nat) *
        (K * (p : Real) ^ (((4 * (l - sigma) : Nat) : Real) / 5)) =
      (K * (p : Real) ^ (((4 * l : Nat) : Real) / 5)) *
        (p : Real) ^ ((sigma : Real) / 5 - 1) := by
  have hpReal : (0 : Real) < p := by exact_mod_cast hp.pos
  have hsubSigma : ((sigma - 2 : Nat) : Real) = (sigma : Real) - 2 := by
    rw [Nat.cast_sub htwo]
    norm_num
  have hsubL : ((l - sigma : Nat) : Real) = (l : Real) - sigma := by
    rw [Nat.cast_sub hle]
  have hexponent :
      (1 : Real) + (sigma - 2 : Nat) +
          ((4 * (l - sigma) : Nat) : Real) / 5 =
        ((4 * l : Nat) : Real) / 5 + ((sigma : Real) / 5 - 1) := by
    rw [hsubSigma]
    push_cast
    rw [hsubL]
    ring
  calc
    (p : Real) * (p ^ (sigma - 2) : Nat) *
        (K * (p : Real) ^ (((4 * (l - sigma) : Nat) : Real) / 5)) =
        K * ((p : Real) * (p ^ (sigma - 2) : Nat) *
          (p : Real) ^ (((4 * (l - sigma) : Nat) : Real) / 5)) := by ring
    _ = K * (p : Real) ^
        ((1 : Real) + (sigma - 2 : Nat) +
          ((4 * (l - sigma) : Nat) : Real) / 5) := by
      rw [Real.rpow_add hpReal, Real.rpow_add hpReal,
        Real.rpow_one, Real.rpow_natCast]
      norm_cast
    _ = K * (p : Real) ^
        (((4 * l : Nat) : Real) / 5 + ((sigma : Real) / 5 - 1)) := by
      rw [hexponent]
    _ = (K * (p : Real) ^ (((4 * l : Nat) : Real) / 5)) *
        (p : Real) ^ ((sigma : Real) / 5 - 1) := by
      rw [Real.rpow_add hpReal]
      ring

/-- The constant-phase terminal block fits the same normalized weight as the
nonterminal induction branch. -/
theorem chenFour_terminal_scale_le
    (p l sigma : Nat) (K : Real) (hp : p.Prime)
    (hK : 1 ≤ K) (hl : 2 ≤ l) (hle : l ≤ sigma) :
    (p : Real) * (p ^ (l - 2) : Nat) ≤
      (K * (p : Real) ^ (((4 * l : Nat) : Real) / 5)) *
        (p : Real) ^ ((sigma : Real) / 5 - 1) := by
  have hpOne : (1 : Real) ≤ p := by exact_mod_cast hp.one_le
  have hleft : 0 ≤ (p : Real) * (p ^ (l - 2) : Nat) := by positivity
  have hB : 0 ≤ K * (p : Real) ^ (((4 * l : Nat) : Real) / 5) := by
    exact mul_nonneg (le_trans (by norm_num) hK) (Real.rpow_nonneg (by positivity) _)
  have hidentity := chenFour_nonterminal_scale_identity p l l K hp hl le_rfl
  have hidentity' :
      (p : Real) * (p ^ (l - 2) : Nat) * K =
        (K * (p : Real) ^ (((4 * l : Nat) : Real) / 5)) *
          (p : Real) ^ ((l : Real) / 5 - 1) := by
    simpa using hidentity
  have hexponent : (l : Real) / 5 - 1 ≤ (sigma : Real) / 5 - 1 := by
    have hleReal : (l : Real) ≤ sigma := by exact_mod_cast hle
    linarith
  calc
    (p : Real) * (p ^ (l - 2) : Nat) =
        ((p : Real) * (p ^ (l - 2) : Nat)) * 1 := by ring
    _ ≤ ((p : Real) * (p ^ (l - 2) : Nat)) * K :=
      mul_le_mul_of_nonneg_left hK hleft
    _ = (K * (p : Real) ^ (((4 * l : Nat) : Real) / 5)) *
        (p : Real) ^ ((l : Real) / 5 - 1) := hidentity'
    _ ≤ (K * (p : Real) ^ (((4 * l : Nat) : Real) / 5)) *
        (p : Real) ^ ((sigma : Real) / 5 - 1) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hpOne hexponent) hB

/-- A primitive prime-field bound propagates to every positive prime power by
Chen's stationary-root induction. -/
theorem chenFour_primePower_bound_of_primeField
    (p : Nat) [Fact p.Prime] [NeZero p] (hp : 11 ≤ p)
    (K : Real) (hK : 1 ≤ K) (hprime : ChenFourPrimeFieldBound p K) :
    ∀ l : Nat, 0 < l → ∀ a₀ a₁ a₂ a₃ a₄ : Int,
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
        (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
        (a₄ : ZMod p) ≠ 0 →
      ‖integerPolynomialCompleteSum (q := p ^ l)
          a₀ a₁ a₂ a₃ a₄‖ ≤
        K * (p : Real) ^ (((4 * l : Nat) : Real) / 5) := by
  intro l
  induction l using Nat.strong_induction_on with
  | h l ih =>
      intro hl a₀ a₁ a₂ a₃ a₄ hcoeff
      by_cases hlOne : l = 1
      · subst l
        simpa [ChenFourPrimeFieldBound] using
          hprime a₀ a₁ a₂ a₃ a₄ hcoeff
      · have hlTwo : 2 ≤ l := by omega
        have hK0 : 0 ≤ K := (by norm_num : (0 : Real) ≤ 1).trans hK
        apply norm_integerPolynomialCompleteSum_primePower_le_of_valuation_blocks
          p l hp hlTwo a₀ a₁ a₂ a₃ a₄ hcoeff
          (K * (p : Real) ^ (((4 * l : Nat) : Real) / 5))
          (mul_nonneg hK0 (Real.rpow_nonneg (by positivity) _))
        intro x hx
        let sigma := fifthCriticalExponent p (x.val : Int)
          a₀ a₁ a₂ a₃ a₄
        let G := fifthCriticalQuotient p (x.val : Int)
          a₀ a₁ a₂ a₃ a₄
        have hderivative :
            fifthPolynomialDerivative
              (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
              (a₃ : ZMod p) (a₄ : ZMod p) ≠ 0 :=
          fifthPolynomialDerivative_ne_zero Fact.out hp _ _ _ _ _ hcoeff
        have hxEval :
            (fifthPolynomialDerivative
              (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
              (a₃ : ZMod p) (a₄ : ZMod p)).eval x = 0 :=
          (eval_fifthPolynomialDerivative_eq_zero_iff_mem_roots
            _ _ _ _ _ x hderivative).mpr hx
        have hroot :
            (fifthPolynomialDerivative
              (a₀ : ZMod p) (a₁ : ZMod p) (a₂ : ZMod p)
              (a₃ : ZMod p) (a₄ : ZMod p)).eval
                ((x.val : Int) : ZMod p) = 0 := by
          simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hxEval
        have hsigma := fifthCriticalExponent_mem_interval hp (x.val : Int)
          a₀ a₁ a₂ a₃ a₄ hcoeff hroot
        have htwo : 2 ≤ sigma := by simpa only [sigma] using hsigma.1
        by_cases hsigmaLt : sigma < l
        · have hsigmaLe : sigma ≤ l := Nat.le_of_lt hsigmaLt
          have hsmaller : l - sigma < l := by omega
          have hpositive : 0 < l - sigma := by omega
          have hprimitive :
              (G.coeff 5 : ZMod p) ≠ 0 ∨ (G.coeff 4 : ZMod p) ≠ 0 ∨
                (G.coeff 3 : ZMod p) ≠ 0 ∨ (G.coeff 2 : ZMod p) ≠ 0 ∨
                (G.coeff 1 : ZMod p) ≠ 0 := by
            simpa only [G] using
              fifthCriticalQuotient_coefficients_primitive hp (x.val : Int)
                a₀ a₁ a₂ a₃ a₄ hcoeff
          have hrec := ih (l - sigma) hsmaller hpositive
            (G.coeff 5) (G.coeff 4) (G.coeff 3) (G.coeff 2) (G.coeff 1)
            hprimitive
          have hblock :=
            fifthCriticalBlockSum_primePower_eq_repeated_quotient
              p l (x.val : Int) a₀ a₁ a₂ a₃ a₄
                (by simpa only [sigma] using htwo)
                (by simpa only [sigma] using hsigmaLe)
          calc
            (p : Real) *
                ‖fifthCriticalBlockSum (q := p ^ l) p (p ^ (l - 2))
                  (x.val : Int) a₀ a₁ a₂ a₃ a₄‖ =
              (p : Real) * (p ^ (sigma - 2) : Nat) *
                ‖integerPolynomialCompleteSum (q := p ^ (l - sigma))
                  (G.coeff 5) (G.coeff 4) (G.coeff 3)
                  (G.coeff 2) (G.coeff 1)‖ := by
                rw [hblock, norm_mul]
                dsimp only [sigma, G]
                norm_cast
                push_cast
                ring
            _ ≤ (p : Real) * (p ^ (sigma - 2) : Nat) *
                (K * (p : Real) ^
                  (((4 * (l - sigma) : Nat) : Real) / 5)) :=
              mul_le_mul_of_nonneg_left hrec (by positivity)
            _ = (K * (p : Real) ^ (((4 * l : Nat) : Real) / 5)) *
                (p : Real) ^ ((sigma : Real) / 5 - 1) :=
              chenFour_nonterminal_scale_identity
                p l sigma K Fact.out htwo hsigmaLe
            _ = (K * (p : Real) ^ (((4 * l : Nat) : Real) / 5)) *
                (p : Real) ^
                  ((fifthCriticalExponent p (x.val : Int)
                    a₀ a₁ a₂ a₃ a₄ : Real) / 5 - 1) := by rfl
        · have hlSigma : l ≤ sigma := Nat.le_of_not_gt hsigmaLt
          calc
            (p : Real) *
                ‖fifthCriticalBlockSum (q := p ^ l) p (p ^ (l - 2))
                  (x.val : Int) a₀ a₁ a₂ a₃ a₄‖ =
              (p : Real) * (p ^ (l - 2) : Nat) := by
                rw [norm_fifthCriticalBlockSum_primePower_of_le_exponent
                  p l (x.val : Int) a₀ a₁ a₂ a₃ a₄
                    (by simpa only [sigma] using hlSigma)]
                norm_cast
            _ ≤ (K * (p : Real) ^ (((4 * l : Nat) : Real) / 5)) *
                (p : Real) ^ ((sigma : Real) / 5 - 1) :=
              chenFour_terminal_scale_le p l sigma K Fact.out hK hlTwo hlSigma
            _ = (K * (p : Real) ^ (((4 * l : Nat) : Real) / 5)) *
                (p : Real) ^
                  ((fifthCriticalExponent p (x.val : Int)
                    a₀ a₁ a₂ a₃ a₄ : Real) / 5 - 1) := by rfl

/-- Source-shaped version of the conditional prime-power induction. -/
theorem chenFour_primePower_rpow_bound_of_primeField
    (p l : Nat) [Fact p.Prime] [NeZero p] (hp : 11 ≤ p)
    (K : Real) (hK : 1 ≤ K) (hprime : ChenFourPrimeFieldBound p K)
    (hl : 0 < l) (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
      (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
      (a₄ : ZMod p) ≠ 0) :
    ‖integerPolynomialCompleteSum (q := p ^ l)
        a₀ a₁ a₂ a₃ a₄‖ ≤
      K * (((p ^ l : Nat) : Real) ^ (4 / 5 : Real)) := by
  rw [primePow_rpow_four_fifths]
  exact chenFour_primePower_bound_of_primeField p hp K hK hprime
    l hl a₀ a₁ a₂ a₃ a₄ hcoeff

/-- Chen's exact source constant, conditional only on the corresponding
primitive prime-field estimate. -/
theorem chenFour_primePower_bound_of_exact_primeField
    (p l : Nat) [Fact p.Prime] [NeZero p] (hp : 11 ≤ p)
    (hprime : ChenFourPrimeFieldBound p (chenFourPrimeFactor p))
    (hl : 0 < l) (a₀ a₁ a₂ a₃ a₄ : Int)
    (hcoeff :
      (a₀ : ZMod p) ≠ 0 ∨ (a₁ : ZMod p) ≠ 0 ∨
      (a₂ : ZMod p) ≠ 0 ∨ (a₃ : ZMod p) ≠ 0 ∨
      (a₄ : ZMod p) ≠ 0) :
    ‖integerPolynomialCompleteSum (q := p ^ l)
        a₀ a₁ a₂ a₃ a₄‖ ≤
      chenFourPrimeFactor p *
        (((p ^ l : Nat) : Real) ^ (4 / 5 : Real)) := by
  exact chenFour_primePower_rpow_bound_of_primeField p l hp
    (chenFourPrimeFactor p) (one_le_chenFourPrimeFactor p) hprime
    hl a₀ a₁ a₂ a₃ a₄ hcoeff

end Waring.Analytic
