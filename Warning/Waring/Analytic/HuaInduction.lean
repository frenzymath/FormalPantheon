import Waring.Analytic.HuaLongRange

/-!
# Hua's fixed-degree prime-power induction

This file proves Hua's strong induction invariant for every degree-five phase
at a prime below eleven [HUA1957-BOOK, pp. 5-7].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Hua's source-shaped strong invariant, specialized to ambient degree five.
The factor `max 1 complexity` makes the short range uniform and the child
complexity estimate closes every nonterminal root block. -/
theorem hua_primePower_strong_bound
    (p : Nat) [Fact p.Prime] [NeZero p] (hpSmall : p < 11) :
    ∀ l : Nat, 0 < l → ∀ (F : Polynomial Int),
      (phase : HuaPhaseData p F) →
      ‖integerFormalPolynomialCompleteSum (q := p ^ l) F‖ ≤
        25 * (Nat.max 1 phase.complexity : Nat) *
          (p : Real) ^ (((4 * l : Nat) : Real) / 5) := by
  intro l
  induction l using Nat.strong_induction_on with
  | h l ih =>
      intro hl F phase
      by_cases hlong : 2 * (phase.derivativeData.exponent + 1) ≤ l
      · have hreduce :=
          norm_integerFormalPolynomialCompleteSum_primePower_le_huaCriticalBlocks
            phase hlong
        have hblocks : ∀ x ∈ phase.roots,
            ‖huaCriticalBlockSum (q := p ^ l)
              p (p ^ (l - 1)) (x.val : Int) F‖ ≤
              25 * (phase.multiplicity x : Nat) *
                (p : Real) ^ (((4 * l : Nat) : Real) / 5) := by
          intro x hx
          have hxEval :
              (phase.derivativeData.normalized.map
                (Int.castRingHom (ZMod p))).eval x = 0 := by
            apply (Polynomial.mem_roots
              phase.derivativeData.map_normalized_ne_zero).1
            simpa only [HuaPhaseData.roots, HuaDerivativeData.roots,
              Multiset.mem_toFinset] using hx
          have hroot :
              (phase.derivativeData.normalized.map
                (Int.castRingHom (ZMod p))).eval
                  ((x.val : Int) : ZMod p) = 0 := by
            simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hxEval
          let T := scaledTaylorDifference (p : Int) (x.val : Int) F
          let sigma := padicValInt p T.content
          let G := primePowerContentQuotient p T
          have hsigmaTwo : 2 ≤ sigma := by
            dsimp only [sigma, T]
            exact two_le_padicValInt_content_scaledTaylorDifference
              phase (x.val : Int) hroot
          have hsigmaFive : sigma ≤ 5 := by
            dsimp only [sigma, T]
            exact padicValInt_content_scaledTaylorDifference_le_five
              phase (x.val : Int)
          have hmultPos : 1 ≤ phase.multiplicity x :=
            phase.derivativeData.multiplicity_pos_of_mem hx
          obtain ⟨child, hchild⟩ :=
            exists_childHuaPhaseData phase (x.val : Int)
          have hchild' : child.complexity ≤ phase.multiplicity x := by
            simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hchild
          have hmaxChild : Nat.max 1 child.complexity ≤
              phase.multiplicity x := max_le hmultPos hchild'
          by_cases hsigmaLt : sigma < l
          · have hsigmaLe : sigma ≤ l := Nat.le_of_lt hsigmaLt
            have hsmaller : l - sigma < l := by omega
            have hpositive : 0 < l - sigma := by omega
            have hrec := ih (l - sigma) hsmaller hpositive G child
            have hblock :=
              huaCriticalBlockSum_primePower_eq_repeated_quotient
                p l (x.val : Int) F
                  (by omega : 1 ≤ sigma) hsigmaLe
            dsimp only at hblock
            change huaCriticalBlockSum (q := p ^ l)
                p (p ^ (l - 1)) (x.val : Int) F =
              (p ^ (sigma - 1) : Complex) *
                integerFormalPolynomialCompleteSum
                  (q := p ^ (l - sigma)) G at hblock
            have hscale := hua_nonterminal_block_scale_le
              p l sigma (Fact.out : p.Prime).one_le hsigmaLe hsigmaFive
            calc
              ‖huaCriticalBlockSum (q := p ^ l)
                  p (p ^ (l - 1)) (x.val : Int) F‖ =
                ((p ^ (sigma - 1) : Nat) : Real) *
                  ‖integerFormalPolynomialCompleteSum
                    (q := p ^ (l - sigma)) G‖ := by
                rw [hblock, norm_mul]
                simp
              _ ≤ ((p ^ (sigma - 1) : Nat) : Real) *
                  (25 * (Nat.max 1 child.complexity : Nat) *
                    (p : Real) ^
                      (((4 * (l - sigma) : Nat) : Real) / 5)) :=
                mul_le_mul_of_nonneg_left hrec (by positivity)
              _ = 25 * (Nat.max 1 child.complexity : Nat) *
                  (((p ^ (sigma - 1) : Nat) : Real) *
                    (p : Real) ^
                      (((4 * (l - sigma) : Nat) : Real) / 5)) := by
                ring
              _ ≤ 25 * (phase.multiplicity x : Nat) *
                  (p : Real) ^ (((4 * l : Nat) : Real) / 5) := by
                gcongr
          · have hlSigma : l ≤ sigma := Nat.le_of_not_gt hsigmaLt
            have hlFive : l ≤ 5 := hlSigma.trans hsigmaFive
            have hblock :=
              huaCriticalBlockSum_primePower_eq_card_of_le_exponent
                p l (x.val : Int) F (by
                  simpa only [sigma, T] using hlSigma)
            have hscale := hua_terminal_block_scale_le
              p l (Fact.out : p.Prime).one_le hlFive
            calc
              ‖huaCriticalBlockSum (q := p ^ l)
                  p (p ^ (l - 1)) (x.val : Int) F‖ =
                ((p ^ (l - 1) : Nat) : Real) := by
                rw [hblock]
                simp
              _ ≤ (p : Real) ^ (((4 * l : Nat) : Real) / 5) := hscale
              _ ≤ 25 * (phase.multiplicity x : Nat) *
                  (p : Real) ^ (((4 * l : Nat) : Real) / 5) := by
                have hscaleNonneg : 0 ≤
                    (p : Real) ^ (((4 * l : Nat) : Real) / 5) :=
                  Real.rpow_nonneg (by positivity) _
                apply le_mul_of_one_le_left hscaleNonneg
                have hmultReal : (1 : Real) ≤ phase.multiplicity x := by
                  exact_mod_cast hmultPos
                nlinarith
        calc
          ‖integerFormalPolynomialCompleteSum (q := p ^ l) F‖ ≤
              ∑ x ∈ phase.roots,
                ‖huaCriticalBlockSum (q := p ^ l)
                  p (p ^ (l - 1)) (x.val : Int) F‖ := hreduce
          _ ≤ ∑ x ∈ phase.roots,
              25 * (phase.multiplicity x : Nat) *
                (p : Real) ^ (((4 * l : Nat) : Real) / 5) := by
            apply Finset.sum_le_sum
            intro x hx
            exact hblocks x hx
          _ = 25 * (phase.complexity : Nat) *
                (p : Real) ^ (((4 * l : Nat) : Real) / 5) := by
            change (∑ x ∈ phase.derivativeData.roots,
                25 * (phase.derivativeData.multiplicity x : Nat) *
                  (p : Real) ^ (((4 * l : Nat) : Real) / 5)) =
              25 * ((∑ x ∈ phase.derivativeData.roots,
                phase.derivativeData.multiplicity x) : Nat) *
                  (p : Real) ^ (((4 * l : Nat) : Real) / 5)
            push_cast
            rw [Finset.mul_sum, Finset.sum_mul]
          _ ≤ 25 * (Nat.max 1 phase.complexity : Nat) *
                (p : Real) ^ (((4 * l : Nat) : Real) / 5) := by
            gcongr
            exact le_max_right 1 phase.complexity
      · have hshort : l <
            2 * (phase.derivativeData.exponent + 1) := by omega
        have htrivial := norm_integerFormalPolynomialCompleteSum_le_modulus
          (p ^ l) F
        have hsmall := hua_short_range_scale_le_twentyFive
          p phase.derivativeData.exponent l
            (Fact.out : p.Prime).two_le hpSmall
            phase.pow_derivativeExponent_le_five hshort
        have hpReal : (0 : Real) < p := by
          exact_mod_cast (Fact.out : p.Prime).pos
        have hsplit :
            (((p ^ l : Nat) : Real)) =
              (p : Real) ^ ((l : Real) / 5) *
                (p : Real) ^ (((4 * l : Nat) : Real) / 5) := by
          rw [Nat.cast_pow, ← Real.rpow_natCast]
          rw [← Real.rpow_add hpReal]
          congr 1
          push_cast
          ring
        have hscaleNonneg :
            0 ≤ (p : Real) ^ (((4 * l : Nat) : Real) / 5) :=
          Real.rpow_nonneg (by positivity) _
        have hcomplexity :
            (1 : Real) ≤ (Nat.max 1 phase.complexity : Nat) := by
          exact_mod_cast (le_max_left 1 phase.complexity)
        calc
          ‖integerFormalPolynomialCompleteSum (q := p ^ l) F‖ ≤
              ((p ^ l : Nat) : Real) := htrivial
          _ = (p : Real) ^ ((l : Real) / 5) *
                (p : Real) ^ (((4 * l : Nat) : Real) / 5) := hsplit
          _ ≤ 25 * (p : Real) ^ (((4 * l : Nat) : Real) / 5) :=
            mul_le_mul_of_nonneg_right hsmall hscaleNonneg
          _ ≤ 25 * (Nat.max 1 phase.complexity : Nat) *
                (p : Real) ^ (((4 * l : Nat) : Real) / 5) := by
            apply mul_le_mul_of_nonneg_right _ hscaleNonneg
            nlinarith

end Waring.Analytic
