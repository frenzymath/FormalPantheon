import Waring.Analytic.CRTNormalization

/-!
# Complete fifth-power sums at powers of five

This file extends the block cancellation in Chen's Lemma 3 to the exact
recurrence needed for the `p=5` branch of Lemma 2.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Complete sums with natural coefficients agree across propositionally equal
natural moduli. This isolates transport of the nonzero-modulus witness. -/
theorem completePowerSum_natCast_modulus_congr {q r : Nat} [NeZero q] [NeZero r]
    (h : q = r) (k a : Nat) :
    completePowerSum k ((a : Nat) : ZMod q) =
      completePowerSum k ((a : Nat) : ZMod r) := by
  subst r
  rfl

/-- Standard-character values of natural residues agree across propositionally
equal natural moduli. -/
theorem stdAddChar_natCast_modulus_congr {q r : Nat} [NeZero q] [NeZero r]
    (h : q = r) (x : Nat) :
    ZMod.stdAddChar ((x : Nat) : ZMod q) =
      ZMod.stdAddChar ((x : Nat) : ZMod r) := by
  subst r
  rfl

/-- Cancelling the common factor `5^5` in a fifth-power phase preserves the
standard additive character. -/
theorem stdAddChar_fifth_fiveScale (u : Nat) [NeZero u] (a y : Nat) :
    ZMod.stdAddChar
        ((a * (5 * y) ^ 5 : Nat) : ZMod (3125 * u)) =
      ZMod.stdAddChar ((a * y ^ 5 : Nat) : ZMod u) := by
  calc
    ZMod.stdAddChar ((a * (5 * y) ^ 5 : Nat) : ZMod (3125 * u)) =
        Complex.exp
          (2 * Real.pi * Complex.I * ((a * (5 * y) ^ 5 : Nat) : Complex) /
            ((3125 * u : Nat) : Complex)) := by
      simpa only [Int.cast_natCast] using
        ZMod.stdAddChar_coe (N := 3125 * u) ((a * (5 * y) ^ 5 : Nat) : Int)
    _ = Complex.exp
        (2 * Real.pi * Complex.I * ((a * y ^ 5 : Nat) : Complex) / (u : Complex)) := by
      congr 1
      push_cast
      have hu : (u : Complex) ≠ 0 := by exact_mod_cast NeZero.ne u
      field_simp [hu]
      ring
    _ = ZMod.stdAddChar ((a * y ^ 5 : Nat) : ZMod u) := by
      symm
      simpa only [Int.cast_natCast] using
        ZMod.stdAddChar_coe (N := u) ((a * y ^ 5 : Nat) : Int)

/-- The character scaling identity in the modulus shape produced directly by
Chen's block decomposition. -/
theorem stdAddChar_fifth_fiveScale_block (u : Nat) [NeZero u] (a y : Nat) :
    ZMod.stdAddChar
        (((a : Nat) : ZMod (25 * (5 * (25 * u)))) *
          (((5 * y : Nat) : ZMod (25 * (5 * (25 * u)))) ^ 5)) =
      ZMod.stdAddChar ((a * y ^ 5 : Nat) : ZMod u) := by
  have hmod : 25 * (5 * (25 * u)) = 3125 * u := by ring
  calc
    ZMod.stdAddChar
        (((a : Nat) : ZMod (25 * (5 * (25 * u)))) *
          (((5 * y : Nat) : ZMod (25 * (5 * (25 * u)))) ^ 5)) =
        ZMod.stdAddChar
          ((a * (5 * y) ^ 5 : Nat) : ZMod (25 * (5 * (25 * u)))) := by
      congr 1
      push_cast
      rfl
    _ = ZMod.stdAddChar ((a * (5 * y) ^ 5 : Nat) : ZMod (3125 * u)) :=
      stdAddChar_natCast_modulus_congr hmod _
    _ = ZMod.stdAddChar ((a * y ^ 5 : Nat) : ZMod u) :=
      stdAddChar_fifth_fiveScale u a y

/-- A complete fifth-power sum with a natural coefficient, written over the
canonical finite set of natural representatives. -/
theorem completePowerSum_fifth_natCast_eq_fin (u : Nat) [NeZero u] (a : Nat) :
    completePowerSum 5 ((a : Nat) : ZMod u) =
      ∑ y : Fin u,
        ZMod.stdAddChar ((a * y.val ^ 5 : Nat) : ZMod u) := by
  rw [completePowerSum, powerSum]
  rw [← (ZMod.finEquiv u).toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  change ZMod.stdAddChar
      (((a : Nat) : ZMod u) * (ZMod.finEquiv u y) ^ 5) = _
  rw [zmod_finEquiv_apply]
  congr 1
  push_cast
  rfl

/-- After Chen's 25-term cancellation, the surviving residues modulo
`3125*u` are exactly the multiples of five. -/
theorem completePowerSum_fifth_eq_fiveMultiples (u : Nat) [NeZero u]
    (a : Nat) (ha : a.Coprime 5) :
    completePowerSum 5 ((a : Nat) : ZMod (25 * (5 * (25 * u)))) =
      ∑ y : Fin (25 * u),
        (25 : Complex) * ZMod.stdAddChar
          (((a : Nat) : ZMod (25 * (5 * (25 * u)))) *
            (((5 * y.val : Nat) : ZMod (25 * (5 * (25 * u)))) ^ 5)) := by
  have h := completePowerSum_fifth_eq_survivors (25 * u) a ha
  refine h.trans ?_
  rw [← (finFiveBlocks (25 * u)).sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  rw [Fin.sum_univ_five]
  have h1 : ¬5 ∣ 1 + 5 * y.val := by omega
  have h2 : ¬5 ∣ 2 + 5 * y.val := by omega
  have h3 : ¬5 ∣ 3 + 5 * y.val := by omega
  have h4 : ¬5 ∣ 4 + 5 * y.val := by omega
  simp only [finFiveBlocks_val]
  simp [h1, h2, h3, h4]

/-- Cancelling the common fifth-power factor rewrites every surviving phase as
a phase modulo `u`. -/
theorem completePowerSum_fifth_eq_scaledResidues (u : Nat) [NeZero u]
    (a : Nat) (ha : a.Coprime 5) :
    completePowerSum 5 ((a : Nat) : ZMod (25 * (5 * (25 * u)))) =
      ∑ y : Fin (25 * u),
        (25 : Complex) *
          ZMod.stdAddChar ((a * y.val ^ 5 : Nat) : ZMod u) := by
  rw [completePowerSum_fifth_eq_fiveMultiples u a ha]
  apply Finset.sum_congr rfl
  intro y _
  rw [stdAddChar_fifth_fiveScale_block]

/-- Exact five-adic recurrence in the modulus shape obtained from Chen's block
decomposition. -/
theorem completePowerSum_fifth_recurrence_block (u : Nat) [NeZero u]
    (a : Nat) (ha : a.Coprime 5) :
    completePowerSum 5 ((a : Nat) : ZMod (25 * (5 * (25 * u)))) =
      625 * completePowerSum 5 ((a : Nat) : ZMod u) := by
  rw [completePowerSum_fifth_eq_scaledResidues u a ha]
  rw [← (finProdFinEquiv : Fin 25 × Fin u ≃ Fin (25 * u)).sum_comp]
  rw [Fintype.sum_prod_type]
  rw [completePowerSum_fifth_natCast_eq_fin]
  calc
    ∑ xi : Fin 25, ∑ y : Fin u,
        (25 : Complex) * ZMod.stdAddChar
          ((a * (finProdFinEquiv (xi, y)).val ^ 5 : Nat) : ZMod u) =
        ∑ _xi : Fin 25, ∑ y : Fin u,
          (25 : Complex) * ZMod.stdAddChar
            ((a * y.val ^ 5 : Nat) : ZMod u) := by
      apply Finset.sum_congr rfl
      intro xi _
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      apply congrArg ZMod.stdAddChar
      push_cast
      have hy :
          (((finProdFinEquiv (xi, y)).val : Nat) : ZMod u) =
            ((y.val : Nat) : ZMod u) := by
        change ((y.val + u * xi.val : Nat) : ZMod u) = _
        push_cast
        rw [ZMod.natCast_self]
        simp
      rw [hy]
    _ = 625 * ∑ y : Fin u,
        ZMod.stdAddChar ((a * y.val ^ 5 : Nat) : ZMod u) := by
      simp only [Finset.mul_sum]
      simp
      rw [← Finset.mul_sum]
      rw [← Finset.mul_sum]
      ring

/-- Exact recurrence for complete fifth-power sums when the modulus is
multiplied by `5^5=3125`. -/
theorem completePowerSum_fifth_recurrence (u : Nat) [NeZero u]
    (a : Nat) (ha : a.Coprime 5) :
    completePowerSum 5 ((a : Nat) : ZMod (3125 * u)) =
      625 * completePowerSum 5 ((a : Nat) : ZMod u) := by
  calc
    completePowerSum 5 ((a : Nat) : ZMod (3125 * u)) =
        completePowerSum 5 ((a : Nat) : ZMod (25 * (5 * (25 * u)))) := by
      apply completePowerSum_natCast_modulus_congr
      ring
    _ = 625 * completePowerSum 5 ((a : Nat) : ZMod u) :=
      completePowerSum_fifth_recurrence_block u a ha

/-- Increasing a power-of-five modulus exponent by five multiplies the
complete sum by `5^4`. -/
theorem completePowerSum_fifth_pow_add_five (alpha a : Nat)
    (ha : a.Coprime 5) :
    completePowerSum 5 ((a : Nat) : ZMod (5 ^ (alpha + 5))) =
      625 * completePowerSum 5 ((a : Nat) : ZMod (5 ^ alpha)) := by
  calc
    completePowerSum 5 ((a : Nat) : ZMod (5 ^ (alpha + 5))) =
        completePowerSum 5 ((a : Nat) : ZMod (3125 * 5 ^ alpha)) := by
      apply completePowerSum_natCast_modulus_congr
      rw [pow_add]
      norm_num
      ring
    _ = 625 * completePowerSum 5 ((a : Nat) : ZMod (5 ^ alpha)) :=
      completePowerSum_fifth_recurrence (5 ^ alpha) a ha

/-- Chen's real-valued `p=5` bound has exactly the same five-step scaling as
the complete sum recurrence. -/
theorem five_rpow_four_fifths_add_five (alpha : Nat) :
    (625 : Real) *
        ((5 : Real) * (5 : Real) ^ (((4 * alpha : Nat) : Real) / 5)) =
      (5 : Real) *
        (5 : Real) ^ (((4 * (alpha + 5) : Nat) : Real) / 5) := by
  have hexponent :
      (((4 * (alpha + 5) : Nat) : Real) / 5) =
        (((4 * alpha : Nat) : Real) / 5) + 4 := by
    push_cast
    ring
  rw [hexponent, Real.rpow_add (by norm_num : (0 : Real) < 5)]
  norm_num [Real.rpow_natCast]
  ring

/-- For the five initial exponent classes, the trivial complete-sum bound is
already at most Chen's printed `p=5` bound. -/
theorem five_pow_le_five_rpow_four_fifths {alpha : Nat} (hAlpha : alpha ≤ 5) :
    ((5 ^ alpha : Nat) : Real) ≤
      (5 : Real) * (5 : Real) ^ (((4 * alpha : Nat) : Real) / 5) := by
  have hExponent :
      (alpha : Real) ≤ 1 + (((4 * alpha : Nat) : Real) / 5) := by
    have hAlphaReal : (alpha : Real) ≤ 5 := by exact_mod_cast hAlpha
    push_cast
    linarith
  calc
    ((5 ^ alpha : Nat) : Real) = (5 : Real) ^ (alpha : Real) := by
      norm_num [Real.rpow_natCast]
    _ ≤ (5 : Real) ^ (1 + (((4 * alpha : Nat) : Real) / 5)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hExponent
    _ = (5 : Real) * (5 : Real) ^ (((4 * alpha : Nat) : Real) / 5) := by
      rw [Real.rpow_add (by norm_num : (0 : Real) < 5)]
      norm_num

/-- The independently reconstructed `p=5` branch of Chen's Lemma 2, valid for
every positive prime-power exponent. -/
theorem chen_two_five_primePower {alpha : Nat} (hAlpha : 0 < alpha)
    (a : Nat) (ha : a.Coprime 5) :
    ‖completePowerSum 5 ((a : Nat) : ZMod (5 ^ alpha))‖ ≤
      (5 : Real) * (5 : Real) ^ (((4 * alpha : Nat) : Real) / 5) := by
  revert hAlpha
  refine Nat.strong_induction_on alpha ?_
  intro alpha ih hAlpha
  by_cases hInitial : alpha ≤ 5
  · exact (norm_completePowerSum_le 5
      ((a : Nat) : ZMod (5 ^ alpha))).trans
        (five_pow_le_five_rpow_four_fifths hInitial)
  · let beta := alpha - 5
    have hBetaLt : beta < alpha := by omega
    have hBetaPos : 0 < beta := by omega
    have hAlphaEq : alpha = beta + 5 := by omega
    have hInduction := ih beta hBetaLt hBetaPos
    rw [hAlphaEq, completePowerSum_fifth_pow_add_five beta a ha, norm_mul]
    norm_num
    calc
      (625 : Real) *
          ‖completePowerSum 5 ((a : Nat) : ZMod (5 ^ beta))‖ ≤
          625 *
            ((5 : Real) * (5 : Real) ^ (((4 * beta : Nat) : Real) / 5)) :=
        mul_le_mul_of_nonneg_left hInduction (by norm_num)
      _ = (5 : Real) *
          (5 : Real) ^ (4 * ((beta : Real) + 5) / 5) := by
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using
          five_rpow_four_fifths_add_five beta

end Waring.Analytic
