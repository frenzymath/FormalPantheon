import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log

/-!
# Finite dyadic decomposition

This file provides the natural-number dyadic partition and scale-count bound
used in Akbary--Hambrook's treatment of the large third Vaughan term.

Source: `AkbaryHambrook2013v2`, Section 6, pp. 21--22, preceding equation
(6.13). Semantic review: `SEM-456`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

/-- The positive natural numbers in the half-open dyadic block
`(2^alpha, 2^(alpha+1)]`. -/
def dyadicBlock (alpha : ℕ) : Finset ℕ :=
  Finset.Ioc (2 ^ alpha) (2 ^ (alpha + 1))

/-- Candidate dyadic exponents through the positive natural cap `X`. -/
def dyadicExponentRange (X : ℕ) : Finset ℕ :=
  Finset.range (Nat.log 2 X + 1)

/-- For `t >= 2`, the unique dyadic block containing `t` is indexed by
`log_2 (t - 1)`. The predecessor is essential at powers of two. -/
theorem mem_dyadicBlock_iff_log_pred_eq
    {t alpha : ℕ} (ht : 2 ≤ t) :
    t ∈ dyadicBlock alpha ↔ Nat.log 2 (t - 1) = alpha := by
  rw [dyadicBlock, Finset.mem_Ioc]
  constructor
  · intro hblock
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · omega
    · omega
  · intro hlog
    have htPred : t - 1 ≠ 0 := by omega
    have hlower := Nat.pow_log_le_self 2 htPred
    have hupper := Nat.lt_pow_succ_log_self (by omega : 1 < 2) (t - 1)
    rw [hlog] at hlower hupper
    constructor
    · omega
    · simpa only [Nat.succ_eq_add_one] using (show t ≤ 2 ^ alpha.succ by omega)

/-- A finite set contained in `[2, X]` is the disjoint sum of its
intersections with the candidate dyadic blocks through `X`. -/
theorem sum_eq_sum_dyadicBlocks
    {A : Type*} [AddCommMonoid A] {X : ℕ}
    (s : Finset ℕ) (hs : ∀ t ∈ s, 2 ≤ t ∧ t ≤ X)
    (f : ℕ → A) :
    (∑ t ∈ s, f t) =
      ∑ alpha ∈ dyadicExponentRange X,
        ∑ t ∈ s.filter (fun t ↦ t ∈ dyadicBlock alpha), f t := by
  let exponent : ℕ → ℕ := fun t ↦ Nat.log 2 (t - 1)
  have hmaps : ∀ t ∈ s, exponent t ∈ dyadicExponentRange X := by
    intro t ht
    rw [dyadicExponentRange, Finset.mem_range]
    have htX := (hs t ht).2
    have hlog : Nat.log 2 (t - 1) ≤ Nat.log 2 X :=
      Nat.log_mono_right (by omega)
    exact Nat.lt_succ_of_le hlog
  have hfiber (alpha : ℕ) :
      s.filter (fun t ↦ t ∈ dyadicBlock alpha) =
        s.filter (fun t ↦ exponent t = alpha) := by
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ht, hblock⟩
      exact ⟨ht, (mem_dyadicBlock_iff_log_pred_eq (hs t ht).1).mp hblock⟩
    · rintro ⟨ht, hlog⟩
      exact ⟨ht, (mem_dyadicBlock_iff_log_pred_eq (hs t ht).1).mpr hlog⟩
  symm
  calc
    (∑ alpha ∈ dyadicExponentRange X,
        ∑ t ∈ s.filter (fun t ↦ t ∈ dyadicBlock alpha), f t) =
        ∑ alpha ∈ dyadicExponentRange X,
          ∑ t ∈ s.filter (fun t ↦ exponent t = alpha), f t := by
      apply Finset.sum_congr rfl
      intro alpha _halpha
      rw [hfiber]
    _ = ∑ t ∈ s, f t :=
      Finset.sum_fiberwise_of_maps_to hmaps f

/-- The number of candidate dyadic exponents through a positive natural cap
is at most `log(2X) / log 2`. -/
theorem card_dyadicExponentRange_le_log
    {X : ℕ} (hX : 0 < X) :
    ((dyadicExponentRange X).card : ℝ) ≤
      Real.log (2 * (X : ℝ)) / Real.log 2 := by
  have hpowNat : 2 ^ (Nat.log 2 X + 1) ≤ 2 * X := by
    calc
      2 ^ (Nat.log 2 X + 1) = 2 ^ Nat.log 2 X * 2 := by rw [pow_succ]
      _ ≤ X * 2 := Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 hX.ne')
      _ = 2 * X := Nat.mul_comm X 2
  have hpowReal :
      (2 : ℝ) ^ (Nat.log 2 X + 1) ≤ 2 * (X : ℝ) := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log
    (pow_pos (by norm_num : (0 : ℝ) < 2) (Nat.log 2 X + 1)) hpowReal
  rw [Real.log_pow] at hlog
  rw [dyadicExponentRange, Finset.card_range]
  exact (le_div_iff₀ (Real.log_pos (by norm_num))).2 hlog

end BoundedGaps.Maynard
