import Waring.Analytic.DivisorMomentRecurrence
import Waring.Analytic.WeightedDivisorMoments

/-!
# A divisor-weighted reciprocal-LCM bound

This file bounds the reciprocal-LCM sum arising from the second moment of the
triple-divisor count.
-/

namespace Waring.Analytic

open scoped BigOperators

noncomputable section

private def weightedDivisorMultiplesSum (X g : Nat) : Real :=
  ∑ a ∈ Finset.Icc 1 X,
    if g ∣ a then (divisorCount a : Real) / (a : Real) else 0

private lemma weightedDivisorMultiplesSum_eq (X g : Nat) (hg : 0 < g) :
    weightedDivisorMultiplesSum X g =
      ∑ r ∈ Finset.Icc 1 (X / g),
        (divisorCount (g * r) : Real) / (g * r : Nat) := by
  unfold weightedDivisorMultiplesSum
  rw [← Finset.sum_filter]
  have hsum_forward :
      ∑ r ∈ Finset.Icc 1 (X / g),
          (divisorCount (g * r) : Real) / (g * r : Nat) =
        ∑ a ∈ {a ∈ Finset.Icc 1 X | g ∣ a},
          (divisorCount a : Real) / a := by
    apply Finset.sum_bij (fun r _ ↦ g * r)
    · intro r hr
      simp only [Finset.mem_Icc, Finset.mem_filter] at hr ⊢
      refine ⟨⟨Nat.mul_pos hg hr.1, ?_⟩, dvd_mul_right g r⟩
      simpa [mul_comm] using Nat.mul_le_of_le_div g r X hr.2
    · intro r₁ _ r₂ _ h
      exact Nat.eq_of_mul_eq_mul_left hg h
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha
      refine ⟨a / g, ?_, ?_⟩
      · simp only [Finset.mem_Icc]
        constructor
        · exact Nat.div_pos (Nat.le_of_dvd (by omega) ha.2) hg
        · exact Nat.div_le_div_right ha.1.2
      · rw [mul_comm]
        exact Nat.div_mul_cancel ha.2
    · intro r _
      rfl
  exact hsum_forward.symm

private lemma divisorQuotient_mul_le (g r : Nat) (hg : 0 < g)
    (hr : 0 < r) :
    (divisorCount (g * r) : Real) / (g * r : Nat) ≤
      ((divisorCount g : Real) / g) *
        ((divisorCount r : Real) / r) := by
  have hcount : (divisorCount (g * r) : Real) ≤
      (divisorCount g : Real) * divisorCount r := by
    exact_mod_cast divisorCount_mul_le g r
  calc
    (divisorCount (g * r) : Real) / (g * r : Nat) ≤
        ((divisorCount g : Real) * divisorCount r) / (g * r : Nat) :=
      div_le_div_of_nonneg_right hcount (by positivity)
    _ = ((divisorCount g : Real) / g) *
        ((divisorCount r : Real) / r) := by
      norm_num only [Nat.cast_mul]
      field_simp

private lemma weightedDivisorMultiplesSum_le {X g : Nat}
    (hg : g ∈ Finset.Icc 1 X) :
    weightedDivisorMultiplesSum X g ≤
      ((divisorCount g : Real) / g) *
        ((1 : Real) / 2 * (Real.log X + 2) ^ 2) := by
  simp only [Finset.mem_Icc] at hg
  have hgpos : 0 < g := by omega
  have hXpos : 0 < X := hgpos.trans_le hg.2
  have hquotpos : 0 < X / g := Nat.div_pos hg.2 hgpos
  have hlog : Real.log (X / g : Nat) ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast hquotpos)
      (by exact_mod_cast Nat.div_le_self X g)
  have hbase : 0 ≤ Real.log (X / g : Nat) + 2 := by
    have hone : (1 : Real) ≤ (X / g : Nat) := by exact_mod_cast hquotpos
    linarith [Real.log_nonneg hone]
  have hpow : (Real.log (X / g : Nat) + 2) ^ 2 ≤
      (Real.log X + 2) ^ 2 :=
    pow_le_pow_left₀ hbase (by linarith) 2
  rw [weightedDivisorMultiplesSum_eq X g hgpos]
  calc
    (∑ r ∈ Finset.Icc 1 (X / g),
        (divisorCount (g * r) : Real) / (g * r : Nat)) ≤
        ∑ r ∈ Finset.Icc 1 (X / g),
          ((divisorCount g : Real) / g) *
            ((divisorCount r : Real) / r) := by
      apply Finset.sum_le_sum
      intro r hr
      simp only [Finset.mem_Icc] at hr
      exact divisorQuotient_mul_le g r hgpos (by omega)
    _ = ((divisorCount g : Real) / g) *
        ∑ r ∈ Finset.Icc 1 (X / g),
          (divisorCount r : Real) / r := by
      rw [Finset.mul_sum]
    _ ≤ ((divisorCount g : Real) / g) *
        ((1 : Real) / 2 * (Real.log (X / g : Nat) + 2) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (chen_eight_weighted_first_moment (X / g)) (by positivity)
    _ ≤ ((divisorCount g : Real) / g) *
        ((1 : Real) / 2 * (Real.log X + 2) ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by positivity)

private def weightedCommonDivisorTerm (a b g : Nat) : Real :=
  if g ∣ a ∧ g ∣ b then
    (divisorCount a : Real) * divisorCount b * g / ((a : Real) * b)
  else 0

private lemma weighted_inv_lcm_le_commonDivisorSum {X a b : Nat}
    (ha : a ∈ Finset.Icc 1 X) (hb : b ∈ Finset.Icc 1 X) :
    (divisorCount a : Real) * divisorCount b /
        (a.lcm b : Nat) ≤
      ∑ g ∈ Finset.Icc 1 X, weightedCommonDivisorTerm a b g := by
  simp only [Finset.mem_Icc] at ha hb
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hgpos : 0 < a.gcd b := Nat.gcd_pos_of_pos_left b (by omega)
  have hgle : a.gcd b ≤ X :=
    (Nat.gcd_le_left b (by omega)).trans ha.2
  have hgmem : a.gcd b ∈ Finset.Icc 1 X := by
    simp only [Finset.mem_Icc]
    omega
  have hlcm0 : a.lcm b ≠ 0 := Nat.lcm_ne_zero ha0 hb0
  have heq : (divisorCount a : Real) * divisorCount b /
      (a.lcm b : Nat) =
        weightedCommonDivisorTerm a b (a.gcd b) := by
    simp only [weightedCommonDivisorTerm, Nat.gcd_dvd_left,
      Nat.gcd_dvd_right, and_self, if_true]
    have hmul : (a.gcd b : Real) * (a.lcm b : Real) =
        (a : Real) * b := by
      exact_mod_cast Nat.gcd_mul_lcm a b
    field_simp [ha0, hb0, hlcm0]
    ring_nf at hmul ⊢
    rw [hmul]
  calc
    (divisorCount a : Real) * divisorCount b / (a.lcm b : Nat) =
        weightedCommonDivisorTerm a b (a.gcd b) := heq
    _ ≤ ∑ g ∈ Finset.Icc 1 X, weightedCommonDivisorTerm a b g := by
      apply Finset.single_le_sum
      · intro g _
        unfold weightedCommonDivisorTerm
        split_ifs
        · positivity
        · exact le_rfl
      · exact hgmem

private lemma weightedCommonDivisorTerm_eq (a b g : Nat) :
    weightedCommonDivisorTerm a b g =
      (g : Real) *
        (if g ∣ a then (divisorCount a : Real) / a else 0) *
        (if g ∣ b then (divisorCount b : Real) / b else 0) := by
  by_cases ha : g ∣ a
  · by_cases hb : g ∣ b
    · simp [weightedCommonDivisorTerm, ha, hb]
      ring
    · simp [weightedCommonDivisorTerm, ha, hb]
  · by_cases hb : g ∣ b
    · simp [weightedCommonDivisorTerm, ha, hb]
    · simp [weightedCommonDivisorTerm, ha, hb]

private lemma sum_weightedCommonDivisorTerm_eq (X g : Nat) :
    ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
        weightedCommonDivisorTerm a b g =
      (g : Real) * (weightedDivisorMultiplesSum X g) ^ 2 := by
  let f : Nat → Real := fun a ↦
    if g ∣ a then (divisorCount a : Real) / a else 0
  calc
    ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
        weightedCommonDivisorTerm a b g =
        ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
          (g : Real) * f a * f b := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact weightedCommonDivisorTerm_eq a b g
    _ = (g : Real) *
        (∑ a ∈ Finset.Icc 1 X, f a) ^ 2 := by
      calc
        (∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
            (g : Real) * f a * f b) =
            ∑ a ∈ Finset.Icc 1 X,
              ((g : Real) * f a) * ∑ b ∈ Finset.Icc 1 X, f b := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
        _ = (∑ a ∈ Finset.Icc 1 X, (g : Real) * f a) *
            ∑ b ∈ Finset.Icc 1 X, f b := by
          rw [Finset.sum_mul]
        _ = ((g : Real) * ∑ a ∈ Finset.Icc 1 X, f a) *
            ∑ b ∈ Finset.Icc 1 X, f b := by
          congr 1
          exact (Finset.mul_sum _ _ _).symm
        _ = (g : Real) * (∑ a ∈ Finset.Icc 1 X, f a) ^ 2 := by ring
    _ = (g : Real) * (weightedDivisorMultiplesSum X g) ^ 2 := by
      congr 2

/-- A divisor-weighted reciprocal-LCM sum is bounded by the eighth power of
the shifted logarithm. -/
theorem sum_divisorCount_mul_inv_lcm_le (X : Nat) :
    ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
        (divisorCount a : Real) * divisorCount b / (a.lcm b : Nat) ≤
      (1 : Real) / 48 * (Real.log X + 3) ^ 8 := by
  by_cases hX0 : X = 0
  · subst X
    norm_num
  have hX : 1 ≤ X := Nat.one_le_iff_ne_zero.mpr hX0
  have hlog : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  calc
    (∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
        (divisorCount a : Real) * divisorCount b / (a.lcm b : Nat)) ≤
        ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 X,
          ∑ g ∈ Finset.Icc 1 X, weightedCommonDivisorTerm a b g := by
      exact Finset.sum_le_sum fun a ha ↦ Finset.sum_le_sum fun b hb ↦
        weighted_inv_lcm_le_commonDivisorSum ha hb
    _ = ∑ a ∈ Finset.Icc 1 X, ∑ g ∈ Finset.Icc 1 X,
          ∑ b ∈ Finset.Icc 1 X, weightedCommonDivisorTerm a b g := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ g ∈ Finset.Icc 1 X, ∑ a ∈ Finset.Icc 1 X,
          ∑ b ∈ Finset.Icc 1 X, weightedCommonDivisorTerm a b g := by
      rw [Finset.sum_comm]
    _ = ∑ g ∈ Finset.Icc 1 X,
        (g : Real) * (weightedDivisorMultiplesSum X g) ^ 2 := by
      apply Finset.sum_congr rfl
      intro g _
      exact sum_weightedCommonDivisorTerm_eq X g
    _ ≤ ∑ g ∈ Finset.Icc 1 X,
        (1 / 4 : Real) * (Real.log X + 3) ^ 4 *
          ((divisorCount g : Real) ^ 2 / g) := by
      apply Finset.sum_le_sum
      intro g hg
      simp only [Finset.mem_Icc] at hg
      have hgpos : 0 < g := by omega
      have hbound := weightedDivisorMultiplesSum_le
        (show g ∈ Finset.Icc 1 X by simpa [Finset.mem_Icc] using hg)
      have hsumNonneg : 0 ≤ weightedDivisorMultiplesSum X g := by
        unfold weightedDivisorMultiplesSum
        positivity
      have hrightNonneg : 0 ≤ ((divisorCount g : Real) / g) *
          ((1 : Real) / 2 * (Real.log X + 2) ^ 2) := by positivity
      have hsquare := pow_le_pow_left₀ hsumNonneg hbound 2
      have hlogPow : (Real.log X + 2) ^ 4 ≤
          (Real.log X + 3) ^ 4 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 4
      calc
        (g : Real) * (weightedDivisorMultiplesSum X g) ^ 2 ≤
            (g : Real) *
              (((divisorCount g : Real) / g) *
                ((1 : Real) / 2 * (Real.log X + 2) ^ 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare (by positivity)
        _ = (1 / 4 : Real) * (Real.log X + 2) ^ 4 *
            ((divisorCount g : Real) ^ 2 / g) := by
          field_simp
          ring
        _ ≤ (1 / 4 : Real) * (Real.log X + 3) ^ 4 *
            ((divisorCount g : Real) ^ 2 / g) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogPow (by norm_num)) (by positivity)
    _ = ((1 / 4 : Real) * (Real.log X + 3) ^ 4) *
        ∑ g ∈ Finset.Icc 1 X,
          (divisorCount g : Real) ^ 2 / g := by
      rw [Finset.mul_sum]
    _ ≤ ((1 / 4 : Real) * (Real.log X + 3) ^ 4) *
        ((1 / 12 : Real) * (Real.log X + 3) ^ 4) := by
      exact mul_le_mul_of_nonneg_left (chen_eight_weighted_second_moment X)
        (by positivity)
    _ = (1 : Real) / 48 * (Real.log X + 3) ^ 8 := by ring

end

end Waring.Analytic
