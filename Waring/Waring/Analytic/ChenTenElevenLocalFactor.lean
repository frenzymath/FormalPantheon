import Waring.Analytic.ChenThreeEleven
import Waring.Analytic.ChenTenGenericLocalFactor
import Waring.Analytic.NonfivePrimePower

/-!
# The eleven-adic local factor in Chen's Lemma 10

The checked modulus-eleven table and the exact initial prime-power values give
an explicit half-unit neighbourhood of one for the local factor at `11`
[CHEN1964-EN, pp. 1565-1566, equations (37)-(38); CHEN1964-ZH, pp. 731-732].
-/

namespace Waring.Analytic

open scoped BigOperators

private lemma norm_chenTenSingularTerm_le_of_norm_completePowerSum_le
    {q : Nat} [NeZero q] (N : Nat) (a : ZMod q) (B : Real)
    (hB : ‖completePowerSum 5 a‖ <= B) :
    ‖chenTenSingularTerm q N a‖ <= (B / q) ^ 15 := by
  have hq : (0 : Real) <= q := by positivity
  unfold chenTenSingularTerm
  simp only [norm_mul, norm_pow, norm_div, Complex.norm_natCast,
    norm_stdAddChar, mul_one]
  exact pow_le_pow_left₀ (by positivity)
    (div_le_div_of_nonneg_right hB hq) 15

/-- The exponent-one singular coefficient at eleven satisfies the explicit
bound obtained from the three rows of Chen's finite residue table. -/
theorem norm_chenTenSingularCoefficient_eleven_le (N : Nat) :
    ‖chenTenSingularCoefficient 11 N‖ <=
      2 * ((237 : Real) / 275) ^ 15 +
        2 * ((87 : Real) / 110) ^ 15 +
          6 * ((28 : Real) / 55) ^ 15 := by
  have hLarge (a : Nat) (ha : a = 1 ∨ a = 10) :
      ‖if IsUnit ((a : Nat) : ZMod 11) then
          chenTenSingularTerm 11 N ((a : Nat) : ZMod 11) else 0‖ <=
        ((237 : Real) / 275) ^ 15 := by
    have hunit : IsUnit ((a : Nat) : ZMod 11) := by
      apply (ZMod.isUnit_iff_coprime a 11).2
      rcases ha with rfl | rfl <;> norm_num
    rw [if_pos hunit]
    convert norm_chenTenSingularTerm_le_of_norm_completePowerSum_le
      N ((a : Nat) : ZMod 11) ((237 : Real) / 25)
        (chen_three_eleven_large ha) using 1; norm_num
  have hMedium (a : Nat) (ha : a = 5 ∨ a = 6) :
      ‖if IsUnit ((a : Nat) : ZMod 11) then
          chenTenSingularTerm 11 N ((a : Nat) : ZMod 11) else 0‖ <=
        ((87 : Real) / 110) ^ 15 := by
    have hunit : IsUnit ((a : Nat) : ZMod 11) := by
      apply (ZMod.isUnit_iff_coprime a 11).2
      rcases ha with rfl | rfl <;> norm_num
    rw [if_pos hunit]
    convert norm_chenTenSingularTerm_le_of_norm_completePowerSum_le
      N ((a : Nat) : ZMod 11) ((87 : Real) / 10)
        (chen_three_eleven_medium ha) using 1; norm_num
  have hSmall (a : Nat)
      (ha : a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 7 ∨ a = 8 ∨ a = 9) :
      ‖if IsUnit ((a : Nat) : ZMod 11) then
          chenTenSingularTerm 11 N ((a : Nat) : ZMod 11) else 0‖ <=
        ((28 : Real) / 55) ^ 15 := by
    have hunit : IsUnit ((a : Nat) : ZMod 11) := by
      apply (ZMod.isUnit_iff_coprime a 11).2
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    rw [if_pos hunit]
    convert norm_chenTenSingularTerm_le_of_norm_completePowerSum_le
      N ((a : Nat) : ZMod 11) ((28 : Real) / 5)
        (chen_three_eleven_small ha) using 1; norm_num
  let B : Fin 11 -> Real := fun i =>
    match i.val with
    | 0 => 0
    | 1 => ((237 : Real) / 275) ^ 15
    | 2 => ((28 : Real) / 55) ^ 15
    | 3 => ((28 : Real) / 55) ^ 15
    | 4 => ((28 : Real) / 55) ^ 15
    | 5 => ((87 : Real) / 110) ^ 15
    | 6 => ((87 : Real) / 110) ^ 15
    | 7 => ((28 : Real) / 55) ^ 15
    | 8 => ((28 : Real) / 55) ^ 15
    | 9 => ((28 : Real) / 55) ^ 15
    | _ => ((237 : Real) / 275) ^ 15
  have hEach (i : Fin 11) :
      ‖if IsUnit ((i.val : Nat) : ZMod 11) then
          chenTenSingularTerm 11 N ((i.val : Nat) : ZMod 11) else 0‖ <=
        B i := by
    fin_cases i
    · have hzero : ¬ IsUnit ((0 : Nat) : ZMod 11) := by
        intro h
        have := (ZMod.isUnit_iff_coprime 0 11).1 h
        norm_num at this
      change ‖if IsUnit ((0 : Nat) : ZMod 11) then
        chenTenSingularTerm 11 N 0 else 0‖ <= 0
      rw [if_neg hzero]
      simp
    · simpa [B] using hLarge 1 (by simp)
    · simpa [B] using hSmall 2 (by simp)
    · simpa [B] using hSmall 3 (by simp)
    · simpa [B] using hSmall 4 (by simp)
    · simpa [B] using hMedium 5 (by simp)
    · simpa [B] using hMedium 6 (by simp)
    · simpa [B] using hSmall 7 (by simp)
    · simpa [B] using hSmall 8 (by simp)
    · simpa [B] using hSmall 9 (by simp)
    · simpa [B] using hLarge 10 (by simp)
  unfold chenTenSingularCoefficient
  calc
    ‖∑ a : ZMod 11,
        if IsUnit a then chenTenSingularTerm 11 N a else 0‖ <=
        ∑ a : ZMod 11,
          ‖if IsUnit a then chenTenSingularTerm 11 N a else 0‖ :=
      norm_sum_le _ _
    _ = ∑ i : Fin 11,
        ‖if IsUnit ((i.val : Nat) : ZMod 11) then
          chenTenSingularTerm 11 N ((i.val : Nat) : ZMod 11) else 0‖ := by
      rw [← (ZMod.finEquiv 11).toEquiv.sum_comp]
      rfl
    _ <= 2 * ((237 : Real) / 275) ^ 15 +
        2 * ((87 : Real) / 110) ^ 15 +
          6 * ((28 : Real) / 55) ^ 15 := by
      calc
        ∑ i : Fin 11,
            ‖if IsUnit ((i.val : Nat) : ZMod 11) then
              chenTenSingularTerm 11 N ((i.val : Nat) : ZMod 11) else 0‖ <=
            ∑ i : Fin 11, B i := by
          exact Finset.sum_le_sum fun i _ => hEach i
        _ = 2 * ((237 : Real) / 275) ^ 15 +
            2 * ((87 : Real) / 110) ^ 15 +
              6 * ((28 : Real) / 55) ^ 15 := by
          simp [B, Fin.sum_univ_succ]
          ring

/-- A convenient coarse form of the checked exponent-one estimate. -/
theorem norm_chenTenSingularCoefficient_eleven_le_coarse (N : Nat) :
    ‖chenTenSingularCoefficient 11 N‖ <=
      (1 : Real) / 3 + 1 / 9 + 1 / 1000 := by
  calc
    ‖chenTenSingularCoefficient 11 N‖ <=
        2 * ((237 : Real) / 275) ^ 15 +
          2 * ((87 : Real) / 110) ^ 15 +
            6 * ((28 : Real) / 55) ^ 15 :=
      norm_chenTenSingularCoefficient_eleven_le N
    _ <= (1 : Real) / 3 + 1 / 9 + 1 / 1000 := by norm_num

/-- Chen's local complete-sum constant at eleven is at most two. -/
theorem chenTwoPrimeFactor_eleven_le_two :
    chenTwoPrimeFactor 11 <= 2 := by
  have hroot : (2 : Real) <= (11 : Real) ^ (3 / 10 : Real) := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (10 : Nat) ≠ 0)
      (Real.rpow_nonneg (by norm_num : (0 : Real) <= 11) _)
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) <= 11)]
    norm_num [Real.rpow_natCast]
  have hrootPos : 0 < (11 : Real) ^ (3 / 10 : Real) :=
    Real.rpow_pos_of_pos (by norm_num) _
  rw [chenTwoPrimeFactor]
  norm_num only [reduceCtorEq, ↓reduceIte, Nat.reduceSub, Nat.reduceDvd,
    Nat.reduceLeDiff]
  simp only [if_false, true_and, if_true]
  rw [Real.rpow_neg (by norm_num : (0 : Real) <= 11)]
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ hrootPos).2
  nlinarith [hroot]

/-- At exponents two through five, exact stationary phase gives the sharp
complete-sum input for the eleven-adic singular coefficient. -/
theorem norm_chenTenSingularCoefficient_eleven_pow_small_le
    {alpha : Nat} (hLower : 1 < alpha) (hUpper : alpha <= 5) (N : Nat) :
    ‖chenTenSingularCoefficient (11 ^ alpha) N‖ <=
      ((11 ^ alpha : Nat) : Real) *
        ((((11 ^ (alpha - 1) : Nat) : Real) /
          (11 ^ alpha : Nat)) ^ 15) := by
  letI : NeZero (11 ^ alpha) := ⟨pow_ne_zero alpha (by norm_num)⟩
  apply norm_chenTenSingularCoefficient_le
  · positivity
  · intro a ha
    obtain ⟨b, rfl⟩ := ZMod.natCast_zmod_surjective a
    have hbPow : b.Coprime (11 ^ alpha) :=
      (ZMod.isUnit_iff_coprime b (11 ^ alpha)).1 ha
    have hb : b.Coprime 11 :=
      (Nat.coprime_pow_right_iff (by omega) b 11).1 hbPow
    rw [completePowerSum_fifth_primePow_small Nat.prime_eleven (by norm_num)
      hLower hUpper b hb]
    simp

end Waring.Analytic
