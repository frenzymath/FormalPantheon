import PrimesRestrictedDigits.PrimeNumberTheorem.PerronCentralWeight
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronOuterWeight

/-!
# A uniform one-term truncated Perron bound

This file assembles the strict central, exact endpoint, and weak outer cases
of `MONTGOMERY-VAUGHAN-MNT-I`, Theorem 5.2 and Corollary 5.3, pp. 139--140.
-/

namespace PrimesRestrictedDigits

/-- The strict near-diagonal summand in the truncated Perron error. -/
noncomputable def perronNearError (x T : Real) (n : Nat) : Real :=
  if x / 2 < (n : Real) ∧ (n : Real) < 2 * x ∧ x ≠ (n : Real) then
    min 1 (x / (T * |x - (n : Real)|))
  else 0

private theorem min_one_two_mul_le_two_mul_min_one {a : Real} (_ha : 0 <= a) :
    min 1 (2 * a) <= 2 * min 1 a := by
  by_cases haone : a <= 1
  · calc
      min 1 (2 * a) <= 2 * a := min_le_right _ _
      _ = 2 * min 1 a := by rw [min_eq_right haone]
  · have honea : 1 <= a := le_of_not_ge haone
    calc
      min 1 (2 * a) <= 1 := min_le_left _ _
      _ <= 2 * min 1 a := by rw [min_eq_left honea]; norm_num

/-- Every positive natural index satisfies one explicit Perron error bound,
with absolute constants on the strict near term and ratio-power term. -/
theorem norm_perronKernel_div_natCast_sub_perronWeight_le_uniform
    {x sigma T : Real} {n : Nat} (hx : 0 < x) (hn : 0 < n)
    (hsigma : 0 < sigma) (hsigma2 : sigma <= 2) (hT : 0 < T) :
    ‖perronKernel (x / (n : Real)) sigma T - (perronWeight x n : Complex)‖ <=
      2 * perronNearError x T n +
        16 * (x / (n : Real)) ^ sigma / T := by
  have hn' : (0 : Real) < n := by exact_mod_cast hn
  have hratio : 0 < x / (n : Real) := div_pos hx hn'
  by_cases hrange : x / 2 < (n : Real) ∧ (n : Real) < 2 * x
  · by_cases hne : x ≠ (n : Real)
    · have hcentral := norm_perronKernel_div_natCast_sub_perronWeight_le
        hx hn hrange.1 hrange.2 hne hsigma hsigma2 hT
      let a : Real := x / (T * |x - (n : Real)|)
      have hdiff : x - (n : Real) ≠ 0 := sub_ne_zero.mpr hne
      have ha : 0 <= a := by
        dsimp [a]
        positivity
      have hnear :
          min 1 (2 * x / (T * |x - (n : Real)|)) <= 2 * min 1 a := by
        rw [show 2 * x / (T * |x - (n : Real)|) = 2 * a by
          dsimp [a]
          ring]
        exact min_one_two_mul_le_two_mul_min_one ha
      have hylo : (1 / 2 : Real) <= x / (n : Real) := by
        rw [le_div_iff₀ hn']
        nlinarith [hrange.2]
      have hquarter : (1 / 4 : Real) <= (x / (n : Real)) ^ sigma := calc
        (1 / 4 : Real) = (1 / 2 : Real) ^ (2 : Real) := by
          rw [Real.rpow_two]
          norm_num
        _ <= (1 / 2 : Real) ^ sigma :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hsigma2
        _ <= (x / (n : Real)) ^ sigma :=
          Real.rpow_le_rpow (by norm_num) hylo hsigma.le
      have hthreeT : 3 * T <= Real.pi * T :=
        mul_le_mul_of_nonneg_right Real.pi_gt_three.le hT.le
      have hpi : 12 / (Real.pi * T) <= 4 / T := calc
        12 / (Real.pi * T) <= 12 / (3 * T) :=
          div_le_div_of_nonneg_left (by norm_num) (mul_pos (by norm_num) hT) hthreeT
        _ = 4 / T := by field_simp [hT.ne']; norm_num
      have hpower : 4 / T <= 16 * (x / (n : Real)) ^ sigma / T := by
        apply (div_le_div_iff_of_pos_right hT).2
        nlinarith
      rw [perronNearError, if_pos ⟨hrange.1, hrange.2, hne⟩]
      exact hcentral.trans <| add_le_add hnear (hpi.trans hpower)
    · have hxn : x = (n : Real) := not_ne_iff.mp hne
      have hnx : (n : Real) = x := hxn.symm
      have hendpoint := norm_perronKernel_div_natCast_sub_perronWeight_eq_le
        hn hnx hsigma hT
      have hratioone : x / (n : Real) = 1 := by
        rw [hxn]
        exact div_self hn'.ne'
      have hden : T <= Real.pi * T := calc
        T = 1 * T := by ring
        _ <= Real.pi * T :=
          mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) hT.le
      have hcoarse : sigma / (Real.pi * T) <=
          16 * (x / (n : Real)) ^ sigma / T := by
        rw [hratioone, Real.one_rpow]
        calc
          sigma / (Real.pi * T) <= sigma / T :=
            div_le_div_of_nonneg_left hsigma.le hT hden
          _ <= 16 / T := div_le_div_of_nonneg_right (by linarith) hT.le
          _ = 16 * 1 / T := by ring
      rw [perronNearError, if_neg (by
        intro h
        exact hne h.2.2)]
      simpa using hendpoint.trans hcoarse
  · have houter : (n : Real) <= x / 2 ∨ 2 * x <= (n : Real) := by
      by_cases hlo : x / 2 < (n : Real)
      · right
        exact le_of_not_gt fun hhi => hrange ⟨hlo, hhi⟩
      · left
        exact le_of_not_gt hlo
    have hout := norm_perronKernel_div_natCast_sub_perronWeight_outer_le
      hx hn houter hsigma hT
    have hnearzero : perronNearError x T n = 0 := by
      rw [perronNearError, if_neg]
      intro h
      exact hrange ⟨h.1, h.2.1⟩
    rw [hnearzero, mul_zero, zero_add]
    have hnonneg : 0 <= (x / (n : Real)) ^ sigma / T := by positivity
    exact hout.trans <| calc
      (x / (n : Real)) ^ sigma / T <=
          16 * ((x / (n : Real)) ^ sigma / T) := by nlinarith
      _ = 16 * (x / (n : Real)) ^ sigma / T := by ring

end PrimesRestrictedDigits
