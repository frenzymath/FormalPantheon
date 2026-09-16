import PrimesRestrictedDigits.PrimeNumberTheorem.PerronPole
/-! # PerronHorizontal -/

open Complex MeasureTheory Set

namespace PrimesRestrictedDigits

/-- A coarse uniform bound for the regularized numerator on a horizontal edge. -/
theorem norm_perronRegularizedCpow_le_five_div
    {y r t T : Real} (hy : 0 < y) (hyhi : y <= 2) (hr : 0 <= r)
    (hr2 : r <= 2) (hT : 0 < T) (ht : T <= abs t) :
    ‖perronRegularizedCpow y (r + t * Complex.I)‖ <= 5 / T := by
  have hs : (r : Complex) + (t : Complex) * Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    have ht0 : t = 0 := by linarith
    subst t
    exact (not_le_of_gt hT) (by simpa using ht)
  have hden : T <= ‖(r : Complex) + (t : Complex) * Complex.I‖ := by
    calc
      T <= abs t := ht
      _ = ‖(t : Complex)‖ := by simp [Real.norm_eq_abs]
      _ = |Complex.im ((r : Complex) + (t : Complex) * Complex.I)| := by simp
      _ <= ‖(r : Complex) + (t : Complex) * Complex.I‖ :=
        Complex.abs_im_le_norm _
  have hpow : ‖(y : Complex) ^ ((r : Complex) + (t : Complex) * Complex.I)‖ <= 4 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp
    have hb : y ^ r <= (2 : Real) ^ r := Real.rpow_le_rpow hy.le hyhi hr
    have he : (2 : Real) ^ r <= 4 := by
      calc
        (2 : Real) ^ r <= 2 ^ (2 : Real) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two hr2
        _ = 4 := by norm_num
    exact hb.trans he
  have hR : perronRegularizedCpow y (r + t * Complex.I) =
      (y : Complex) ^ ((r : Complex) + (t : Complex) * Complex.I) /
          ((r : Complex) + (t : Complex) * Complex.I) -
        1 / ((r : Complex) + (t : Complex) * Complex.I) := by
    have h := perronCpow_div_eq_regularized_add_inv hy hs
    calc
      perronRegularizedCpow y ((r : Complex) + (t : Complex) * Complex.I) =
          (perronRegularizedCpow y ((r : Complex) + (t : Complex) * Complex.I) +
            1 / ((r : Complex) + (t : Complex) * Complex.I)) -
            1 / ((r : Complex) + (t : Complex) * Complex.I) := by ring
      _ = _ := by rw [← h]
  rw [hR]
  calc
    ‖(y : Complex) ^ ((r : Complex) + (t : Complex) * Complex.I) /
          ((r : Complex) + (t : Complex) * Complex.I) -
        1 / ((r : Complex) + (t : Complex) * Complex.I)‖ <=
        ‖(y : Complex) ^ ((r : Complex) + (t : Complex) * Complex.I) /
          ((r : Complex) + (t : Complex) * Complex.I)‖ +
          ‖1 / ((r : Complex) + (t : Complex) * Complex.I)‖ := norm_sub_le _ _
    _ = ‖(y : Complex) ^ ((r : Complex) + (t : Complex) * Complex.I)‖ /
          ‖(r : Complex) + (t : Complex) * Complex.I‖ +
          1 / ‖(r : Complex) + (t : Complex) * Complex.I‖ := by
      rw [norm_div, norm_div]
      norm_num
    _ <= 4 / T + 1 / T := by
      have hden0 : 0 < ‖(r : Complex) + (t : Complex) * Complex.I‖ :=
        lt_of_lt_of_le hT hden
      have h1a : ‖(y : Complex) ^ ((r : Complex) + (t : Complex) * Complex.I)‖ /
          ‖(r : Complex) + (t : Complex) * Complex.I‖ <=
          4 / ‖(r : Complex) + (t : Complex) * Complex.I‖ := by
        exact div_le_div_of_nonneg_right hpow hden0.le
      have h1b : (4 : Real) / ‖(r : Complex) + (t : Complex) * Complex.I‖ <= 4 / T :=
        div_le_div_of_nonneg_left (by norm_num) hT hden
      have h2 : 1 / ‖(r : Complex) + (t : Complex) * Complex.I‖ <= 1 / T := by
        exact one_div_le_one_div_of_le hT hden
      exact add_le_add (h1a.trans h1b) h2
    _ = 5 / T := by ring

end PrimesRestrictedDigits
