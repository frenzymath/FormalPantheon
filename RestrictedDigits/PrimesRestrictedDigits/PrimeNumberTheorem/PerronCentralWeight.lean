import PrimesRestrictedDigits.PrimeNumberTheorem.PerronCentralKernel
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronSincStep
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronWeight
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronLogRatio

/-!
# The central Perron kernel against the starred cutoff weight

This file packages the strict near-diagonal branch of
`MONTGOMERY-VAUGHAN-MNT-I`, Theorem 5.2 and Corollary 5.3, pp. 139--140,
for a positive natural Dirichlet-series index.
-/

open Complex MeasureTheory
open scoped Interval

namespace PrimesRestrictedDigits

/-- In the strict central range, the one-term Perron error is controlled by
the truncated reciprocal logarithm and the explicit contour error. -/
theorem norm_perronKernel_div_natCast_sub_perronWeight_le_log
    {x sigma T : Real} {n : Nat} (hx : 0 < x) (hn : 0 < n)
    (hlo : x / 2 < (n : Real)) (hhi : (n : Real) < 2 * x)
    (hne : x ≠ (n : Real)) (hsigma : 0 < sigma) (hsigma2 : sigma <= 2)
    (hT : 0 < T) :
    ‖perronKernel (x / (n : Real)) sigma T - (perronWeight x n : Complex)‖ <=
      min 1 (1 / (T * |Real.log (x / (n : Real))|)) +
        12 / (Real.pi * T) := by
  have hn' : (0 : Real) < n := by exact_mod_cast hn
  let y : Real := x / (n : Real)
  have hy : 0 < y := div_pos hx hn'
  have hylo : (1 / 2 : Real) <= y := by
    dsimp [y]
    rw [le_div_iff₀ hn']
    nlinarith [hhi]
  have hyhi : y <= 2 := by
    dsimp [y]
    rw [div_le_iff₀ hn']
    nlinarith [hlo]
  have hyne : y ≠ 1 := by
    intro hyone
    apply hne
    have := (div_eq_iff hn'.ne').mp hyone
    simpa using this
  have hlogne : Real.log y ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hy hyne
  have hAne : T * Real.log y ≠ 0 := mul_ne_zero hT.ne' hlogne
  let S : Real := ∫ u in (0 : Real)..(T * Real.log y), Real.sinc u
  let approx : Complex := (((1 / 2 + S / Real.pi : Real)) : Complex)
  let weight : Complex := (perronWeight x n : Complex)
  have hcentral : ‖perronKernel y sigma T - approx‖ <=
      12 / (Real.pi * T) := by
    dsimp [approx, S]
    exact norm_perronKernel_sub_half_add_sinc_le
      hylo hyhi hsigma hsigma2 hT
  have hstep : (if 0 < T * Real.log y then (1 : Real) else 0) =
      perronWeight x n := by
    by_cases hnx : (n : Real) < x
    · have hyone : 1 < y := by
        dsimp [y]
        rw [lt_div_iff₀ hn']
        simpa using hnx
      have hApos : 0 < T * Real.log y := mul_pos hT (Real.log_pos hyone)
      rw [if_pos hApos, perronWeight_eq_one_of_lt hnx]
    · have hxn : x < (n : Real) :=
        lt_of_le_of_ne (le_of_not_gt hnx) hne
      have hyone : y < 1 := by
        dsimp [y]
        exact (div_lt_one hn').2 hxn
      have hAneg : T * Real.log y < 0 :=
        mul_neg_of_pos_of_neg hT (Real.log_neg hy hyone)
      rw [if_neg (not_lt_of_ge hAneg.le), perronWeight_eq_zero_of_lt hxn]
  have hsinc := abs_half_add_sincIntegral_sub_step_le hAne
  change abs (1 / 2 + S / Real.pi -
      (if 0 < T * Real.log y then 1 else 0)) <=
    min 1 (1 / abs (T * Real.log y)) at hsinc
  rw [hstep, abs_mul, abs_of_pos hT] at hsinc
  have happrox : ‖approx - weight‖ <=
      min 1 (1 / (T * |Real.log y|)) := by
    dsimp [approx, weight]
    rw [show (((1 / 2 + S / Real.pi : Real)) : Complex) -
        (perronWeight x n : Complex) =
        ((1 / 2 + S / Real.pi - perronWeight x n : Real) : Complex) by
      push_cast
      ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hsinc
  change ‖perronKernel y sigma T - weight‖ <= _
  calc
    ‖perronKernel y sigma T - weight‖ =
        ‖(perronKernel y sigma T - approx) + (approx - weight)‖ := by
      congr 1
      ring
    _ <= ‖perronKernel y sigma T - approx‖ + ‖approx - weight‖ :=
      norm_add_le _ _
    _ <= 12 / (Real.pi * T) +
        min 1 (1 / (T * |Real.log y|)) := add_le_add hcentral happrox
    _ = min 1 (1 / (T * |Real.log y|)) +
        12 / (Real.pi * T) := add_comm _ _

/-- Corollary 5.3 form of the central one-term error, with the logarithmic
distance replaced by the additive distance from the cutoff. -/
theorem norm_perronKernel_div_natCast_sub_perronWeight_le
    {x sigma T : Real} {n : Nat} (hx : 0 < x) (hn : 0 < n)
    (hlo : x / 2 < (n : Real)) (hhi : (n : Real) < 2 * x)
    (hne : x ≠ (n : Real)) (hsigma : 0 < sigma) (hsigma2 : sigma <= 2)
    (hT : 0 < T) :
    ‖perronKernel (x / (n : Real)) sigma T - (perronWeight x n : Complex)‖ <=
      min 1 (2 * x / (T * |x - (n : Real)|)) +
        12 / (Real.pi * T) := by
  have hkernel := norm_perronKernel_div_natCast_sub_perronWeight_le_log
    hx hn hlo hhi hne hsigma hsigma2 hT
  have hlog := min_one_div_mul_abs_log_div_le hx (by exact_mod_cast hn)
    hlo hhi hne hT
  exact hkernel.trans (add_le_add hlog (le_refl _))

end PrimesRestrictedDigits
