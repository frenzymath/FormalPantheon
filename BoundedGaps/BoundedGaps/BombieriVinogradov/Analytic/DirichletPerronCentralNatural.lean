import BoundedGaps.BombieriVinogradov.Analytic.DirichletPerronCentral

/-!
# The central Perron kernel at natural indices

This file turns the oriented sinc primitive in the central scalar theorem into
the exact strict/half/zero weight at a natural cutoff. The endpoint itself is
excluded here and remains owned by `DirichletPerronKernel`.

Semantic review: `SEM-533`.
-/

namespace BoundedGaps.Maynard

open Complex MeasureTheory
open scoped Interval

noncomputable section

private lemma abs_half_add_sincIntegral_sub_step_le
    {A : ℝ} (hA : A ≠ 0) :
    |1 / 2 +
        (∫ u in (0 : ℝ)..A, Real.sinc u) / Real.pi -
          (if 0 < A then 1 else 0)| ≤
      min 1 (1 / |A|) := by
  let S : ℝ := ∫ u in (0 : ℝ)..A, Real.sinc u
  have hAabs : 0 < |A| := abs_pos.mpr hA
  by_cases hlarge : 1 ≤ |A|
  · rw [min_eq_right ((div_le_one hAabs).2 hlarge)]
    have htail :=
      abs_integral_sinc_sub_sign_pi_div_two_le_inv_abs hA
    by_cases hApos : 0 < A
    · rw [if_pos hApos, Real.sign_of_pos hApos] at *
      have htailS : |S - Real.pi / 2| ≤ |A| ^ (-1 : ℤ) := by
        simpa [S] using htail
      calc
        |1 / 2 + S / Real.pi - 1| =
            |S - Real.pi / 2| / Real.pi := by
          rw [show 1 / 2 + S / Real.pi - 1 =
              (S - Real.pi / 2) / Real.pi by
            field_simp [Real.pi_ne_zero]
            ring,
            abs_div, abs_of_pos Real.pi_pos]
        _ ≤ (|A| ^ (-1 : ℤ)) / Real.pi :=
          div_le_div_of_nonneg_right htailS Real.pi_pos.le
        _ ≤ 1 / |A| := by
          rw [zpow_neg_one]
          have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
          have hinv : 0 ≤ |A|⁻¹ := inv_nonneg.mpr hAabs.le
          rw [one_div]
          exact (div_le_iff₀ Real.pi_pos).2
            (by simpa using mul_le_mul_of_nonneg_left hpi hinv)
    · have hAneg : A < 0 := lt_of_le_of_ne (le_of_not_gt hApos) hA
      rw [if_neg hApos, Real.sign_of_neg hAneg] at *
      have htailS : |S + Real.pi / 2| ≤ |A| ^ (-1 : ℤ) := by
        simpa [S] using htail
      calc
        |1 / 2 + S / Real.pi - 0| =
            |S + Real.pi / 2| / Real.pi := by
          rw [show 1 / 2 + S / Real.pi - 0 =
              (S + Real.pi / 2) / Real.pi by
            field_simp [Real.pi_ne_zero]
            ring,
            abs_div, abs_of_pos Real.pi_pos]
        _ ≤ (|A| ^ (-1 : ℤ)) / Real.pi :=
          div_le_div_of_nonneg_right htailS Real.pi_pos.le
        _ ≤ 1 / |A| := by
          rw [zpow_neg_one]
          have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
          have hinv : 0 ≤ |A|⁻¹ := inv_nonneg.mpr hAabs.le
          rw [one_div]
          exact (div_le_iff₀ Real.pi_pos).2
            (by simpa using mul_le_mul_of_nonneg_left hpi hinv)
  · have hsmall : |A| ≤ 1 := le_of_not_ge hlarge
    rw [min_eq_left]
    · have hS : |S| ≤ |A| := by
        have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : ℝ)) (b := A) (C := (1 : ℝ)) (f := Real.sinc)
          (fun u _ => by
            simpa [Real.norm_eq_abs] using Real.abs_sinc_le_one u)
        simpa [S, Real.norm_eq_abs] using hbound
      have hInvPi : 1 / Real.pi ≤ 1 / 2 := by
        rw [div_le_iff₀ Real.pi_pos]
        linarith [Real.pi_gt_three]
      have hStep :
          |(1 / 2 : ℝ) - (if 0 < A then 1 else 0)| = 1 / 2 := by
        split_ifs <;> norm_num
      calc
        |1 / 2 + S / Real.pi - (if 0 < A then 1 else 0)| =
            |((1 / 2 : ℝ) - (if 0 < A then 1 else 0)) +
              S / Real.pi| := by congr 1; ring
        _ ≤ |(1 / 2 : ℝ) - (if 0 < A then 1 else 0)| +
            |S / Real.pi| := abs_add_le _ _
        _ = 1 / 2 + |S| / Real.pi := by
          rw [hStep, abs_div, abs_of_pos Real.pi_pos]
        _ ≤ 1 / 2 + 1 / Real.pi := by
          gcongr
          exact hS.trans hsmall
        _ ≤ 1 := by linarith
    · exact (one_le_div hAabs).2 hsmall

private lemma one_div_abs_log_div_le
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hyUpper : y < 2 * x) (hne : x ≠ y) :
    1 / |Real.log (x / y)| ≤ 2 * x / |x - y| := by
  by_cases hxy : x < y
  · have hratio : 0 < y / x := div_pos hy hx
    have hratioInv : (y / x)⁻¹ = x / y := by field_simp
    have hlower := Real.one_sub_inv_le_log_of_pos hratio
    rw [hratioInv] at hlower
    have hrewrite : 1 - x / y = (y - x) / y := by field_simp
    rw [hrewrite] at hlower
    have hlogInv : Real.log (y / x) = -Real.log (x / y) := by
      rw [show y / x = (x / y)⁻¹ by field_simp, Real.log_inv]
    rw [hlogInv] at hlower
    have hlogNeg : Real.log (x / y) < 0 :=
      Real.log_neg (div_pos hx hy) ((div_lt_one hy).2 hxy)
    have hdiff : 0 < y - x := sub_pos.mpr hxy
    rw [abs_of_neg hlogNeg, abs_of_neg (sub_neg.mpr hxy)]
    have hrecip :
        1 / (-Real.log (x / y)) ≤ y / (y - x) := by
      have hbase : 0 < (y - x) / y := div_pos hdiff hy
      calc
        1 / (-Real.log (x / y)) ≤ 1 / ((y - x) / y) :=
          one_div_le_one_div_of_le hbase hlower
        _ = y / (y - x) := by field_simp
    calc
      1 / -Real.log (x / y) ≤ y / (y - x) := hrecip
      _ ≤ 2 * x / (y - x) := by
        exact div_le_div_of_nonneg_right hyUpper.le hdiff.le
      _ = 2 * x / -(x - y) := by congr 1; ring
  · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy) hne.symm
    have hratio : 0 < x / y := div_pos hx hy
    have hlower := Real.one_sub_inv_le_log_of_pos hratio
    have hrewrite : 1 - (x / y)⁻¹ = (x - y) / x := by field_simp
    rw [hrewrite] at hlower
    have hlogPos : 0 < Real.log (x / y) :=
      Real.log_pos ((one_lt_div hy).2 hyx)
    have hdiff : 0 < x - y := sub_pos.mpr hyx
    rw [abs_of_pos hlogPos, abs_of_pos hdiff]
    calc
      1 / Real.log (x / y) ≤ 1 / ((x - y) / x) :=
        one_div_le_one_div_of_le (div_pos hdiff hx) hlower
      _ = x / (x - y) := by field_simp
      _ ≤ 2 * x / (x - y) := by
        exact div_le_div_of_nonneg_right (by linarith) hdiff.le

private lemma min_log_error_le_distance_error
    {x y U : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hyUpper : y < 2 * x) (hne : x ≠ y) (hU : 0 < U) :
    min 1 (1 / (U * |Real.log (x / y)|)) ≤
      min 1 (2 * x / (U * |x - y|)) := by
  apply min_le_min_left
  have hbase := one_div_abs_log_div_le hx hy hyUpper hne
  have hlog : Real.log (x / y) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (div_pos hx hy) (by
      intro hratio
      apply hne
      exact (div_eq_one_iff_eq hy.ne').mp hratio)
  have hdiff : x - y ≠ 0 := sub_ne_zero.mpr hne
  calc
    1 / (U * |Real.log (x / y)|) =
        (1 / |Real.log (x / y)|) / U := by
      field_simp [hU.ne', hlog]
    _ ≤ (2 * x / |x - y|) / U :=
      div_le_div_of_nonneg_right hbase hU.le
    _ = 2 * x / (U * |x - y|) := by
      field_simp [hU.ne', hdiff]

/-- In the strict central range, the scalar kernel differs from its natural
starred weight by the reciprocal distance term and the central contour error.
-/
theorem norm_dirichletPerronKernel_sub_naturalWeight_central_le
    {x n : ℕ} {alpha U : ℝ}
    (hx : 0 < x) (hn : 0 < n)
    (hLower : (x : ℝ) / 2 < (n : ℝ))
    (hUpper : (n : ℝ) < 2 * x) (hne : n ≠ x)
    (halpha : 0 < alpha) (halphaUpper : alpha ≤ 2)
    (hU : 0 < U) :
    ‖dirichletPerronKernel ((x : ℝ) / n) alpha U -
      (dirichletPerronNaturalWeight x n : ℂ)‖ ≤
      min 1 (2 * (x : ℝ) /
        (U * |(x : ℝ) - n|)) + 20 / (Real.pi * U) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let y : ℝ := (x : ℝ) / n
  have hy : 0 < y := div_pos hxR hnR
  have hyLower : (1 / 2 : ℝ) ≤ y := by
    dsimp [y]
    rw [le_div_iff₀ hnR]
    nlinarith
  have hyUpper : y ≤ 2 := by
    dsimp [y]
    rw [div_le_iff₀ hnR]
    nlinarith
  have hxy : (x : ℝ) ≠ (n : ℝ) := by exact_mod_cast hne.symm
  have hyOne : y ≠ 1 := by
    intro hyOne
    apply hxy
    exact (div_eq_one_iff_eq hnR.ne').mp hyOne
  have hlog : Real.log y ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hy hyOne
  have hA : U * Real.log y ≠ 0 := mul_ne_zero hU.ne' hlog
  let S : ℝ := ∫ u in (0 : ℝ)..(U * Real.log y), Real.sinc u
  let approx : ℂ := ((1 / 2 + S / Real.pi : ℝ) : ℂ)
  have hcentral :
      ‖dirichletPerronKernel y alpha U - approx‖ ≤
        20 / (Real.pi * U) := by
    exact norm_dirichletPerronKernel_sub_half_add_sinc_le
      hyLower hyUpper halpha halphaUpper hU
  have hstepRaw := abs_half_add_sincIntegral_sub_step_le hA
  change |1 / 2 + S / Real.pi -
      (if 0 < U * Real.log y then 1 else 0)| ≤
    min 1 (1 / |U * Real.log y|) at hstepRaw
  have hweight :
      (if 0 < U * Real.log y then (1 : ℝ) else 0) =
        dirichletPerronNaturalWeight x n := by
    rcases lt_or_gt_of_ne hne with hnx | hxn
    · have hyOneLt : 1 < y := by
        dsimp [y]
        rw [lt_div_iff₀ hnR]
        have hnxR : (n : ℝ) < x := by exact_mod_cast hnx
        simpa using hnxR
      have hApos : 0 < U * Real.log y :=
        mul_pos hU (Real.log_pos hyOneLt)
      rw [if_pos hApos,
        dirichletPerronNaturalWeight_of_pos_of_lt hn hnx]
    · have hyLtOne : y < 1 := by
        dsimp [y]
        exact (div_lt_one hnR).2 (by exact_mod_cast hxn)
      have hAneg : U * Real.log y < 0 :=
        mul_neg_of_pos_of_neg hU (Real.log_neg hy hyLtOne)
      rw [if_neg hAneg.not_gt,
        dirichletPerronNaturalWeight_of_lt hxn]
  have hstep :
      ‖approx - (dirichletPerronNaturalWeight x n : ℂ)‖ ≤
        min 1 (1 / (U * |Real.log y|)) := by
    rw [hweight, abs_mul, abs_of_pos hU] at hstepRaw
    dsimp [approx]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hstepRaw
  have hdistance :
      min 1 (1 / (U * |Real.log y|)) ≤
        min 1 (2 * (x : ℝ) / (U * |(x : ℝ) - n|)) := by
    dsimp [y]
    exact min_log_error_le_distance_error hxR hnR hUpper hxy hU
  change ‖dirichletPerronKernel y alpha U -
    (dirichletPerronNaturalWeight x n : ℂ)‖ ≤ _
  calc
    ‖dirichletPerronKernel y alpha U -
        (dirichletPerronNaturalWeight x n : ℂ)‖ =
        ‖(dirichletPerronKernel y alpha U - approx) +
          (approx - (dirichletPerronNaturalWeight x n : ℂ))‖ := by
      congr 1
      ring
    _ ≤ ‖dirichletPerronKernel y alpha U - approx‖ +
        ‖approx - (dirichletPerronNaturalWeight x n : ℂ)‖ :=
      norm_add_le _ _
    _ ≤ 20 / (Real.pi * U) +
        min 1 (1 / (U * |Real.log y|)) := add_le_add hcentral hstep
    _ ≤ 20 / (Real.pi * U) +
        min 1 (2 * (x : ℝ) / (U * |(x : ℝ) - n|)) :=
      add_le_add_right hdistance _
    _ = min 1 (2 * (x : ℝ) / (U * |(x : ℝ) - n|)) +
        20 / (Real.pi * U) := add_comm _ _

end

end BoundedGaps.Maynard
