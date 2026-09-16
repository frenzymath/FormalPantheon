import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Field

/-!
# Log-ratio comparison for truncated Perron errors

The strict near-diagonal range here is the one used in
`MONTGOMERY-VAUGHAN-MNT-I`, Corollary 5.3, p. 140.  The equality case is
deliberately excluded because it is represented by `perronWeight` rather than
by a totalized reciprocal logarithm.
-/

namespace PrimesRestrictedDigits

/-- Reversing a quotient between positive reals negates its logarithm and
therefore preserves the absolute value. -/
theorem abs_log_div_comm {x y : Real} (hx : 0 < x) (hy : 0 < y) :
    |Real.log (x / y)| = |Real.log (y / x)| := by
  rw [show y / x = (x / y)⁻¹ by field_simp, Real.log_inv, abs_neg]

/-- In the strict near-diagonal range, a reciprocal logarithmic distance is
controlled by the relative additive distance with explicit constant two. -/
theorem one_div_abs_log_div_le {x y : Real} (hx : 0 < x) (hy : 0 < y)
    (hlo : x / 2 < y) (hhi : y < 2 * x) (hne : x ≠ y) :
    1 / |Real.log (x / y)| <= 2 * x / |x - y| := by
  have hratio : 0 < x / y := div_pos hx hy
  by_cases hlt : x < y
  · have hlt_ratio : x / y < 1 := by
      rw [div_lt_iff₀ hy]
      linarith
    have hlogneg : Real.log (x / y) < 0 := Real.log_neg hratio hlt_ratio
    rw [abs_of_neg hlogneg]
    have hinv : 1 - x / y <= Real.log (y / x) := by
      convert Real.one_sub_inv_le_log_of_pos (div_pos hy hx) using 1;
        field_simp
    have hlog_inv : Real.log (y / x) = -Real.log (x / y) := by
      rw [show y / x = (x / y)⁻¹ by field_simp]
      exact Real.log_inv _
    rw [hlog_inv] at hinv
    have hden : 0 < 1 - x / y := sub_pos.mpr hlt_ratio
    have hrecip : 1 / (-Real.log (x / y)) <= 1 / (1 - x / y) :=
      one_div_le_one_div_of_le hden hinv
    calc
      1 / -Real.log (x / y) <= 1 / (1 - x / y) := hrecip
      _ = y / (y - x) := by field_simp
      _ <= 2 * x / (y - x) := by
        apply (div_le_div_iff_of_pos_right (sub_pos.mpr hlt)).2
        linarith [hhi]
      _ = 2 * x / |x - y| := by
        rw [abs_of_neg (sub_neg.mpr hlt)]
        congr 2
        ring
  · have hle : y <= x := le_of_not_gt hlt
    have hgt : y < x := lt_of_le_of_ne hle (Ne.symm hne)
    have hgt_ratio : 1 < x / y := by
      rw [lt_div_iff₀ hy]
      linarith
    have hlogpos : 0 < Real.log (x / y) := Real.log_pos hgt_ratio
    rw [abs_of_pos hlogpos]
    have hinv := Real.one_sub_inv_le_log_of_pos (x := x / y) (div_pos hx hy)
    have hden : 0 < 1 - y / x := by
      apply sub_pos.mpr
      exact (div_lt_iff₀ hx).2 (by nlinarith)
    have hbound : 1 - y / x <= Real.log (x / y) := by
      simpa [one_div, div_eq_mul_inv] using hinv
    have hrecip : 1 / Real.log (x / y) <= 1 / (1 - y / x) :=
      one_div_le_one_div_of_le hden hbound
    calc
      1 / Real.log (x / y) <= 1 / (1 - y / x) := hrecip
      _ = x / (x - y) := by field_simp
      _ <= 2 * x / (x - y) := by
        apply (div_le_div_iff_of_pos_right (sub_pos.mpr hgt)).2
        linarith
      _ = 2 * x / |x - y| := by rw [abs_of_pos (sub_pos.mpr hgt)]

/-- Natural-index specialization of `one_div_abs_log_div_le`. -/
theorem one_div_abs_log_div_natCast_le {x : Real} {n : Nat} (hx : 0 < x)
    (hn : 0 < n) (hlo : x / 2 < (n : Real)) (hhi : (n : Real) < 2 * x)
    (hne : x ≠ (n : Real)) :
    1 / |Real.log (x / (n : Real))| <= 2 * x / |x - (n : Real)| := by
  exact one_div_abs_log_div_le hx (by exact_mod_cast hn) hlo hhi hne

/-- Source-oriented form of the log-ratio comparison, with `y / x` inside
the logarithm. -/
theorem one_div_abs_log_div_comm_le {x y : Real} (hx : 0 < x) (hy : 0 < y)
    (hlo : x / 2 < y) (hhi : y < 2 * x) (hne : x ≠ y) :
    1 / |Real.log (y / x)| <= 2 * x / |x - y| := by
  rw [← abs_log_div_comm hx hy]
  exact one_div_abs_log_div_le hx hy hlo hhi hne

/-- The log-ratio comparison after positive height scaling and truncation by
one, in the form used by the Perron error sum. -/
theorem min_one_div_mul_abs_log_div_le {x y T : Real} (hx : 0 < x)
    (hy : 0 < y) (hlo : x / 2 < y) (hhi : y < 2 * x) (hne : x ≠ y)
    (hT : 0 < T) :
    min 1 (1 / (T * |Real.log (x / y)|)) <=
      min 1 (2 * x / (T * |x - y|)) := by
  apply min_le_min_left
  have hbound := one_div_abs_log_div_le hx hy hlo hhi hne
  have hlogne : Real.log (x / y) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one (div_pos hx hy)
    intro heq
    apply hne
    simpa using (div_eq_iff (ne_of_gt hy)).mp heq
  have hdiffne : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hscaled : (1 / |Real.log (x / y)|) / T <=
      (2 * x / |x - y|) / T :=
    div_le_div_of_nonneg_right hbound hT.le
  calc
    1 / (T * |Real.log (x / y)|) =
        (1 / |Real.log (x / y)|) / T := by
      field_simp [hT.ne', hlogne]
    _ <= (2 * x / |x - y|) / T := hscaled
    _ = 2 * x / (T * |x - y|) := by
      field_simp [hT.ne', hdiffne]

end PrimesRestrictedDigits
