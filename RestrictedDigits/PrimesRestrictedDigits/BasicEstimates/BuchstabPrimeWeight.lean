import PrimesRestrictedDigits.BasicEstimates.BuchstabDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The transformed Buchstab prime weight

This file differentiates and bounds the weight in Eq. (7.45) of
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 7, p. 218. The derivative excludes the
genuine seam where the Buchstab argument equals two.
-/

namespace PrimesRestrictedDigits

/-- The translated Buchstab argument in the prime-sum induction. -/
noncomputable def buchstabArgument (x t : Real) : Real :=
  Real.log x / Real.log t - 1

/-- The weight applied to the prime-counting measure in Eq. (7.45). -/
noncomputable def buchstabPrimeWeight (x t : Real) : Real :=
  x * buchstabFunction (buchstabArgument x t) / (t * Real.log t)

private noncomputable def buchstabWeightSlope (x t slope : Real) : Real :=
  ((x * (slope * (-Real.log x / (t * Real.log t ^ 2)))) *
      (t * Real.log t) -
    (x * buchstabFunction (buchstabArgument x t)) * (Real.log t + 1)) /
    (t * Real.log t) ^ 2

/-- The derivative of the inverse initial branch, away from both endpoints. -/
theorem hasDerivAt_buchstabFunction_of_one_lt_of_lt_two
    {u : Real} (h1 : 1 < u) (h2 : u < 2) :
    HasDerivAt buchstabFunction (-(u ^ 2)⁻¹) u := by
  have heq : buchstabFunction =ᶠ[nhds u] fun t : Real => t⁻¹ := by
    filter_upwards [Ioo_mem_nhds h1 h2] with t ht
    exact buchstabFunction_eq_inv ht.1.le ht.2.le
  exact (hasDerivAt_inv (by linarith : u ≠ 0)).congr_of_eventuallyEq heq

theorem hasDerivAt_buchstabArgument {x t : Real} (ht : 1 < t) :
    HasDerivAt (buchstabArgument x)
      (-Real.log x / (t * Real.log t ^ 2)) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog0 : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one
    (by linarith) (by linarith)
  have hquot :=
    (hasDerivAt_const t (Real.log x)).fun_div
      (Real.hasDerivAt_log ht0) hlog0
  have hsub := hquot.sub_const 1
  have hcoeff :
      (0 * Real.log t - Real.log x * t⁻¹) / Real.log t ^ 2 =
        -Real.log x / (t * Real.log t ^ 2) := by
    field_simp
    ring
  exact hsub.congr_deriv hcoeff

private theorem hasDerivAt_buchstabWeight_aux {x t slope : Real} (ht : 1 < t)
    (homega : HasDerivAt buchstabFunction slope (buchstabArgument x t)) :
    HasDerivAt (buchstabPrimeWeight x) (buchstabWeightSlope x t slope) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog0 : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one
    (by linarith) (by linarith)
  have hnum : HasDerivAt
      (fun s : Real => x * buchstabFunction (buchstabArgument x s))
      (x * (slope * (-Real.log x / (t * Real.log t ^ 2)))) t :=
    (homega.comp t (hasDerivAt_buchstabArgument ht)).const_mul x
  have hdenRaw := (hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)
  have hden : HasDerivAt (fun s : Real => s * Real.log s)
      (Real.log t + 1) t := by
    change HasDerivAt (id * Real.log) (Real.log t + 1) t
    apply hdenRaw.congr_deriv
    simp [ht0]
  exact hnum.fun_div hden (mul_ne_zero ht0 hlog0)

/-- The exact derivative formula for the transformed prime weight. -/
theorem hasDerivAt_buchstabPrimeWeight {x t slope : Real} (ht : 1 < t)
    (homega : HasDerivAt buchstabFunction slope (buchstabArgument x t)) :
    HasDerivAt (buchstabPrimeWeight x)
      (-x * ((Real.log t + 1) * buchstabFunction (buchstabArgument x t) +
        (buchstabArgument x t + 1) * slope) /
        (t ^ 2 * Real.log t ^ 2)) t := by
  have ht0 : t ≠ 0 := by linarith
  have hlog0 : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one
    (by linarith) (by linarith)
  apply (hasDerivAt_buchstabWeight_aux ht homega).congr_deriv
  unfold buchstabWeightSlope buchstabArgument
  field_simp
  ring

private theorem exists_buchstabFunction_slope_bound {u : Real} (h1 : 1 < u)
    (h2 : u ≠ 2) :
    ∃ slope : Real, HasDerivAt buchstabFunction slope u ∧
      |slope| * (u + 1) ≤ 2 := by
  rcases lt_or_gt_of_ne h2 with hu | hu
  · refine ⟨-(u ^ 2)⁻¹,
      hasDerivAt_buchstabFunction_of_one_lt_of_lt_two h1 hu, ?_⟩
    have hu0 : 0 < u := by linarith
    have hsq : 0 < u ^ 2 := sq_pos_of_pos hu0
    have hpoly : u + 1 ≤ 2 * u ^ 2 := by
      nlinarith [sq_nonneg (u - 1)]
    rw [abs_neg, abs_inv, abs_of_pos hsq]
    rw [inv_mul_eq_div, div_le_iff₀ hsq]
    exact hpoly
  · refine ⟨(buchstabFunction (u - 1) - buchstabFunction u) / u,
      hasDerivAt_buchstabFunction hu, ?_⟩
    have hu0 : 0 < u := by linarith
    have hslope := abs_deriv_buchstabFunction_le hu
    rw [deriv_buchstabFunction hu] at hslope
    calc
      |(buchstabFunction (u - 1) - buchstabFunction u) / u| * (u + 1) ≤
          (1 / (2 * u)) * (u + 1) := by
        gcongr
      _ ≤ 1 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 2 * u)]
        nlinarith
      _ ≤ 2 := by norm_num

/-- Buchstab's function is differentiable above one away from its seam. -/
theorem hasDerivAt_buchstabFunction_of_one_lt_of_ne_two {u : Real}
    (h1 : 1 < u) (h2 : u ≠ 2) :
    HasDerivAt buchstabFunction (deriv buchstabFunction u) u := by
  rcases lt_or_gt_of_ne h2 with hu | hu
  · have h := hasDerivAt_buchstabFunction_of_one_lt_of_lt_two h1 hu
    exact h.congr_deriv h.deriv.symm
  · have h := hasDerivAt_buchstabFunction hu
    exact h.congr_deriv h.deriv.symm

/-- The slope times the translated argument has a uniform elementary bound. -/
theorem abs_deriv_buchstabFunction_mul_add_le_two {u : Real}
    (h1 : 1 < u) (h2 : u ≠ 2) :
    |deriv buchstabFunction u| * (u + 1) ≤ 2 := by
  obtain ⟨slope, hslope, hbound⟩ :=
    exists_buchstabFunction_slope_bound h1 h2
  rw [hslope.deriv]
  exact hbound

/-- The explicit derivative bound used for the PNT remainder integral. -/
theorem abs_deriv_buchstabPrimeWeight_le {x t : Real}
    (hx : 0 ≤ x) (ht : 2 ≤ t)
    (hv : 1 < buchstabArgument x t)
    (hseam : buchstabArgument x t ≠ 2) :
    |deriv (buchstabPrimeWeight x) t| ≤
      x * (Real.log t + 3) / (t ^ 2 * Real.log t ^ 2) := by
  have ht1 : 1 < t := by linarith
  have ht0 : 0 < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hvadd : 0 < buchstabArgument x t + 1 := by linarith
  have homega := buchstabFunction_mem_Icc hv.le
  have hslope :=
    abs_deriv_buchstabFunction_mul_add_le_two hv hseam
  have hfirst :
      |(Real.log t + 1) * buchstabFunction (buchstabArgument x t)| ≤
        Real.log t + 1 := by
    rw [abs_mul, abs_of_pos (by linarith : 0 < Real.log t + 1),
      abs_of_pos (buchstabFunction_pos hv.le)]
    nlinarith [homega.2]
  have hsecond :
      |(buchstabArgument x t + 1) * deriv buchstabFunction
        (buchstabArgument x t)| ≤ 2 := by
    rw [abs_mul, abs_of_pos hvadd]
    simpa only [mul_comm] using hslope
  have hinner :
      |(Real.log t + 1) * buchstabFunction (buchstabArgument x t) +
          (buchstabArgument x t + 1) * deriv buchstabFunction
            (buchstabArgument x t)| ≤
        Real.log t + 3 := by
    calc
      _ ≤ |(Real.log t + 1) * buchstabFunction (buchstabArgument x t)| +
          |(buchstabArgument x t + 1) * deriv buchstabFunction
            (buchstabArgument x t)| := abs_add_le _ _
      _ ≤ (Real.log t + 1) + 2 := add_le_add hfirst hsecond
      _ = Real.log t + 3 := by ring
  have hweight := hasDerivAt_buchstabPrimeWeight ht1
    (hasDerivAt_buchstabFunction_of_one_lt_of_ne_two hv hseam)
  rw [hweight.deriv, abs_div, abs_mul, abs_neg, abs_of_nonneg hx,
    abs_of_pos (mul_pos (sq_pos_of_pos ht0) (sq_pos_of_pos hlog))]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinner hx) (by positivity)

/-- The transformed weight itself has the corresponding endpoint bound. -/
theorem abs_buchstabPrimeWeight_le {x t : Real}
    (hx : 0 ≤ x) (ht : 2 ≤ t) (hv : 1 ≤ buchstabArgument x t) :
    |buchstabPrimeWeight x t| ≤ x / (t * Real.log t) := by
  have ht1 : 1 < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos ht1
  rw [buchstabPrimeWeight, abs_div, abs_mul, abs_of_nonneg hx,
    abs_of_pos (buchstabFunction_pos hv),
    abs_of_pos (mul_pos (by linarith) hlog)]
  exact div_le_div_of_nonneg_right
    (by simpa using
      (mul_le_mul_of_nonneg_left (buchstabFunction_mem_Icc hv).2 hx))
    (by positivity)

end PrimesRestrictedDigits
