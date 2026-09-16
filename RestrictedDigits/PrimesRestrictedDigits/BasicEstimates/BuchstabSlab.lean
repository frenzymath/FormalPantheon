import PrimesRestrictedDigits.BasicEstimates.BuchstabPrimeWeight

/-!
# Geometry of a Buchstab induction slab

This file formalizes the power-interval geometry in the induction for
`MONTGOMERY-VAUGHAN-MNT-I`, Theorem 7.11, pp. 217--218.
-/

namespace PrimesRestrictedDigits

/-- The Buchstab argument has the closed source range on a closed power interval. -/
theorem buchstabArgument_mem_Icc_powerInterval
    {m : Nat} {x u t : Real} (hx : 1 < x) (hm : 0 < m)
    (hmu : (m : Real) ≤ u)
    (ht : t ∈ Set.Icc (x ^ (1 / u)) (x ^ (1 / (m : Real)))) :
    buchstabArgument x t ∈ Set.Icc ((m : Real) - 1) (u - 1) := by
  have hx0 : 0 < x := by linarith
  have hm0 : 0 < (m : Real) := by exact_mod_cast hm
  have hu0 : 0 < u := hm0.trans_le hmu
  have hlower1 : 1 < x ^ (1 / u) :=
    Real.one_lt_rpow hx (by positivity)
  have ht1 : 1 < t := hlower1.trans_le ht.1
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hlogLower : Real.log (x ^ (1 / u)) ≤ Real.log t :=
    Real.log_le_log (by positivity) ht.1
  have hlogUpper : Real.log t ≤ Real.log (x ^ (1 / (m : Real))) :=
    Real.log_le_log (by positivity) ht.2
  rw [Real.log_rpow hx0] at hlogLower hlogUpper
  constructor
  · unfold buchstabArgument
    rw [sub_le_sub_iff_right, le_div_iff₀ hlogt]
    have hmul := mul_le_mul_of_nonneg_left hlogUpper hm0.le
    field_simp at hmul
    nlinarith
  · unfold buchstabArgument
    rw [sub_le_sub_iff_right, div_le_iff₀ hlogt]
    have hmul := mul_le_mul_of_nonneg_left hlogLower hu0.le
    field_simp at hmul
    nlinarith

/-- Strict power endpoints give the strict Buchstab-argument range. -/
theorem buchstabArgument_mem_Ioo_powerInterval
    {m : Nat} {x u t : Real} (hx : 1 < x) (hm : 0 < m)
    (hmu : (m : Real) ≤ u)
    (ht : t ∈ Set.Ioo (x ^ (1 / u)) (x ^ (1 / (m : Real)))) :
    buchstabArgument x t ∈ Set.Ioo ((m : Real) - 1) (u - 1) := by
  have hx0 : 0 < x := by linarith
  have hm0 : 0 < (m : Real) := by exact_mod_cast hm
  have hu0 : 0 < u := hm0.trans_le hmu
  have hlower1 : 1 < x ^ (1 / u) :=
    Real.one_lt_rpow hx (by positivity)
  have ht1 : 1 < t := hlower1.trans ht.1
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hlogLower : Real.log (x ^ (1 / u)) < Real.log t :=
    Real.log_lt_log (by positivity) ht.1
  have hlogUpper : Real.log t < Real.log (x ^ (1 / (m : Real))) :=
    Real.log_lt_log (by positivity) ht.2
  rw [Real.log_rpow hx0] at hlogLower hlogUpper
  constructor
  · unfold buchstabArgument
    rw [sub_lt_sub_iff_right, lt_div_iff₀ hlogt]
    have hmul := mul_lt_mul_of_pos_left hlogUpper hm0
    field_simp at hmul
    nlinarith
  · unfold buchstabArgument
    rw [sub_lt_sub_iff_right, div_lt_iff₀ hlogt]
    have hmul := mul_lt_mul_of_pos_left hlogLower hu0
    field_simp at hmul
    nlinarith

/-- The interior of a natural induction slab avoids Buchstab's seam at two. -/
theorem buchstabArgument_one_lt_and_ne_two_of_mem_slab
    {m : Nat} {x u t : Real} (hx : 1 < x) (hm : 2 ≤ m)
    (hmu : (m : Real) ≤ u) (hu : u ≤ (m : Real) + 1)
    (ht : t ∈ Set.Ioo (x ^ (1 / u)) (x ^ (1 / (m : Real)))) :
    1 < buchstabArgument x t ∧ buchstabArgument x t ≠ 2 := by
  have hrange := buchstabArgument_mem_Ioo_powerInterval hx (by omega) hmu ht
  constructor
  · have hmreal : (2 : Real) ≤ m := by exact_mod_cast hm
    linarith [hrange.1]
  · intro hseam
    rw [hseam] at hrange
    have hm_lt_real : (m : Real) < 3 := by linarith [hrange.1]
    have hm_lt : m < 3 := by exact_mod_cast hm_lt_real
    have hm_gt : 2 < m := by
      have hm_gt_real : (2 : Real) < m := by linarith [hrange.2, hu]
      exact_mod_cast hm_gt_real
    omega

/-- The transformed-weight derivative bound instantiated on an open source slab. -/
theorem abs_deriv_buchstabPrimeWeight_le_of_mem_slab
    {m : Nat} {x u t : Real} (hx : 1 < x) (hm : 2 ≤ m)
    (hmu : (m : Real) ≤ u) (hu : u ≤ (m : Real) + 1)
    (hlower : 2 ≤ x ^ (1 / u))
    (ht : t ∈ Set.Ioo (x ^ (1 / u)) (x ^ (1 / (m : Real)))) :
    |deriv (buchstabPrimeWeight x) t| ≤
      x * (Real.log t + 3) / (t ^ 2 * Real.log t ^ 2) := by
  have hgeometry :=
    buchstabArgument_one_lt_and_ne_two_of_mem_slab hx hm hmu hu ht
  exact abs_deriv_buchstabPrimeWeight_le (by linarith)
    (by linarith [hlower, ht.1]) hgeometry.1 hgeometry.2

/-- The endpoint weight bound instantiated on a closed source slab. -/
theorem abs_buchstabPrimeWeight_le_of_mem_closed_slab
    {m : Nat} {x u t : Real} (hx : 1 < x) (hm : 2 ≤ m)
    (hmu : (m : Real) ≤ u) (hlower : 2 ≤ x ^ (1 / u))
    (ht : t ∈ Set.Icc (x ^ (1 / u)) (x ^ (1 / (m : Real)))) :
    |buchstabPrimeWeight x t| ≤ x / (t * Real.log t) := by
  have hrange :=
    buchstabArgument_mem_Icc_powerInterval hx (by omega) hmu ht
  have hmreal : (2 : Real) ≤ m := by exact_mod_cast hm
  exact abs_buchstabPrimeWeight_le (by linarith) (by linarith [hlower, ht.1])
    (by linarith [hrange.1])

end PrimesRestrictedDigits
