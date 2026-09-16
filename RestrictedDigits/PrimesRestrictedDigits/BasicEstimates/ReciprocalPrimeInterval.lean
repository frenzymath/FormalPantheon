import PrimesRestrictedDigits.BasicEstimates.PrimeDistribution

/-!
# Reciprocal primes on a Buchstab induction slab

This file proves the half-open reciprocal-prime upper bound used in the proof
of `MONTGOMERY-VAUGHAN-MNT-I`, Theorem 7.11. It derives only the required
consequence from elementary Chebyshev and Abel bounds, not Mertens' asymptotic.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- An elementary upper bound for reciprocal primes in a real half-open interval. -/
theorem sum_prime_inv_halfOpen_le
    (a b : Real) (ha : 1 < a) (hb : 1 ≤ b) :
    (∑ p ∈ (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
      (p : Real)⁻¹) ≤
      (Real.log a)⁻¹ * (Real.log 4 * (1 + Real.log b)) := by
  have hloga : 0 < Real.log a := Real.log_pos ha
  have hinvloga : 0 ≤ (Real.log a)⁻¹ := (inv_pos.mpr hloga).le
  have hfloor : 1 ≤ Nat.floor b := (Nat.one_le_floor_iff b).mpr hb
  have hsubset :
      (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime ⊆
        (Nat.primesLE (Nat.floor b)).filter (fun p : Nat => a ≤ (p : Real)) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hinterval := mem_naturalLeftClosedRightOpenInterval.mp hp'.1
    have hp_le_floor : p ≤ Nat.floor b :=
      (Nat.le_floor_iff (by linarith [hb])).mpr hinterval.2.le
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primesLE.mpr ⟨hp_le_floor, hp'.2⟩, hinterval.1⟩
  calc
    (∑ p ∈ (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
        (p : Real)⁻¹) ≤
        ∑ p ∈ (Nat.primesLE (Nat.floor b)).filter
          (fun p : Nat => a ≤ (p : Real)), (p : Real)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp hnot
      positivity
    _ ≤ (Real.log a)⁻¹ *
        (Real.log 4 * (1 + Real.log (Nat.floor b : Real))) := by
      calc
        (∑ p ∈ (Nat.primesLE (Nat.floor b)).filter
            (fun p : Nat => a ≤ (p : Real)), (p : Real)⁻¹) ≤
            ∑ p ∈ (Nat.primesLE (Nat.floor b)).filter
              (fun p : Nat => a ≤ (p : Real)),
              (Real.log a)⁻¹ * (Real.log (p : Real) / (p : Real)) := by
          apply Finset.sum_le_sum
          intro p hp
          have hp_lower : a ≤ (p : Real) := (Finset.mem_filter.mp hp).2
          have hp_pos : 0 < (p : Real) :=
            lt_of_lt_of_le (by positivity) hp_lower
          have hlog_le : Real.log a ≤ Real.log (p : Real) :=
            Real.log_le_log (by positivity) hp_lower
          calc
            (p : Real)⁻¹ =
                (Real.log a)⁻¹ * (Real.log a / (p : Real)) := by
              field_simp
            _ ≤ (Real.log a)⁻¹ *
                (Real.log (p : Real) / (p : Real)) := by
              exact mul_le_mul_of_nonneg_left
                (div_le_div_of_nonneg_right hlog_le hp_pos.le) hinvloga
        _ = (Real.log a)⁻¹ *
            (∑ p ∈ (Nat.primesLE (Nat.floor b)).filter
              (fun p : Nat => a ≤ (p : Real)),
              Real.log (p : Real) / (p : Real)) := by
          rw [Finset.mul_sum]
        _ ≤ (Real.log a)⁻¹ *
            (∑ p ∈ Nat.primesLE (Nat.floor b),
              Real.log (p : Real) / (p : Real)) := by
          apply mul_le_mul_of_nonneg_left _ hinvloga
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _)
          intro p hp hps
          positivity
        _ ≤ (Real.log a)⁻¹ *
            (Real.log 4 * (1 + Real.log (Nat.floor b : Real))) := by
          exact mul_le_mul_of_nonneg_left
            (sum_prime_log_div_le_log_four_mul_one_add_log
              (Nat.floor b) hfloor) hinvloga
    _ ≤ (Real.log a)⁻¹ * (Real.log 4 * (1 + Real.log b)) := by
      have hlogfloor : Real.log (Nat.floor b : Real) ≤ Real.log b := by
        apply Real.log_le_log
        · exact_mod_cast (Nat.zero_lt_of_lt hfloor)
        · exact Nat.floor_le (by linarith [hb])
      have hcoef : 0 ≤ (Real.log a)⁻¹ * Real.log 4 :=
        mul_nonneg hinvloga (Real.log_nonneg (by norm_num))
      nlinarith

/-- A uniform reciprocal-prime bound on one Buchstab induction slab. -/
theorem sum_prime_inv_buchstabSlab_le
    (x U u : Real) (hx : 0 < x) (hU : 2 ≤ U) (hUu : U ≤ u)
    (hu : u ≤ U + 1) (hlower : 2 ≤ x ^ (1 / u)) :
    (∑ p ∈
      (naturalLeftClosedRightOpenInterval (x ^ (1 / u))
        (x ^ (1 / U))).filter Nat.Prime, (p : Real)⁻¹) ≤
      Real.log 4 * ((3 / 2 : Real) + (Real.log 2)⁻¹) := by
  have hUpos : 0 < U := by linarith
  have hupos : 0 < u := hUpos.trans_le hUu
  have hx1 : 1 < x := by
    by_contra h
    have hxle : x ≤ 1 := le_of_not_gt h
    have hpowle : x ^ (1 / u) ≤ 1 :=
      Real.rpow_le_one hx.le hxle (by positivity)
    linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have ha : 1 < x ^ (1 / u) := by linarith
  have hb : 1 ≤ x ^ (1 / U) :=
    Real.one_le_rpow hx1.le (by positivity)
  apply (sum_prime_inv_halfOpen_le
    (x ^ (1 / u)) (x ^ (1 / U)) ha hb).trans
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloga : 0 < Real.log (x ^ (1 / u)) := Real.log_pos ha
  have hlog_lower : Real.log 2 ≤ Real.log (x ^ (1 / u)) :=
    Real.log_le_log (by norm_num) hlower
  have hinv_lower : (Real.log (x ^ (1 / u)))⁻¹ ≤ (Real.log 2)⁻¹ :=
    (inv_le_inv₀ hloga hlog2).mpr hlog_lower
  have hratio :
      (Real.log (x ^ (1 / u)))⁻¹ * Real.log (x ^ (1 / U)) = u / U := by
    rw [Real.log_rpow hx, Real.log_rpow hx]
    field_simp [hlogx.ne']
  have hratio_le : u / U ≤ 3 / 2 := by
    rw [div_le_iff₀ hUpos]
    nlinarith
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc
    (Real.log (x ^ (1 / u)))⁻¹ *
        (Real.log 4 * (1 + Real.log (x ^ (1 / U)))) =
      Real.log 4 * ((Real.log (x ^ (1 / u)))⁻¹ + u / U) := by
        rw [← hratio]
        ring
    _ ≤ Real.log 4 * ((Real.log 2)⁻¹ + 3 / 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hinv_lower hratio_le) hlog4
    _ = Real.log 4 * ((3 / 2 : Real) + (Real.log 2)⁻¹) := by ring

end PrimesRestrictedDigits
