import PrimesRestrictedDigits.TypeI.LargeSieveBand
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scalar simplification of the Type I large-sieve band bound

This removes the fixed divisor `d | 10` from the one-band estimate with explicit coefficients,
then specializes it to the active real-capped fibers.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Every active real-capped decade scale is strictly positive. -/
theorem typeIDecadeScale_pos_of_mem
    {Q R : Real} (hR : R ∈ typeIDecadeScalesBelow Q) : 0 < R := by
  classical
  rcases Finset.mem_image.mp hR with ⟨q, hqCarrier, hqScale⟩
  have hqFiber : q ∈ typeIDecadeFiber Q R := by
    exact Finset.mem_filter.mpr ⟨hqCarrier, hqScale⟩
  have hqUpper := (typeIDecadeFiber_bounds hqFiber).2.1
  have hqData := (Finset.mem_filter.mp hqCarrier).2
  have hqPos : (0 : Real) < q := by
    exact_mod_cast (by omega : 0 < q)
  exact hqPos.trans_le hqUpper

/-- Complete arithmetic and endpoint data for a reduced denominator in an
active decade fiber. -/
theorem typeIDecadeFiber_data
    {Q R : Real} {q : Nat} (hq : q ∈ typeIDecadeFiber Q R) :
    1 < q ∧ q.Coprime 10 ∧ R / 10 < (q : Real) ∧ (q : Real) ≤ R := by
  have hqBounds := typeIDecadeFiber_bounds hq
  have hqCarrier := (Finset.mem_filter.mp hq).1
  have hqData := (Finset.mem_filter.mp hqCarrier).2
  exact ⟨hqData.1, hqData.2, hqBounds.1, hqBounds.2.1⟩

/-- Uniformly remove the fixed decimal divisor from the one-band Lemma 8.1
right side. -/
theorem typeILargeSieveBand_scalar_le
    (d : Nat) (S X : Real) (hd : d ∈ Nat.divisors 10)
    (hS : 0 < S) (hX : 0 ≤ X) :
    (10 / S) * largeSieveConstant *
        (((d : Real) * S) ^ (54 / 77 : Real) +
          ((d : Real) * S) ^ 2 * X ^ (-(50 / 77 : Real))) ≤
      largeSieveConstant *
        (100 * S ^ (-(23 / 77 : Real)) +
          1000 * S * X ^ (-(50 / 77 : Real))) := by
  have hdLe : d ≤ 10 := Nat.le_of_dvd (by norm_num)
    (Nat.dvd_of_mem_divisors hd)
  have hdNonneg : (0 : Real) ≤ d := by positivity
  have hdLeReal : (d : Real) ≤ 10 := by exact_mod_cast hdLe
  have hconstant : 0 ≤ largeSieveConstant := by
    unfold largeSieveConstant
    positivity
  have htail : 0 ≤ X ^ (-(50 / 77 : Real)) :=
    Real.rpow_nonneg hX _
  have hdPower : ((d : Real) ^ (54 / 77 : Real)) ≤ 10 := by
    calc
      ((d : Real) ^ (54 / 77 : Real)) ≤
          (10 : Real) ^ (54 / 77 : Real) :=
        Real.rpow_le_rpow hdNonneg hdLeReal (by norm_num)
      _ ≤ (10 : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 10 := Real.rpow_one 10
  have hSratio :
      S ^ (54 / 77 : Real) / S = S ^ (-(23 / 77 : Real)) := by
    calc
      S ^ (54 / 77 : Real) / S =
          S ^ (54 / 77 : Real) / S ^ (1 : Real) := by
        rw [Real.rpow_one]
      _ = S ^ ((54 / 77 : Real) - 1) :=
        (Real.rpow_sub hS (54 / 77 : Real) 1).symm
      _ = S ^ (-(23 / 77 : Real)) := by norm_num
  have hheadIdentity :
      (10 / S) * largeSieveConstant *
          (((d : Real) * S) ^ (54 / 77 : Real)) =
        (largeSieveConstant * (10 * (d : Real) ^ (54 / 77 : Real))) *
          S ^ (-(23 / 77 : Real)) := by
    rw [Real.mul_rpow hdNonneg hS.le]
    rw [← hSratio]
    field_simp [hS.ne']
  have hheadCoefficient :
      largeSieveConstant * (10 * (d : Real) ^ (54 / 77 : Real)) ≤
        largeSieveConstant * 100 := by
    apply mul_le_mul_of_nonneg_left _ hconstant
    nlinarith
  have hhead :
      (10 / S) * largeSieveConstant *
          (((d : Real) * S) ^ (54 / 77 : Real)) ≤
        largeSieveConstant * (100 * S ^ (-(23 / 77 : Real))) := by
    rw [hheadIdentity]
    calc
      (largeSieveConstant * (10 * (d : Real) ^ (54 / 77 : Real))) *
          S ^ (-(23 / 77 : Real)) ≤
          (largeSieveConstant * 100) * S ^ (-(23 / 77 : Real)) :=
        mul_le_mul_of_nonneg_right hheadCoefficient
          (Real.rpow_nonneg hS.le _)
      _ = largeSieveConstant *
          (100 * S ^ (-(23 / 77 : Real))) := by ring
  have hdSquare : ((d : Real) ^ 2) ≤ 100 := by
    nlinarith [sq_nonneg ((d : Real) - 10)]
  have htailIdentity :
      (10 / S) * largeSieveConstant *
          (((d : Real) * S) ^ 2 * X ^ (-(50 / 77 : Real))) =
        (largeSieveConstant * (10 * (d : Real) ^ 2)) *
          (S * X ^ (-(50 / 77 : Real))) := by
    field_simp [hS.ne']
  have htailCoefficient :
      largeSieveConstant * (10 * (d : Real) ^ 2) ≤
        largeSieveConstant * 1000 := by
    apply mul_le_mul_of_nonneg_left _ hconstant
    nlinarith
  have hsecond :
      (10 / S) * largeSieveConstant *
          (((d : Real) * S) ^ 2 * X ^ (-(50 / 77 : Real))) ≤
        largeSieveConstant *
          (1000 * S * X ^ (-(50 / 77 : Real))) := by
    rw [htailIdentity]
    calc
      (largeSieveConstant * (10 * (d : Real) ^ 2)) *
          (S * X ^ (-(50 / 77 : Real))) ≤
          (largeSieveConstant * 1000) *
            (S * X ^ (-(50 / 77 : Real))) :=
        mul_le_mul_of_nonneg_right htailCoefficient
          (mul_nonneg hS.le htail)
      _ = largeSieveConstant *
          (1000 * S * X ^ (-(50 / 77 : Real))) := by ring
  calc
    (10 / S) * largeSieveConstant *
        (((d : Real) * S) ^ (54 / 77 : Real) +
          ((d : Real) * S) ^ 2 * X ^ (-(50 / 77 : Real))) =
        (10 / S) * largeSieveConstant *
            (((d : Real) * S) ^ (54 / 77 : Real)) +
          (10 / S) * largeSieveConstant *
            (((d : Real) * S) ^ 2 * X ^ (-(50 / 77 : Real))) := by ring
    _ ≤ largeSieveConstant * (100 * S ^ (-(23 / 77 : Real))) +
        largeSieveConstant *
          (1000 * S * X ^ (-(50 / 77 : Real))) :=
      add_le_add hhead hsecond
    _ = largeSieveConstant *
        (100 * S ^ (-(23 / 77 : Real)) +
          1000 * S * X ^ (-(50 / 77 : Real))) := by ring

/-- The explicit large-sieve bound on one active real-capped Type I fiber. -/
theorem sum_typeIDecadeFiber_div_le_largeSieve
    (digit : Fin 10) (length d : Nat) {Q R : Real}
    (hd : d ∈ Nat.divisors 10) (hR : R ∈ typeIDecadeScalesBelow Q) :
    (∑ q ∈ typeIDecadeFiber Q R,
      typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
      largeSieveConstant *
        (100 * R ^ (-(23 / 77 : Real)) +
          1000 * R *
            (((10 ^ length : Nat) : Real) ^ (-(50 / 77 : Real)))) := by
  calc
    (∑ q ∈ typeIDecadeFiber Q R,
        typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
        (10 / R) * largeSieveConstant *
          (((d : Real) * R) ^ (54 / 77 : Real) +
            ((d : Real) * R) ^ 2 *
              (((10 ^ length : Nat) : Real) ^ (-(50 / 77 : Real)))) :=
      sum_typeIReducedFrequencyMass_div_le_largeSieve
        digit length d (typeIDecadeFiber Q R) R hd
          (typeIDecadeScale_pos_of_mem hR).le
          (fun q hq => typeIDecadeFiber_data hq)
    _ ≤ _ := typeILargeSieveBand_scalar_le d R
      (((10 ^ length : Nat) : Real)) hd
        (typeIDecadeScale_pos_of_mem hR) (by positivity)

end

end PrimesRestrictedDigits
