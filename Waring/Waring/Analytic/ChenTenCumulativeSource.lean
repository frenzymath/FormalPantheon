import Waring.Analytic.ChenTenCumulativeDifference

/-!
# Scale transfer for Chen's cumulative-count error

This file converts lower and upper bounds on the averaging length into the
common error scale used for `scratchShiftSquareCount`, then packages the
cumulative estimate consumed by the singular-integral argument.
-/

set_option autoImplicit false

namespace Waring.Analytic

noncomputable section

/-- A lower averaging-length bound controls the `K15` error scale. -/
theorem chenTen_K_scale_of_averageLength_lower
    {P N M : Nat} (hP : 0 < P) (hN : 0 < N)
    (hMlower :
      (N : Real) ^ (4 / 5 : Real) * (P : Real) ^ (1 / 5 : Real) ≤
        (M : Real)) :
    (N : Real) ^ (14 / 5 : Real) * (M : Real) ≤
      (N : Real) ^ 2 * (M : Real) ^ 2 *
        (P : Real) ^ (-1 / 5 : Real) := by
  have hPR : (0 : Real) < P := by exact_mod_cast hP
  have hNR : (0 : Real) < N := by exact_mod_cast hN
  have hpinv : (P : Real) ^ (1 / 5 : Real) *
      (P : Real) ^ (-1 / 5 : Real) = 1 := by
    rw [← Real.rpow_add hPR]
    norm_num
  have hsmall : (N : Real) ^ (4 / 5 : Real) ≤
      (M : Real) * (P : Real) ^ (-1 / 5 : Real) := by
    have hmul := mul_le_mul_of_nonneg_right hMlower
      (Real.rpow_nonneg hPR.le (-1 / 5 : Real))
    calc
      (N : Real) ^ (4 / 5 : Real) =
          ((N : Real) ^ (4 / 5 : Real) * (P : Real) ^ (1 / 5 : Real)) *
            (P : Real) ^ (-1 / 5 : Real) := by rw [mul_assoc, hpinv, mul_one]
      _ ≤ (M : Real) * (P : Real) ^ (-1 / 5 : Real) := hmul
  have hpow : (N : Real) ^ (14 / 5 : Real) =
      (N : Real) ^ 2 * (N : Real) ^ (4 / 5 : Real) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hNR]
    norm_num
  rw [hpow]
  calc
    (N : Real) ^ 2 * (N : Real) ^ (4 / 5 : Real) * (M : Real) ≤
        (N : Real) ^ 2 *
          ((M : Real) * (P : Real) ^ (-1 / 5 : Real)) * (M : Real) := by
      gcongr
    _ = (N : Real) ^ 2 * (M : Real) ^ 2 *
        (P : Real) ^ (-1 / 5 : Real) := by ring

/-- An upper averaging-length bound controls the cubic finite-difference scale. -/
theorem chenTen_cube_scale_of_averageLength_upper
    {P N M : Nat} (hMupper :
      (M : Real) ≤ (N : Real) * (P : Real) ^ (-1 / 5 : Real)) :
    (N : Real) * (M : Real) ^ 3 ≤
      (N : Real) ^ 2 * (M : Real) ^ 2 *
        (P : Real) ^ (-1 / 5 : Real) := by
  calc
    (N : Real) * (M : Real) ^ 3 =
        ((N : Real) * (M : Real) ^ 2) * (M : Real) := by ring
    _ ≤ ((N : Real) * (M : Real) ^ 2) *
        ((N : Real) * (P : Real) ^ (-1 / 5 : Real)) := by
      gcongr
    _ = (N : Real) ^ 2 * (M : Real) ^ 2 *
        (P : Real) ^ (-1 / 5 : Real) := by ring

private theorem fifteen_le_fifthRoot_of_pow_le
    {X : Nat} (hX : 15 ^ 5 ≤ X) :
    (15 : Real) ≤ (X : Real) ^ (1 / (5 : Real)) := by
  have hcast : ((15 : Real) ^ 5) ≤ (X : Real) := by exact_mod_cast hX
  have hr := Real.rpow_le_rpow (by positivity) hcast (by norm_num :
    (0 : Real) ≤ 1 / 5)
  calc
    (15 : Real) = ((15 : Real) ^ 5) ^ (1 / (5 : Real)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by positivity : (0 : Real) ≤ 15)]
      norm_num
    _ ≤ (X : Real) ^ (1 / (5 : Real)) := hr

/-- Admissible lower and upper scales imply the cumulative shift-count error estimate. -/
theorem chenTen_shiftSquareCount_cumulative_error_of_scales
    {P N M : Nat} (hP : 0 < P) (hN : 0 < N) (hM : 0 < M)
    (hRoom : 15 ^ 5 + 2 * M + 1 ≤ N)
    (hNPow : N ≤ (P + 1) ^ 5)
    (hMlower :
      (N : Real) ^ (4 / 5 : Real) * (P : Real) ^ (1 / 5 : Real) ≤
        (M : Real))
    (hMupper :
      (M : Real) ≤ (N : Real) * (P : Real) ^ (-1 / 5 : Real)) :
    |(scratchShiftSquareCount P N M : Real) -
        (3 * chenTenT15 * (N : Real) ^ 2) * (M : Real) ^ 2| ≤
      (3000 * chenTenT15 * (N : Real) ^ 2 *
        (P : Real) ^ (-1 / 5 : Real)) * (M : Real) ^ 2 := by
  have hMN : 2 * M + 2 ≤ N := by omega
  have hrootA : ∀ v ∈ scratchShiftSet M,
      (15 : Real) ≤ ((N - v - 1 : Nat) : Real) ^ (1 / (5 : Real)) := by
    intro v hv
    have hvM : v ≤ M := (Finset.mem_Icc.mp hv).2
    apply fifteen_le_fifthRoot_of_pow_le
    omega
  have hrootB : ∀ v ∈ scratchShiftSet M,
      (15 : Real) ≤ ((N - v - M - 1 : Nat) : Real) ^ (1 / (5 : Real)) := by
    intro v hv
    have hvM : v ≤ M := (Finset.mem_Icc.mp hv).2
    apply fifteen_le_fifthRoot_of_pow_le
    omega
  exact scratch_shiftSquareCount_cumulative_error hM hMN hNPow hrootA hrootB
    (chenTen_K_scale_of_averageLength_lower hP hN hMlower)
    (chenTen_cube_scale_of_averageLength_upper hMupper)

end

end Waring.Analytic
