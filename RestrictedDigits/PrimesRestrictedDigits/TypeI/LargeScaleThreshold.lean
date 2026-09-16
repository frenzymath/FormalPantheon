import PrimesRestrictedDigits.TypeI.LargeSieveBandScalars
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The large-scale threshold in the Type I estimate

This applies the source split `log(X)^(4*A+8) < R` and the global Type I level to the explicit
one-band estimate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem typeILargeBand_head_le
    {saving X R : Real} (hsaving : 0 < saving)
    (hlog : 1 ≤ Real.log X)
    (hR : Real.log X ^ (4 * saving + 8) < R) :
    R ^ (-(23 / 77 : Real)) ≤
      Real.log X ^ (-(saving + 2)) := by
  have hlogPos : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hthresholdPos : 0 < Real.log X ^ (4 * saving + 8) :=
    Real.rpow_pos_of_pos hlogPos _
  calc
    R ^ (-(23 / 77 : Real)) ≤
        (Real.log X ^ (4 * saving + 8)) ^ (-(23 / 77 : Real)) :=
      Real.rpow_le_rpow_of_nonpos hthresholdPos hR.le (by norm_num)
    _ = Real.log X ^
        ((4 * saving + 8) * (-(23 / 77 : Real))) :=
      (Real.rpow_mul hlogPos.le _ _).symm
    _ ≤ Real.log X ^ (-(saving + 2)) := by
      apply Real.rpow_le_rpow_of_exponent_le hlog
      nlinarith

private theorem typeILargeBand_tail_le
    {saving X Q R : Real} (hsaving : 0 < saving) (hX : 0 < X)
    (hlog : 1 ≤ Real.log X) (hRQ : R ≤ Q)
    (hQ : Q ≤ X ^ (50 / 77 : Real) *
      Real.log X ^ (-2 * saving - 2)) :
    R * X ^ (-(50 / 77 : Real)) ≤
      Real.log X ^ (-(saving + 2)) := by
  have hdecay : 0 ≤ X ^ (-(50 / 77 : Real)) :=
    Real.rpow_nonneg hX.le _
  have hcancel :
      X ^ (50 / 77 : Real) * X ^ (-(50 / 77 : Real)) = 1 := by
    rw [← Real.rpow_add hX]
    norm_num
  calc
    R * X ^ (-(50 / 77 : Real)) ≤
        Q * X ^ (-(50 / 77 : Real)) :=
      mul_le_mul_of_nonneg_right hRQ hdecay
    _ ≤ (X ^ (50 / 77 : Real) *
          Real.log X ^ (-2 * saving - 2)) *
        X ^ (-(50 / 77 : Real)) :=
      mul_le_mul_of_nonneg_right hQ hdecay
    _ = Real.log X ^ (-2 * saving - 2) := by
      rw [mul_assoc, mul_comm (Real.log X ^ (-2 * saving - 2)),
        ← mul_assoc, hcancel, one_mul]
    _ ≤ Real.log X ^ (-(saving + 2)) := by
      apply Real.rpow_le_rpow_of_exponent_le hlog
      linarith

/-- Each large active-scale right side saves two logarithms beyond the
requested exponent. -/
theorem typeILargeSieveBand_le_logPower
    {saving X Q R : Real} (hsaving : 0 < saving) (hX : 0 < X)
    (hlog : 1 ≤ Real.log X)
    (hRLower : Real.log X ^ (4 * saving + 8) < R)
    (hRQ : R ≤ Q)
    (hQ : Q ≤ X ^ (50 / 77 : Real) *
      Real.log X ^ (-2 * saving - 2)) :
    largeSieveConstant *
        (100 * R ^ (-(23 / 77 : Real)) +
          1000 * R * X ^ (-(50 / 77 : Real))) ≤
      1100 * largeSieveConstant *
        Real.log X ^ (-(saving + 2)) := by
  have hhead := typeILargeBand_head_le hsaving hlog hRLower
  have htail := typeILargeBand_tail_le hsaving hX hlog hRQ hQ
  have hconstant : 0 ≤ largeSieveConstant := by
    unfold largeSieveConstant
    positivity
  have htailScaled :
      1000 * R * X ^ (-(50 / 77 : Real)) ≤
        1000 * Real.log X ^ (-(saving + 2)) := by
    calc
      1000 * R * X ^ (-(50 / 77 : Real)) =
          1000 * (R * X ^ (-(50 / 77 : Real))) := by ring
      _ ≤ 1000 * Real.log X ^ (-(saving + 2)) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
  calc
    largeSieveConstant *
        (100 * R ^ (-(23 / 77 : Real)) +
          1000 * R * X ^ (-(50 / 77 : Real))) ≤
        largeSieveConstant *
          (100 * Real.log X ^ (-(saving + 2)) +
            1000 * Real.log X ^ (-(saving + 2))) := by
      apply mul_le_mul_of_nonneg_left _ hconstant
      exact add_le_add
        (mul_le_mul_of_nonneg_left hhead (by norm_num)) htailScaled
    _ = 1100 * largeSieveConstant *
        Real.log X ^ (-(saving + 2)) := by ring

/-- The published Type I level is no larger than its ambient analytic scale. -/
theorem typeILevel_le_scale
    {saving X Q : Real} (hsaving : 0 < saving) (hX : 1 ≤ X)
    (hlog : 1 ≤ Real.log X)
    (hQ : Q ≤ X ^ (50 / 77 : Real) *
      Real.log X ^ (-2 * saving - 2)) :
    Q ≤ X := by
  have hXpow : X ^ (50 / 77 : Real) ≤ X := by
    calc
      X ^ (50 / 77 : Real) ≤ X ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
      _ = X := Real.rpow_one X
  have hlogpow : Real.log X ^ (-2 * saving - 2) ≤ 1 := by
    calc
      Real.log X ^ (-2 * saving - 2) ≤
          Real.log X ^ (0 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hlog (by linarith)
      _ = 1 := Real.rpow_zero _
  calc
    Q ≤ X ^ (50 / 77 : Real) *
        Real.log X ^ (-2 * saving - 2) := hQ
    _ ≤ X * 1 := mul_le_mul hXpow hlogpow (by positivity) (by positivity)
    _ = X := mul_one X

/-- Every active real-capped scale remains below the original cutoff. -/
theorem typeIDecadeScale_le_cutoff_of_mem
    {Q R : Real} (hR : R ∈ typeIDecadeScalesBelow Q) : R ≤ Q := by
  classical
  rcases Finset.mem_image.mp hR with ⟨q, hqCarrier, hqScale⟩
  have hqFiber : q ∈ typeIDecadeFiber Q R :=
    Finset.mem_filter.mpr ⟨hqCarrier, hqScale⟩
  exact (typeIDecadeFiber_bounds hqFiber).2.2

/-- The explicit logarithmic bound for one active large Type I fiber. -/
theorem sum_typeIDecadeFiber_div_le_largeBand
    (saving : Real) (digit : Fin 10) (length d : Nat) {Q R : Real}
    (hd : d ∈ Nat.divisors 10) (hsaving : 0 < saving)
    (hlog : 1 ≤ Real.log (((10 ^ length : Nat) : Real)))
    (hQ : Q ≤ (((10 ^ length : Nat) : Real) ^ (50 / 77 : Real)) *
      Real.log (((10 ^ length : Nat) : Real)) ^ (-2 * saving - 2))
    (hR : R ∈ typeIDecadeScalesBelow Q)
    (hRLower : Real.log (((10 ^ length : Nat) : Real)) ^
      (4 * saving + 8) < R) :
    (∑ q ∈ typeIDecadeFiber Q R,
      typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
      1100 * largeSieveConstant *
        Real.log (((10 ^ length : Nat) : Real)) ^ (-(saving + 2)) := by
  calc
    (∑ q ∈ typeIDecadeFiber Q R,
        typeIReducedFrequencyMass digit length d q / (q : Real)) ≤
        largeSieveConstant *
          (100 * R ^ (-(23 / 77 : Real)) +
            1000 * R *
              (((10 ^ length : Nat) : Real) ^ (-(50 / 77 : Real)))) :=
      sum_typeIDecadeFiber_div_le_largeSieve digit length d
        hd hR
    _ ≤ _ := typeILargeSieveBand_le_logPower hsaving (by positivity) hlog
      hRLower (typeIDecadeScale_le_cutoff_of_mem hR) hQ

end

end PrimesRestrictedDigits
