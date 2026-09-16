import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Scalar domains for the finite Rosser recurrences

These lemmas convert Iwaniec's logarithmic ratio hypotheses into the power conditions and
strict inner domains used by equations (4.4)--(4.6).
-/

namespace PrimesRestrictedDigits

/-- A lower bound for `log y / log z` gives the corresponding power bound. -/
theorem power_le_of_natCast_le_log_div_log
    {y z : Real} {n : Nat} (hy : 2 <= y) (hz : 2 <= z)
    (h : (n : Real) <= Real.log y / Real.log z) :
    z ^ n <= y := by
  have hyPos : 0 < y := by linarith
  have hzPos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  apply (Real.log_le_log_iff (pow_pos hzPos n) hyPos).mp
  rw [Real.log_pow]
  exact (le_div_iff₀ hlogz).mp h

/-- An upper bound for `log y / log z` gives the reverse power bound. -/
theorem le_power_of_log_div_log_le_natCast
    {y z : Real} {n : Nat} (hy : 2 <= y) (hz : 2 <= z)
    (h : Real.log y / Real.log z <= (n : Real)) :
    y <= z ^ n := by
  have hyPos : 0 < y := by linarith
  have hzPos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  apply (Real.log_le_log_iff hyPos (pow_pos hzPos n)).mp
  rw [Real.log_pow]
  exact (div_le_iff₀ hlogz).mp h

private theorem innerLevel_gt_cutoff_of_sq_le
    {y z : Real} {p : Nat} (hp : p.Prime)
    (hpz : (p : Real) < z) (hpow : z ^ 2 <= y) :
    z < y / (p : Real) := by
  have hpPos : 0 < (p : Real) := by exact_mod_cast hp.pos
  rw [lt_div_iff₀ hpPos]
  have hzPos : 0 < z := hpPos.trans hpz
  have hmul : z * (p : Real) < z * z :=
    mul_lt_mul_of_pos_left hpz hzPos
  nlinarith

private theorem one_lt_innerLogRatio_of_sq_le
    {y z : Real} {p : Nat} (hp : p.Prime)
    (hpz : (p : Real) < z) (hpow : z ^ 2 <= y) :
    1 < Real.log (y / (p : Real)) / Real.log (p : Real) := by
  have hpPos : 0 < (p : Real) := by exact_mod_cast hp.pos
  have hpOne : 1 < (p : Real) := by exact_mod_cast hp.one_lt
  have hpSq : (p : Real) ^ 2 < z ^ 2 :=
    pow_lt_pow_left₀ hpz (le_of_lt hpPos) (by norm_num)
  have hpDiv : (p : Real) < y / (p : Real) := by
    rw [lt_div_iff₀ hpPos]
    nlinarith
  have hlogp : 0 < Real.log (p : Real) := Real.log_pos hpOne
  apply (lt_div_iff₀ hlogp).mpr
  simpa using Real.log_lt_log hpPos hpDiv

private theorem innerLevel_gt_cutoffSq_of_cube_le
    {y z : Real} {p : Nat} (hp : p.Prime)
    (hpz : (p : Real) < z) (hpow : z ^ 3 <= y) :
    z ^ 2 < y / (p : Real) := by
  have hpPos : 0 < (p : Real) := by exact_mod_cast hp.pos
  rw [lt_div_iff₀ hpPos]
  have hzPos : 0 < z := hpPos.trans hpz
  have hzSqPos : 0 < z ^ 2 := pow_pos hzPos 2
  have hmul : z ^ 2 * (p : Real) < z ^ 2 * z :=
    mul_lt_mul_of_pos_left hpz hzSqPos
  nlinarith

private theorem two_lt_innerLogRatio_of_cube_le
    {y z : Real} {p : Nat} (hp : p.Prime)
    (hpz : (p : Real) < z) (hpow : z ^ 3 <= y) :
    2 < Real.log (y / (p : Real)) / Real.log (p : Real) := by
  have hpPos : 0 < (p : Real) := by exact_mod_cast hp.pos
  have hpOne : 1 < (p : Real) := by exact_mod_cast hp.one_lt
  have hpCube : (p : Real) ^ 3 < z ^ 3 :=
    pow_lt_pow_left₀ hpz (le_of_lt hpPos) (by norm_num)
  have hpSqDiv : (p : Real) ^ 2 < y / (p : Real) := by
    rw [lt_div_iff₀ hpPos]
    nlinarith
  have hlogp : 0 < Real.log (p : Real) := Real.log_pos hpOne
  apply (lt_div_iff₀ hlogp).mpr
  have hlog := Real.log_lt_log (pow_pos hpPos 2) hpSqDiv
  rw [Real.log_pow] at hlog
  norm_num at hlog ⊢
  exact hlog

/-- The outer primes in (4.4) have ratio strictly greater than one after the
head is removed. -/
theorem rosserInnerDomains_of_two_le_logRatio
    {y z : Real} {p : Nat} (hy : 2 <= y) (hz : 2 <= z)
    (hp : p.Prime) (hpz : (p : Real) < z)
    (hratio : (2 : Real) <= Real.log y / Real.log z) :
    z < y / (p : Real) ∧
      1 < Real.log (y / (p : Real)) / Real.log (p : Real) := by
  have hpow : z ^ 2 <= y :=
    power_le_of_natCast_le_log_div_log hy hz hratio
  exact ⟨innerLevel_gt_cutoff_of_sq_le hp hpz hpow,
    one_lt_innerLogRatio_of_sq_le hp hpz hpow⟩

/-- The outer primes in (4.5) have ratio strictly greater than two after the
head is removed. -/
theorem rosserInnerDomains_of_three_le_logRatio
    {y z : Real} {p : Nat} (hy : 2 <= y) (hz : 2 <= z)
    (hp : p.Prime) (hpz : (p : Real) < z)
    (hratio : (3 : Real) <= Real.log y / Real.log z) :
    z ^ 2 < y / (p : Real) ∧
      2 < Real.log (y / (p : Real)) / Real.log (p : Real) := by
  have hpow : z ^ 3 <= y :=
    power_le_of_natCast_le_log_div_log hy hz hratio
  exact ⟨innerLevel_gt_cutoffSq_of_cube_le hp hpz hpow,
    two_lt_innerLogRatio_of_cube_le hp hpz hpow⟩

end PrimesRestrictedDigits
