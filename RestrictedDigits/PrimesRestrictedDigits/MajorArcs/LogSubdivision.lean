import PrimesRestrictedDigits.MajorArcs.Phase
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Logarithmic major-arc subdivision

This gives an integral interpretation of the subdivision count on published
pp. 187--188 and discharges the omitted size condition in its phase sum.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The natural exponent used to make the source subdivision count integral. -/
def majorArcLogSubdivisionExponent (D ell : ℕ) : ℕ :=
  10 * D + 10 * ell

/-- The integral reciprocal of the logarithmic subdivision width. -/
noncomputable def majorArcLogSubdivisionCount (X D ell : ℕ) : ℕ :=
  Nat.ceil (Real.log (X : ℝ)) ^ majorArcLogSubdivisionExponent D ell

theorem majorArcLogSubdivisionExponent_pos
    {D ell : ℕ} (hell : 0 < ell) :
    0 < majorArcLogSubdivisionExponent D ell := by
  dsimp [majorArcLogSubdivisionExponent]
  omega

theorem majorArcLogSubdivisionCount_pos
    {X D ell : ℕ} (hX : 1 < X) :
    0 < majorArcLogSubdivisionCount X D ell := by
  apply pow_pos
  exact Nat.ceil_pos.mpr (Real.log_pos (by exact_mod_cast hX))

/-- At the source range and positive arity, the logarithmic subdivision has
at least one positive block after block zero. -/
theorem majorArcLogSubdivisionCount_one_lt
    {X D ell : ℕ} (hX : 4 ≤ X) (hell : 0 < ell) :
    1 < majorArcLogSubdivisionCount X D ell := by
  let B := Nat.ceil (Real.log (X : ℝ))
  have hXpos : (0 : ℝ) < X := by positivity
  have hlog : 1 < Real.log (X : ℝ) :=
    (Real.lt_log_iff_exp_lt hXpos).mpr <|
      Real.exp_one_lt_three.trans_le
        (by exact_mod_cast (show 3 ≤ X by omega))
  have hB : 1 < B := by
    rw [← Nat.add_one_le_iff, show 1 + 1 = 2 by norm_num,
      Nat.add_one_le_ceil_iff]
    simpa using hlog
  rw [majorArcLogSubdivisionCount]
  exact Nat.one_lt_pow
    (majorArcLogSubdivisionExponent_pos hell).ne' hB

theorem majorArcLogSubdivisionWidth_eq (X D ell : ℕ) :
    majorArcSubdivisionWidth (majorArcLogSubdivisionCount X D ell) =
      (((Nat.ceil (Real.log (X : ℝ)) : ℕ) : ℝ) ^
        majorArcLogSubdivisionExponent D ell)⁻¹ := by
  simp [majorArcSubdivisionWidth, majorArcLogSubdivisionCount]

theorem log_pow_le_majorArcLogSubdivisionCount
    {X D ell : ℕ} (hX : 1 < X) :
    Real.log (X : ℝ) ^ majorArcLogSubdivisionExponent D ell ≤
      (majorArcLogSubdivisionCount X D ell : ℝ) := by
  rw [majorArcLogSubdivisionCount, Nat.cast_pow]
  apply pow_le_pow_left₀
  · exact (Real.log_pos (by exact_mod_cast hX)).le
  · exact Nat.le_ceil _

theorem majorArcLogSubdivisionWidth_le_inv_log_pow
    {X D ell : ℕ} (hX : 1 < X) :
    majorArcSubdivisionWidth (majorArcLogSubdivisionCount X D ell) ≤
      (Real.log (X : ℝ) ^ majorArcLogSubdivisionExponent D ell)⁻¹ := by
  rw [majorArcLogSubdivisionWidth_eq]
  have hpos : 0 < Real.log (X : ℝ) ^ majorArcLogSubdivisionExponent D ell :=
    pow_pos (Real.log_pos (by exact_mod_cast hX)) _
  have hle := log_pow_le_majorArcLogSubdivisionCount
    (D := D) (ell := ell) hX
  rw [majorArcLogSubdivisionCount, Nat.cast_pow] at hle
  exact inv_anti₀ hpos hle

theorem majorArcLogSubdivisionCount_le_two_mul_log_pow
    {X D ell : ℕ} (hX : 4 ≤ X) :
    (majorArcLogSubdivisionCount X D ell : ℝ) ≤
      (2 * Real.log (X : ℝ)) ^ majorArcLogSubdivisionExponent D ell := by
  have hXpos : (0 : ℝ) < X := by positivity
  have hlog : 1 < Real.log (X : ℝ) :=
    (Real.lt_log_iff_exp_lt hXpos).mpr <|
      Real.exp_one_lt_three.trans_le (by exact_mod_cast (show 3 ≤ X by omega))
  rw [majorArcLogSubdivisionCount, Nat.cast_pow]
  apply pow_le_pow_left₀
  · positivity
  · exact Nat.ceil_le_two_mul (by linarith)

theorem majorArcFrequency_natAbs_lt_logSubdivisionCount
    {X D ell : ℕ} {c : ℤ} (hX : 4 ≤ X) (hell : 0 < ell)
    (hc : |(c : ℝ)| ≤ Real.log (X : ℝ) ^ D) :
    c.natAbs < majorArcLogSubdivisionCount X D ell := by
  let B := Nat.ceil (Real.log (X : ℝ))
  let N := majorArcLogSubdivisionExponent D ell
  have hXpos : (0 : ℝ) < X := by positivity
  have hlog : 1 < Real.log (X : ℝ) :=
    (Real.lt_log_iff_exp_lt hXpos).mpr <|
      Real.exp_one_lt_three.trans_le (by exact_mod_cast (show 3 ≤ X by omega))
  have hB : 1 < B := by
    rw [← Nat.add_one_le_iff, show 1 + 1 = 2 by norm_num,
      Nat.add_one_le_ceil_iff]
    simpa using hlog
  have hDN : D < N := by
    dsimp [N, majorArcLogSubdivisionExponent]
    omega
  have hlogNonneg : 0 ≤ Real.log (X : ℝ) := le_trans (by norm_num) hlog.le
  have hbase : Real.log (X : ℝ) ≤ (B : ℝ) := Nat.le_ceil _
  have habs : (c.natAbs : ℝ) ≤ (B : ℝ) ^ D := by
    calc
      (c.natAbs : ℝ) = |(c : ℝ)| := by simp
      _ ≤ Real.log (X : ℝ) ^ D := hc
      _ ≤ (B : ℝ) ^ D := pow_le_pow_left₀ hlogNonneg hbase D
  have hpow : (B : ℝ) ^ D < (B : ℝ) ^ N :=
    pow_lt_pow_right₀ (by exact_mod_cast hB) hDN
  have hreal : (c.natAbs : ℝ) < ((B ^ N : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    exact habs.trans_lt hpow
  exact_mod_cast hreal

theorem majorArcPhase_sum_logSubdivision_eq_neg_one
    {X D ell : ℕ} {c : ℤ} (hX : 4 ≤ X) (hell : 0 < ell)
    (hc0 : c ≠ 0) (hc : |(c : ℝ)| ≤ Real.log (X : ℝ) ^ D) :
    (∑ j ∈ Finset.Ico 1 (majorArcLogSubdivisionCount X D ell),
      majorArcPhase ((j : ℝ) * (c : ℝ) /
        majorArcLogSubdivisionCount X D ell)) = -1 := by
  apply majorArcPhase_sum_Ico_one_eq_neg_one_of_abs_lt
  · have hcount := majorArcLogSubdivisionCount_pos
      (X := X) (D := D) (ell := ell) (by omega)
    have hfrequency :=
      majorArcFrequency_natAbs_lt_logSubdivisionCount hX hell hc
    omega
  · exact hc0
  · exact majorArcFrequency_natAbs_lt_logSubdivisionCount hX hell hc

end PrimesRestrictedDigits
