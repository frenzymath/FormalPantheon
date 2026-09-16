import PrimesRestrictedDigits.LatticeEstimates.Lemma14Three
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic form of repaired Lemma 14.3

The all-length theorem uses the exact polynomial cover. For positive decimal length, this
module converts it to the source's `(log X)^5` factor without making the false claim at `X=1`.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- An explicit absolute coefficient converting the five-dimensional scale
carrier to the fifth power of the natural logarithm. -/
noncomputable def latticeLemma14ThreeLogConstant : Real :=
  2 * (8 / Real.log 10) ^ 5

theorem latticeLemma14ThreeLogConstant_pos :
    0 < latticeLemma14ThreeLogConstant := by
  unfold latticeLemma14ThreeLogConstant
  have hlog : 0 < Real.log 10 := Real.log_pos (by norm_num)
  positivity

/-- For positive decimal length, the exact cover factor is an absolute
multiple of `(log(10^length))^5`. -/
theorem latticeLemma14Three_coverFactor_le_log
    {length : Nat} (hlength : 1 <= length) :
    ((2 * (length + 7) ^ 5 : Nat) : Real) <=
      latticeLemma14ThreeLogConstant *
        Real.log (((10 ^ length : Nat) : Real)) ^ 5 := by
  have hlengthBound : length + 7 <= 8 * length := by omega
  have hlengthBoundReal : ((length + 7 : Nat) : Real) <= 8 * (length : Real) := by
    exact_mod_cast hlengthBound
  have hlogPos : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hlog : Real.log (((10 ^ length : Nat) : Real)) =
      (length : Real) * Real.log 10 := by
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    exact Real.log_pow 10 length
  calc
    ((2 * (length + 7) ^ 5 : Nat) : Real) =
        2 * (((length + 7 : Nat) : Real) ^ 5) := by
      norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    _ <= 2 * (8 * (length : Real)) ^ 5 := by gcongr
    _ = latticeLemma14ThreeLogConstant *
        Real.log (((10 ^ length : Nat) : Real)) ^ 5 := by
      rw [hlog]
      unfold latticeLemma14ThreeLogConstant
      field_simp [hlogPos.ne']

/-- Positive-length logarithmic consequence of the all-length maximum form. -/
theorem latticeGeneratingExceptionalMass_le_logScaleMaximum
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hlength : 1 <= length)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) :
    latticeGeneratingExceptionalMass digit length N K delta <=
      latticeLemma14ThreeLogConstant *
        Real.log (((10 ^ length : Nat) : Real)) ^ 5 *
          latticeLemma14ThreeScaleMaximum digit length (N * K) := by
  have hraw := latticeGeneratingExceptionalMass_le_scaleMaximum
    digit N K delta hN hK hdelta hdeltaLower
  have hmaximumNonneg := latticeLemma14ThreeScaleMaximum_nonneg
    digit length (N * K)
  calc
    latticeGeneratingExceptionalMass digit length N K delta <=
        ((2 * (length + 7) ^ 5 : Nat) : Real) *
          latticeLemma14ThreeScaleMaximum digit length (N * K) := hraw
    _ <= (latticeLemma14ThreeLogConstant *
          Real.log (((10 ^ length : Nat) : Real)) ^ 5) *
        latticeLemma14ThreeScaleMaximum digit length (N * K) := by
      exact mul_le_mul_of_nonneg_right
        (latticeLemma14Three_coverFactor_le_log hlength) hmaximumNonneg
    _ = latticeLemma14ThreeLogConstant *
        Real.log (((10 ^ length : Nat) : Real)) ^ 5 *
          latticeLemma14ThreeScaleMaximum digit length (N * K) := rfl

end

end PrimesRestrictedDigits
