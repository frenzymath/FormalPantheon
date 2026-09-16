import PrimesRestrictedDigits.Fourier.HybridSparseBound
import PrimesRestrictedDigits.Fourier.HybridDenseBound

/-!
# Unified generic hybrid estimate

The sparse and dense branches use the same explicit coefficient and are
combined here before any source-specific carrier is introduced.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

theorem sum_alignedGridSum_hybridEstimate
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (digit : Fin 10) (length : Nat) (base : ι -> Real)
    {L E : Real} (hL : 1 <= L) (hE : 1 <= E)
    (hbase : ∀ i ∈ s, base i ∈ Set.Icc (0 : Real) 1)
    (hseparated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      1 / L <= dist ((base i : Real) : UnitAddCircle)
        ((base j : Real) : UnitAddCircle)) :
    (∑ i ∈ s, alignedGridSum digit length E (base i)) <=
      hybridSamplingConstant *
        ((L * E) ^ largeSieveAlpha +
          L * E * (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := by
  classical
  let Y : Real := ((10 ^ length : Nat) : Real)
  have hY : 0 < Y := by
    dsimp [Y]
    positivity
  by_cases hlow : 10 * L * E < Y
  · have hs := sum_alignedGridSum_sparse_le s digit length base hL hE
      hbase hseparated (by simpa [Y] using hlow)
    calc
      (∑ i ∈ s, alignedGridSum digit length E (base i)) <=
          hybridSamplingConstant * (L * E) ^ largeSieveAlpha := hs
      _ <= hybridSamplingConstant *
          ((L * E) ^ largeSieveAlpha + L * E * Y ^ (-largeSieveSigma)) := by
        have hconstant : 0 <= hybridSamplingConstant := by
          unfold hybridSamplingConstant
          norm_num
        have htail : 0 <= L * E * Y ^ (-largeSieveSigma) :=
          mul_nonneg (mul_nonneg (by positivity) (by positivity))
            (Real.rpow_nonneg hY.le _)
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right htail) hconstant
  · have hhigh : Y <= 10 * L * E := le_of_not_gt hlow
    have hd := sum_alignedGridSum_dense_le s digit length base hL hE
      hbase hseparated (by simpa [Y] using hhigh)
    calc
      (∑ i ∈ s, alignedGridSum digit length E (base i)) <=
          4400000 * L * E * Y ^ (-largeSieveSigma) := hd
      _ <= hybridSamplingConstant *
          ((L * E) ^ largeSieveAlpha + L * E * Y ^ (-largeSieveSigma)) := by
        have hnonneg : 0 <= L * E * Y ^ (-largeSieveSigma) := by
          exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
            (Real.rpow_nonneg hY.le _)
        unfold hybridSamplingConstant
        nlinarith [Real.rpow_nonneg (show 0 <= L * E by positivity)
          largeSieveAlpha]

end

end PrimesRestrictedDigits
