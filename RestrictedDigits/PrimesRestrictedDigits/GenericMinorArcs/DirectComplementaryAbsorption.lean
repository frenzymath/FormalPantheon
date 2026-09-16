import PrimesRestrictedDigits.GenericMinorArcs.DirectComplementaryRegion
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic absorption for direct complementary decay

This spends half of the exact power-saving margin in Lemma 12.2 of
`MAYNARD-PRD-PUBLISHED` to absorb the fixed eta-dependent factorial and
logarithm coefficient.
-/

open Filter Asymptotics

namespace PrimesRestrictedDigits

/-- The explicit eta-region coefficient is eventually absorbed by half of the
exact complementary power-saving margin. -/
theorem eventually_sourceRegionCoefficient_decay
    (K eta : Real) (_hK : 0 <= K) (_heta : 0 < eta) :
    ∀ᶠ X : Real in atTop,
      Real.sqrt K *
          ((Nat.factorial (Nat.ceil (2 / eta)) : Real) *
            Real.log X ^ Nat.ceil (2 / eta)) /
          X ^ (127 / 10669120 : Real) <=
        1 / X ^ (127 / 21338240 : Real) := by
  let R := Nat.ceil (2 / eta)
  let C := Real.sqrt K * (Nat.factorial R : Real)
  have hC : 0 <= C := by
    dsimp only [C]
    positivity
  have hbound :=
    ((isLittleO_log_rpow_rpow_atTop (R : Real)
      (by norm_num : (0 : Real) < 127 / 21338240)).const_mul_left C).bound
        zero_lt_one
  filter_upwards [hbound, eventually_gt_atTop (1 : Real)] with X hlogBound hX
  have hXPos : 0 < X := zero_lt_one.trans hX
  have hleft : 0 <= C * Real.log X ^ R :=
    mul_nonneg hC (pow_nonneg (Real.log_pos hX).le R)
  have hright : 0 <= X ^ (127 / 21338240 : Real) :=
    (Real.rpow_pos_of_pos hXPos _).le
  have hgrowth :
      C * Real.log X ^ R <= X ^ (127 / 21338240 : Real) := by
    simpa only [Real.rpow_natCast, Real.norm_of_nonneg hleft,
      Real.norm_of_nonneg hright, one_mul] using hlogBound
  have hdenom : 0 <= X ^ (127 / 10669120 : Real) :=
    (Real.rpow_pos_of_pos hXPos _).le
  calc
    Real.sqrt K *
          ((Nat.factorial (Nat.ceil (2 / eta)) : Real) *
            Real.log X ^ Nat.ceil (2 / eta)) /
          X ^ (127 / 10669120 : Real) =
        C * Real.log X ^ R / X ^ (127 / 10669120 : Real) := by
      simp only [C, R]
      ring
    _ <= X ^ (127 / 21338240 : Real) /
        X ^ (127 / 10669120 : Real) :=
      div_le_div_of_nonneg_right hgrowth hdenom
    _ = X ^ ((127 / 21338240 : Real) - 127 / 10669120) :=
      (Real.rpow_sub hXPos _ _).symm
    _ = X ^ (-(127 / 21338240 : Real)) := by norm_num
    _ = 1 / X ^ (127 / 21338240 : Real) := by
      rw [Real.rpow_neg hXPos.le]
      exact (one_div _).symm

/-- Beyond one decimal-length threshold, coefficient absorption and the
`X >= 4` endpoint needed by the direct region theorem hold simultaneously. -/
theorem exists_sourceRegionCoefficient_powerTenDecayThreshold
    (K eta : Real) (hK : 0 <= K) (heta : 0 < eta) :
    ∃ length0 : Nat, ∀ length : Nat, length0 <= length ->
      4 <= 10 ^ length ∧
        Real.sqrt K *
            ((Nat.factorial (Nat.ceil (2 / eta)) : Real) *
              Real.log (((10 ^ length : Nat) : Real)) ^
                Nat.ceil (2 / eta)) /
            (((10 ^ length : Nat) : Real) ^
              (127 / 10669120 : Real)) <=
          1 / (((10 ^ length : Nat) : Real) ^
            (127 / 21338240 : Real)) := by
  have hreal := eventually_sourceRegionCoefficient_decay K eta hK heta
  have hpow :
      Tendsto (fun length : Nat => (10 : Real) ^ length) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hpull := hpow.eventually hreal
  have hpull' : ∀ᶠ length : Nat in atTop,
      Real.sqrt K *
            ((Nat.factorial (Nat.ceil (2 / eta)) : Real) *
              Real.log (((10 ^ length : Nat) : Real)) ^
                Nat.ceil (2 / eta)) /
            (((10 ^ length : Nat) : Real) ^
              (127 / 10669120 : Real)) <=
          1 / (((10 ^ length : Nat) : Real) ^
            (127 / 21338240 : Real)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpull
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (1 : Nat), hpull'] with length hlength hdecay
  refine ⟨?_, hdecay⟩
  calc
    4 <= 10 := by norm_num
    _ = 10 ^ 1 := by norm_num
    _ <= 10 ^ length := Nat.pow_le_pow_right (by norm_num) hlength

/-- The global strict-complement region estimate has a uniform explicit decay
beyond a threshold depending only on the moment constant and `eta`. -/
theorem
    exists_sourceSmallNormalizedMagnitude_mul_normalizedLogRegion_decayThreshold
    (K eta : Real) (hK : 0 <= K) (heta : 0 < eta) :
    ∃ length0 : Nat, ∀ length : Nat, length0 <= length ->
      ∀ (a : Fin 10) (ell : Nat), (ell : Real) <= 2 / eta ->
      ∀ (region : Set (Fin ell -> Real))
        (frequencies : Finset (Fin (10 ^ length))),
        (∀ h ∈ frequencies,
          normalizedPaddedDigitFourierMagnitude a length h.val <
            (((10 ^ length : Nat) : Real) ^ (-(23 / 80 : Real)))) ->
        (∑ h : Fin (10 ^ length),
          normalizedPaddedDigitFourierMagnitude a length h.val ^
            (235 / 154 : Real)) <=
          K * (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real)) ->
        (∑ h ∈ frequencies,
          normalizedPaddedDigitFourierMagnitude a length h.val *
            ‖majorArcWeightedPhaseSum (Finset.range (10 ^ length))
              (fun n => (normalizedLogRegionWeightAtProduct
                (10 ^ length) region n : Complex))
              (-((h.val : Real) /
                ((10 ^ length : Nat) : Real)))‖) /
            ((10 ^ length : Nat) : Real) <=
          1 / (((10 ^ length : Nat) : Real) ^
            (127 / 21338240 : Real)) := by
  obtain ⟨length0, hlength0⟩ :=
    exists_sourceRegionCoefficient_powerTenDecayThreshold K eta hK heta
  refine ⟨length0, ?_⟩
  intro length hlength a ell hell region frequencies hsmall hmoment
  obtain ⟨hX, hdecay⟩ := hlength0 length hlength
  exact (sum_sourceSmallNormalizedMagnitude_mul_normalizedLogRegion_norm_div_le
    a length ell hX heta hell region frequencies K hK hsmall hmoment).trans
      hdecay

end PrimesRestrictedDigits
