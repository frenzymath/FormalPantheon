import PrimesRestrictedDigits.GenericMinorArcs.DigitLevelSets
import PrimesRestrictedDigits.GenericMinorArcs.PrimeL2
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Direct complementary-frequency energy bound

This replaces the comparable-band decomposition in Lemma 12.2 of
`MAYNARD-PRD-PUBLISHED` by one finite Cauchy--Schwarz estimate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Below a positive digit-magnitude threshold, the complete digit moment and
prime Parseval energy directly control the normalized product sum. -/
theorem sum_smallNormalizedMagnitude_mul_weightedPhase_norm_div_le
    (a : Fin 10) (length : Nat) (w : Nat -> Complex)
    (frequencies : Finset (Fin (10 ^ length)))
    (T t M L : Real) (hT : 0 < T) (ht0 : 0 <= t) (ht2 : t <= 2)
    (hsmall : ∀ h ∈ frequencies,
      normalizedPaddedDigitFourierMagnitude a length h.val < T)
    (hmoment : (∑ h : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length h.val ^ t) <= M)
    (hL : 0 <= L)
    (hw : ∀ n ∈ Finset.range (10 ^ length), ‖w n‖ <= L) :
    (∑ h ∈ frequencies,
      normalizedPaddedDigitFourierMagnitude a length h.val *
        ‖majorArcWeightedPhaseSum (Finset.range (10 ^ length)) w
          (-((h.val : Real) / ((10 ^ length : Nat) : Real)))‖) /
        ((10 ^ length : Nat) : Real) <=
      T ^ (1 - t / 2) * Real.sqrt M * L := by
  let F : Fin (10 ^ length) -> Real := fun h =>
    normalizedPaddedDigitFourierMagnitude a length h.val
  let S : Fin (10 ^ length) -> Real := fun h =>
    ‖majorArcWeightedPhaseSum (Finset.range (10 ^ length)) w
      (-((h.val : Real) / ((10 ^ length : Nat) : Real)))‖
  change (∑ h ∈ frequencies, F h * S h) /
      ((10 ^ length : Nat) : Real) <=
    T ^ (1 - t / 2) * Real.sqrt M * L
  have hFnonneg (h : Fin (10 ^ length)) : 0 <= F h := by
    exact normalizedPaddedDigitFourierMagnitude_nonneg a length h.val
  have hdigitPoint : ∀ h ∈ frequencies,
      F h ^ 2 <= T ^ (2 - t) * F h ^ t := by
    intro h hh
    by_cases hzero : F h = 0
    · rw [hzero]
      by_cases htzero : t = 0
      · subst t
        rw [Real.rpow_zero]
        norm_num
        exact sq_nonneg T
      · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
        rw [Real.zero_rpow htpos.ne']
        norm_num
    · have hpos : 0 < F h :=
        lt_of_le_of_ne (hFnonneg h) (Ne.symm hzero)
      have hthreshold : F h ^ (2 - t) <= T ^ (2 - t) :=
        Real.rpow_le_rpow (hFnonneg h) (hsmall h hh).le
          (sub_nonneg.mpr ht2)
      calc
        F h ^ 2 = F h ^ (2 : Real) :=
          (Real.rpow_natCast (F h) 2).symm
        _ = F h ^ (t + (2 - t)) := by ring_nf
        _ = F h ^ t * F h ^ (2 - t) := Real.rpow_add hpos _ _
        _ <= F h ^ t * T ^ (2 - t) :=
          mul_le_mul_of_nonneg_left hthreshold
            (Real.rpow_nonneg (hFnonneg h) t)
        _ = T ^ (2 - t) * F h ^ t := mul_comm _ _
  have hdigitEnergy : (∑ h ∈ frequencies, F h ^ 2) <=
      T ^ (2 - t) * M := by
    calc
      (∑ h ∈ frequencies, F h ^ 2) <=
          ∑ h ∈ frequencies, T ^ (2 - t) * F h ^ t :=
        Finset.sum_le_sum hdigitPoint
      _ = T ^ (2 - t) * ∑ h ∈ frequencies, F h ^ t := by
        rw [Finset.mul_sum]
      _ <= T ^ (2 - t) * ∑ h : Fin (10 ^ length), F h ^ t := by
        apply mul_le_mul_of_nonneg_left _
          (Real.rpow_nonneg hT.le (2 - t))
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ frequencies)
        intro h hh hnot
        exact Real.rpow_nonneg (hFnonneg h) t
      _ <= T ^ (2 - t) * M :=
        mul_le_mul_of_nonneg_left hmoment
          (Real.rpow_nonneg hT.le (2 - t))
  have hmomentNonneg : 0 <=
      (∑ h : Fin (10 ^ length), F h ^ t) := by
    exact Finset.sum_nonneg fun h _ => Real.rpow_nonneg (hFnonneg h) t
  have hM : 0 <= M := hmomentNonneg.trans hmoment
  have hcoeffEnergy :
      (∑ n ∈ Finset.range (10 ^ length), ‖w n‖ ^ 2) <=
        (((10 ^ length : Nat) : Real) * L ^ 2) := by
    calc
      (∑ n ∈ Finset.range (10 ^ length), ‖w n‖ ^ 2) <=
          ∑ _n ∈ Finset.range (10 ^ length), L ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact (sq_le_sq₀ (norm_nonneg _) hL).2 (hw n hn)
      _ = ((10 ^ length : Nat) : Real) * L ^ 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hprimeEnergy : (∑ h ∈ frequencies, S h ^ 2) <=
      (((10 ^ length : Nat) : Real) * L) ^ 2 := by
    calc
      (∑ h ∈ frequencies, S h ^ 2) <=
          ∑ h : Fin (10 ^ length), S h ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ frequencies)
        intro h hh hnot
        positivity
      _ = ∑ h ∈ Finset.range (10 ^ length),
          ‖majorArcWeightedPhaseSum (Finset.range (10 ^ length)) w
            (-((h : Real) / ((10 ^ length : Nat) : Real)))‖ ^ 2 := by
        exact Fin.sum_univ_eq_sum_range (fun h =>
          ‖majorArcWeightedPhaseSum (Finset.range (10 ^ length)) w
            (-((h : Real) / ((10 ^ length : Nat) : Real)))‖ ^ 2)
          (10 ^ length)
      _ = ((10 ^ length : Nat) : Real) *
          ∑ n ∈ Finset.range (10 ^ length), ‖w n‖ ^ 2 :=
        sum_norm_sq_weightedPhase_grid (10 ^ length) (by positivity) w
      _ <= ((10 ^ length : Nat) : Real) *
          (((10 ^ length : Nat) : Real) * L ^ 2) :=
        mul_le_mul_of_nonneg_left hcoeffEnergy (by positivity)
      _ = (((10 ^ length : Nat) : Real) * L) ^ 2 := by ring
  have hcauchy := Real.sum_mul_le_sqrt_mul_sqrt frequencies F S
  have hproduct : (∑ h ∈ frequencies, F h * S h) <=
      Real.sqrt (T ^ (2 - t) * M) *
        Real.sqrt ((((10 ^ length : Nat) : Real) * L) ^ 2) := by
    exact hcauchy.trans (mul_le_mul
      (Real.sqrt_le_sqrt hdigitEnergy)
      (Real.sqrt_le_sqrt hprimeEnergy)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hdigitSqrt : Real.sqrt (T ^ (2 - t) * M) =
      T ^ (1 - t / 2) * Real.sqrt M := by
    calc
      Real.sqrt (T ^ (2 - t) * M) =
          Real.sqrt (T ^ (2 - t)) * Real.sqrt M :=
        Real.sqrt_mul (Real.rpow_nonneg hT.le (2 - t)) M
      _ = ((T ^ (2 - t)) ^ (1 / 2 : Real)) * Real.sqrt M := by
        rw [Real.sqrt_eq_rpow]
      _ = T ^ ((2 - t) * (1 / 2 : Real)) * Real.sqrt M := by
        rw [Real.rpow_mul hT.le]
      _ = T ^ (1 - t / 2) * Real.sqrt M := by ring_nf
  rw [hdigitSqrt, Real.sqrt_sq (by positivity)] at hproduct
  have hX : (0 : Real) < (10 ^ length : Nat) := by positivity
  apply (div_le_iff₀ hX).2
  calc
    (∑ h ∈ frequencies, F h * S h) <=
        T ^ (1 - t / 2) * Real.sqrt M *
          (((10 ^ length : Nat) : Real) * L) := hproduct
    _ = (T ^ (1 - t / 2) * Real.sqrt M * L) *
        ((10 ^ length : Nat) : Real) := by ring

/-- Exact simplification of the direct complementary expression at the source
threshold and moment exponents. -/
theorem genericDirectComplementary_eq_sourceDecay
    (X K L : Real) (hX : 0 < X) (hK : 0 <= K) :
    (X ^ (-(23 / 80 : Real))) ^
        (1 - (235 / 154 : Real) / 2) *
      Real.sqrt (K * X ^ (59 / 433 : Real)) * L =
    Real.sqrt K * L / X ^ (127 / 10669120 : Real) := by
  have hsqrt : Real.sqrt (K * X ^ (59 / 433 : Real)) =
      Real.sqrt K * X ^ (59 / 866 : Real) := by
    calc
      Real.sqrt (K * X ^ (59 / 433 : Real)) =
          Real.sqrt K * Real.sqrt (X ^ (59 / 433 : Real)) :=
        Real.sqrt_mul hK _
      _ = Real.sqrt K *
          ((X ^ (59 / 433 : Real)) ^ (1 / 2 : Real)) := by
        rw [Real.sqrt_eq_rpow (X ^ (59 / 433 : Real))]
      _ = Real.sqrt K *
          X ^ ((59 / 433 : Real) * (1 / 2 : Real)) := by
        rw [Real.rpow_mul hX.le]
      _ = Real.sqrt K * X ^ (59 / 866 : Real) := by norm_num
  have hthreshold :
      (X ^ (-(23 / 80 : Real))) ^
          (1 - (235 / 154 : Real) / 2) =
        X ^ (-(23 / 80 : Real) * (73 / 308 : Real)) := by
    calc
      (X ^ (-(23 / 80 : Real))) ^
          (1 - (235 / 154 : Real) / 2) =
          X ^ ((-(23 / 80 : Real)) *
            (1 - (235 / 154 : Real) / 2)) :=
        (Real.rpow_mul hX.le _ _).symm
      _ = X ^ (-(23 / 80 : Real) * (73 / 308 : Real)) := by
        congr 1
        norm_num
  have hcombine :
      X ^ (-(23 / 80 : Real) * (73 / 308 : Real)) *
          X ^ (59 / 866 : Real) =
        X ^ (-(127 / 10669120 : Real)) := by
    calc
      X ^ (-(23 / 80 : Real) * (73 / 308 : Real)) *
          X ^ (59 / 866 : Real) =
          X ^ (-(23 / 80 : Real) * (73 / 308 : Real) + 59 / 866) :=
        (Real.rpow_add hX _ _).symm
      _ = X ^ (-(127 / 10669120 : Real)) := by norm_num
  have hneg : X ^ (-(127 / 10669120 : Real)) =
      1 / X ^ (127 / 10669120 : Real) := by
    rw [Real.rpow_neg hX.le]
    rw [one_div]
  rw [hthreshold, hsqrt]
  rw [show X ^ (-(23 / 80 : Real) * (73 / 308 : Real)) *
      (Real.sqrt K * X ^ (59 / 866 : Real)) * L =
      Real.sqrt K * L *
        (X ^ (-(23 / 80 : Real) * (73 / 308 : Real)) *
          X ^ (59 / 866 : Real)) by ring]
  rw [hcombine, hneg]
  ring

/-- The direct complementary bound at the exact exceptional threshold and
digit-moment exponents of Lemma 12.2. -/
theorem sum_sourceSmallNormalizedMagnitude_mul_weightedPhase_norm_div_le
    (a : Fin 10) (length : Nat) (w : Nat -> Complex)
    (frequencies : Finset (Fin (10 ^ length))) (K L : Real)
    (hK : 0 <= K) (hL : 0 <= L)
    (hsmall : ∀ h ∈ frequencies,
      normalizedPaddedDigitFourierMagnitude a length h.val <
        (((10 ^ length : Nat) : Real) ^ (-(23 / 80 : Real))))
    (hmoment : (∑ h : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length h.val ^
        (235 / 154 : Real)) <=
      K * (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real)))
    (hw : ∀ n ∈ Finset.range (10 ^ length), ‖w n‖ <= L) :
    (∑ h ∈ frequencies,
      normalizedPaddedDigitFourierMagnitude a length h.val *
        ‖majorArcWeightedPhaseSum (Finset.range (10 ^ length)) w
          (-((h.val : Real) / ((10 ^ length : Nat) : Real)))‖) /
        ((10 ^ length : Nat) : Real) <=
      Real.sqrt K * L /
        (((10 ^ length : Nat) : Real) ^ (127 / 10669120 : Real)) := by
  calc
    (∑ h ∈ frequencies,
        normalizedPaddedDigitFourierMagnitude a length h.val *
          ‖majorArcWeightedPhaseSum (Finset.range (10 ^ length)) w
            (-((h.val : Real) / ((10 ^ length : Nat) : Real)))‖) /
          ((10 ^ length : Nat) : Real) <=
        ((((10 ^ length : Nat) : Real) ^ (-(23 / 80 : Real)))) ^
            (1 - (235 / 154 : Real) / 2) *
          Real.sqrt (K * (((10 ^ length : Nat) : Real) ^
            (59 / 433 : Real))) * L :=
      sum_smallNormalizedMagnitude_mul_weightedPhase_norm_div_le
        a length w frequencies
          (((10 ^ length : Nat) : Real) ^ (-(23 / 80 : Real)))
          (235 / 154 : Real)
          (K * (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real))) L
        (Real.rpow_pos_of_pos (by positivity) _) (by norm_num) (by norm_num)
        hsmall hmoment hL hw
    _ = Real.sqrt K * L /
        (((10 ^ length : Nat) : Real) ^ (127 / 10669120 : Real)) :=
      genericDirectComplementary_eq_sourceDecay
        ((10 ^ length : Nat) : Real) K L (by positivity) hK

end PrimesRestrictedDigits
