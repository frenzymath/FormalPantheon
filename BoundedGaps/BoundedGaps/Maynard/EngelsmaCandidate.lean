import BoundedGaps.Foundations.Admissible
import BoundedGaps.Maynard.ConcreteParameters
import BoundedGaps.Maynard.ConcreteWeights
import BoundedGaps.Maynard.LevelSelection
import BoundedGaps.Maynard.MaynardArithmeticBounds
import BoundedGaps.Maynard.MaynardLambdaSharpBound

/-!
# Transporting the variational candidate to the Engelsma tuple

Packet C is indexed by `Fin 105`, while the arithmetic sieve is indexed by the
subtype of the explicit Engelsma finset. This module records the checked finite
equivalence and specializes the conditional normalized-limit bridge to the
Packet C candidate and constants.
-/

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

noncomputable def engelsmaIndexEquiv :
    BoundedGaps.engelsmaTuple ≃ Fin 105 :=
  Fintype.equivFinOfCardEq (by
    simpa only [Fintype.card_coe] using BoundedGaps.engelsmaTuple_card)

noncomputable def engelsmaSmallKCandidate
    (t : BoundedGaps.engelsmaTuple → ℝ) : ℝ :=
  smallKCandidate (fun i => t (engelsmaIndexEquiv.symm i))

theorem engelsmaSmallKCandidate_norm_le
    (t : BoundedGaps.engelsmaTuple → ℝ) :
    ‖engelsmaSmallKCandidate t‖ ≤ smallKCandidateBound := by
  exact smallKCandidate_norm_le _

theorem engelsmaSmallKCandidate_abs_le
    (t : BoundedGaps.engelsmaTuple → ℝ) :
    |engelsmaSmallKCandidate t| ≤ smallKCandidateBound := by
  simpa only [Real.norm_eq_abs] using engelsmaSmallKCandidate_norm_le t

theorem abs_engelsmaMaynardCoefficient_le
    {alpha : ℝ} (N : ℕ) (d : BoundedGaps.engelsmaTuple → ℕ) :
    |maynardCoefficientFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
        engelsmaSmallKCandidate N d| ≤
      (divisorTupleProduct BoundedGaps.engelsmaTuple d : ℝ) *
        (maynardDivisorTupleBox BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N)).card * smallKCandidateBound := by
  simpa only [maynardCoefficientFamily] using
    (abs_maynardCoefficient_le_of_bound
      BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N) engelsmaSmallKCandidate d
      smallKCandidateBound smallKCandidateBound_nonneg
      engelsmaSmallKCandidate_abs_le)

set_option maxRecDepth 2000 in
theorem abs_engelsmaMaynardCoefficient_le_log_envelope
    {alpha : ℝ} (N : ℕ) {d : BoundedGaps.engelsmaTuple → ℕ}
    (hd : d ∈ maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N) :
    |maynardCoefficientFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
        engelsmaSmallKCandidate N d| ≤
      (engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
        (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
          (2 * Fintype.card BoundedGaps.engelsmaTuple) := by
  simpa only [maynardCoefficientFamily] using
    (abs_maynardCoefficient_le_log_envelope
      BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N) engelsmaSmallKCandidate d
      smallKCandidateBound smallKCandidateBound_nonneg
      engelsmaSmallKCandidate_abs_le (by simpa [maynardSupportFamily] using hd))

set_option maxRecDepth 2000 in
theorem abs_engelsmaMaynardCoefficient_le_sharp_log
    {alpha : ℝ} (N : ℕ) {d : BoundedGaps.engelsmaTuple → ℕ}
    (hd : d ∈ maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N) :
    |maynardCoefficientFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
        engelsmaSmallKCandidate N d| ≤
      smallKCandidateBound *
        (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
          (2 * (Fintype.card BoundedGaps.engelsmaTuple) ^ 2) := by
  have hH : BoundedGaps.engelsmaTuple.Nonempty := by
    apply Finset.card_pos.mp
    rw [BoundedGaps.engelsmaTuple_card]
    norm_num
  simpa only [maynardCoefficientFamily] using
    (abs_maynardCoefficient_le_sharp_log
      BoundedGaps.engelsmaTuple (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N) engelsmaSmallKCandidate d
      smallKCandidateBound smallKCandidateBound_nonneg
      engelsmaSmallKCandidate_abs_le hH
      (by simpa [maynardSupportFamily] using hd))

set_option maxRecDepth 2000 in
theorem abs_engelsmaMaynardCoefficient_le_on_support
    {alpha : ℝ} (N : ℕ) {d : BoundedGaps.engelsmaTuple → ℕ}
    (hd : d ∈ maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N) :
    |maynardCoefficientFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
        engelsmaSmallKCandidate N d| ≤
      (engelsmaMaynardRadius alpha N : ℝ) *
        (maynardDivisorTupleBox BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N)).card * smallKCandidateBound := by
  classical
  have hcoeff := abs_engelsmaMaynardCoefficient_le (alpha := alpha) N d
  have hsupport : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) d := by
    unfold maynardSupportFamily at hd
    unfold maynardDivisorTupleSupport at hd
    exact (Finset.mem_filter.mp hd).2
  have hprod : divisorTupleProduct BoundedGaps.engelsmaTuple d <
      engelsmaMaynardRadius alpha N := hsupport.1
  have hnonneg : 0 ≤
      (maynardDivisorTupleBox BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N)).card * smallKCandidateBound := by
    exact mul_nonneg (Nat.cast_nonneg _) smallKCandidateBound_nonneg
  calc
    |maynardCoefficientFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
        engelsmaSmallKCandidate N d| ≤
        (divisorTupleProduct BoundedGaps.engelsmaTuple d : ℝ) *
          (maynardDivisorTupleBox BoundedGaps.engelsmaTuple
            (engelsmaMaynardRadius alpha N)).card * smallKCandidateBound := hcoeff
    _ ≤ (engelsmaMaynardRadius alpha N : ℝ) *
          (maynardDivisorTupleBox BoundedGaps.engelsmaTuple
            (engelsmaMaynardRadius alpha N)).card * smallKCandidateBound := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hprod.le)
          (Nat.cast_nonneg _)) smallKCandidateBound_nonneg

theorem exists_engelsmaSmallKCandidate_alpha_of_bombieriVinogradov
    (hBV : bombieriVinogradov) :
    ∃ alpha : ℝ, 0 < alpha ∧
      0 < alpha * (∑ m : Fin 105, maynardJ 105 m smallKCandidate) -
        maynardI 105 smallKCandidate := by
  obtain ⟨theta, delta, _htheta0, _hthetaHalf, _hlevel,
      _hdelta0, hdeltaTheta, hmain⟩ :=
    exists_smallKCandidate_level_delta_with_positive_mainTerm hBV
  exact ⟨theta / 2 - delta, sub_pos.mpr hdeltaTheta, hmain⟩

theorem boundedGapsStatement_of_engelsmaSmallKCandidate_normalized_asymptotics
    {alpha : ℝ} (R W v : ℕ → ℕ) (scale : ℕ → ℝ)
    (hmargin :
      0 < alpha * (∑ m : Fin 105, maynardJ 105 m smallKCandidate) -
        maynardI 105 smallKCandidate)
    (hscale : ∀ᶠ N : ℕ in atTop, 0 < scale N)
    (hS1 : Tendsto
      (fun N : ℕ => sieveWeightSum N
        (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple R W v
          engelsmaSmallKCandidate N) / scale N)
      atTop (nhds (maynardI 105 smallKCandidate)))
    (hS2 : Tendsto
      (fun N : ℕ => primeWeightedSieveSum BoundedGaps.engelsmaTuple N
        (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple R W v
          engelsmaSmallKCandidate N) / scale N)
      atTop (nhds
        (alpha * (∑ m : Fin 105, maynardJ 105 m smallKCandidate)))) :
    BoundedGaps.boundedGapsStatement := by
  exact boundedGapsStatement_of_engelsma_maynardPreSieved_normalized_asymptotics
    (I := maynardI 105 smallKCandidate)
    (J := alpha * (∑ m : Fin 105, maynardJ 105 m smallKCandidate))
    R W v engelsmaSmallKCandidate scale hmargin hscale hS1 hS2

theorem boundedGapsStatement_of_engelsmaSmallKCandidate_concrete_normalized_asymptotics
    {alpha : ℝ} (halpha : 0 < alpha)
    (hmargin :
      0 < alpha * (∑ m : Fin 105, maynardJ 105 m smallKCandidate) -
        maynardI 105 smallKCandidate)
    (hS1 : Tendsto
      (fun N : ℕ => sieveWeightSum N
        (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
          engelsmaPreSieveResidue engelsmaSmallKCandidate N) /
            engelsmaMaynardScale alpha N)
      atTop (nhds (maynardI 105 smallKCandidate)))
    (hS2 : Tendsto
      (fun N : ℕ => primeWeightedSieveSum BoundedGaps.engelsmaTuple N
        (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
          engelsmaPreSieveResidue engelsmaSmallKCandidate N) /
            engelsmaMaynardScale alpha N)
      atTop (nhds
        (alpha * (∑ m : Fin 105, maynardJ 105 m smallKCandidate)))) :
    BoundedGaps.boundedGapsStatement := by
  exact boundedGapsStatement_of_engelsmaSmallKCandidate_normalized_asymptotics
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
    engelsmaPreSieveResidue (engelsmaMaynardScale alpha)
    hmargin (eventually_engelsmaMaynardScale_pos halpha) hS1 hS2

end BoundedGaps.Maynard
