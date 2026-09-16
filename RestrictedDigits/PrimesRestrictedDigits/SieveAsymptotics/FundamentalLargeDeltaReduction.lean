import PrimesRestrictedDigits.SieveAsymptotics.FundamentalSmallDeltaSplit
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaAmbient
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaMonotonicity
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaPreparation
import PrimesRestrictedDigits.SieveAsymptotics.RoughReciprocalBound
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalSieveParameters
import PrimesRestrictedDigits.Digits.LocalDensity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Large-delta reduction for the repaired Fundamental Lemma

This is the fixed-epsilon large branch of the repair.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

set_option maxHeartbeats 800000 in
theorem exists_correctedFundamentalLargeDeltaReduction
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1) :
    ∃ C : Real, 1 <= C ∧
      ∃ length0 : Nat, 1 <= length0 ∧
        ∀ length : Nat, length0 <= length ->
          ∀ (digit : Fin 10) (delta : Real),
            epsilon ^ (4 : Nat) < delta ->
            let X : Real := ((10 ^ length : Nat) : Real)
            5 <= X ^ delta ->
            (∑ d ∈ maynardStrictRoughCarrier
                (X ^ (50 / 77 - epsilon)) (X ^ delta),
              |((strictSiftedCarrier
                  (sieveDilation
                    (paddedRestrictedNumbers digit length) d.toPNat')
                  (X ^ delta)).card : Real) -
                (restrictedDigitDensity digit : Real) *
                  ((paddedRestrictedNumbers digit length).card : Real) / X *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta)).card : Real)|) <=
              C * ((paddedRestrictedNumbers digit length).card : Real) *
                Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X +
              C * ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log X ^ (100 : Nat) := by
  obtain ⟨Csmall, hCsmall, hSmall⟩ :=
    exists_correctedFundamentalSmallDeltaSplit
  obtain ⟨Kambient, hKambient, hAmbient⟩ :=
    exists_largeDeltaAmbientSiftedCount_upper epsilon hepsilon
      hepsilonSmall hepsilonRosser
  let delta0 : Real := epsilon ^ (4 : Nat)
  let alpha : Real := 50 / 77 - epsilon
  obtain ⟨hdelta0, _, _, _⟩ :
      0 < delta0 ∧ delta0 <= alpha ∧ delta0 <= epsilon ∧
        delta0 + alpha <= 1 := by
    simpa [delta0, alpha] using
      fundamentalLargeDelta_parameter_bounds epsilon hepsilon hepsilonSmall
  obtain ⟨lengthSmall, _, hlengthSmall⟩ :=
    hSmall epsilon hepsilon hepsilonSmall hepsilonRosser
  obtain ⟨lengthAmbient, _, hlengthAmbient⟩ :=
    hAmbient
  obtain ⟨lengthEndpoint, hlengthEndpoint⟩ :=
    exists_decimalEndpointThreshold delta0 hdelta0
  let Kcorr : Real :=
    (10 / 9 : Real) * Kambient *
      Real.exp (16 / Real.log 2) * (alpha / delta0) ^ (16 : Nat)
  let C : Real :=
    Csmall + Kcorr * Real.exp (delta0 ^ (-(2 / 3 : Real))) + 1
  have hKcorr : 0 <= Kcorr := by
    dsimp [Kcorr]
    positivity
  have hC : 1 <= C := by
    dsimp [C]
    have hexp : 0 <= Real.exp (delta0 ^ (-(2 / 3 : Real))) := by positivity
    nlinarith [hCsmall, hKcorr]
  refine ⟨C, hC, ?_⟩
  let length0 : Nat :=
    max 1 (max lengthSmall (max lengthAmbient lengthEndpoint))
  refine ⟨length0, ?_, ?_⟩
  · dsimp [length0]
    omega
  · intro length hlength digit delta hdeltaLarge
    dsimp
    intro hcutoff
    let X : Real := ((10 ^ length : Nat) : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let D : Finset Nat :=
      maynardStrictRoughCarrier (X ^ alpha) (X ^ delta)
    let D0 : Finset Nat :=
      maynardStrictRoughCarrier (X ^ alpha) (X ^ delta0)
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * (A.card : Real) / X
    have hlengthSmall' : lengthSmall <= length := by
      have hrest : max lengthSmall (max lengthAmbient lengthEndpoint) <= length :=
        (Nat.le_max_right 1 _).trans hlength
      exact (Nat.le_max_left _ _).trans hrest
    have hlengthAmbient' : lengthAmbient <= length := by
      have hrest : max lengthSmall (max lengthAmbient lengthEndpoint) <= length :=
        (Nat.le_max_right 1 _).trans hlength
      have hrest' : max lengthAmbient lengthEndpoint <=
          max lengthSmall (max lengthAmbient lengthEndpoint) :=
        Nat.le_max_right _ _
      exact (Nat.le_max_left _ _).trans (hrest'.trans hrest)
    have hlengthEndpoint' : lengthEndpoint <= length := by
      have hrest : max lengthSmall (max lengthAmbient lengthEndpoint) <= length :=
        (Nat.le_max_right 1 _).trans hlength
      have hrest' : max lengthAmbient lengthEndpoint <=
          max lengthSmall (max lengthAmbient lengthEndpoint) :=
        Nat.le_max_right _ _
      exact (Nat.le_max_right _ _).trans (hrest'.trans hrest)
    have hendpoint := hlengthEndpoint length hlengthEndpoint'
    have hlengthOne : 1 <= length := hendpoint.1
    have hY0 : 5 <= X ^ delta0 := by
      simpa [X] using hendpoint.2.1
    have hlogXOne : 1 <= Real.log X := by
      simpa [X] using hendpoint.2.2
    have hX : 1 < X := by
      dsimp [X]
      exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
        (by norm_num : 1 < (10 : Nat))
    have hXpos : 0 < X := by linarith
    have hXne : X ≠ 0 := ne_of_gt hXpos
    have hlogX : 0 < Real.log X := Real.log_pos hX
    have hdelta0Small : delta0 <= epsilon ^ (4 : Nat) := by rfl
    have hsmallRaw := hlengthSmall length hlengthSmall' digit delta0
      hdelta0 hdelta0Small
    dsimp at hsmallRaw
    have hsmallRaw := hsmallRaw (by simpa [X] using hY0)
    have hDensity : 0 <= (restrictedDigitDensity digit : Real) ∧
        (restrictedDigitDensity digit : Real) <= 10 / 9 := by
      rw [restrictedDigitDensity_eq]
      split_ifs <;> norm_num
    have hlambda : 0 <= lambda := by
      dsimp [lambda]
      exact div_nonneg (mul_nonneg hDensity.1 (by positivity)) hXpos.le
    have hDsubset : D ⊆ D0 := by
      dsimp [D, D0, alpha]
      exact largeDelta_outer_carrier_subset hX hdelta0
        (le_of_lt hdeltaLarge)
    have hpointwise :
        ∀ d ∈ D,
          |((strictSiftedCarrier
              (sieveDilation A d.toPNat') (X ^ delta)).card : Real) -
              lambda *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta)).card : Real)| <=
            |((strictSiftedCarrier
                (sieveDilation A d.toPNat') (X ^ delta0)).card : Real) -
              lambda *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta0)).card : Real)| +
              lambda *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta0)).card : Real) := by
      intro d hd
      have hD0d : d ∈ D0 := hDsubset hd
      have hsourceNonneg :
          0 <= ((strictSiftedCarrier
            (sieveDilation A d.toPNat') (X ^ delta0)).card : Real) := by
        positivity
      have hsourceDeltaNonneg :
          0 <= ((strictSiftedCarrier
            (sieveDilation A d.toPNat') (X ^ delta)).card : Real) := by
        positivity
      have hambientNonneg :
          0 <= ((strictSiftedCarrier
            (sieveDilation (maynardAmbientCarrier X) d.toPNat')
            (X ^ delta0)).card : Real) := by
        positivity
      have hambientDeltaNonneg :
          0 <= ((strictSiftedCarrier
            (sieveDilation (maynardAmbientCarrier X) d.toPNat')
            (X ^ delta)).card : Real) := by
        positivity
      have hsourceLe := card_strictSiftedCarrier_sieveDilation_threshold_le
        A d.toPNat' (show X ^ delta0 ≤ X ^ delta by
          exact Real.rpow_le_rpow_of_exponent_le hX.le
            (le_of_lt hdeltaLarge))
      have hambientLe := card_strictSiftedCarrier_sieveDilation_threshold_le
        (maynardAmbientCarrier X) d.toPNat'
        (show X ^ delta0 ≤ X ^ delta by
          exact Real.rpow_le_rpow_of_exponent_le hX.le
            (le_of_lt hdeltaLarge))
      exact largeDelta_pointwise_abs_le hsourceNonneg
        hsourceDeltaNonneg hambientNonneg hambientDeltaNonneg
        hsourceLe hambientLe hlambda
    have hpointSum :
        (∑ d ∈ D,
          |((strictSiftedCarrier
              (sieveDilation A d.toPNat') (X ^ delta)).card : Real) -
              lambda *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta)).card : Real)|) <=
          (∑ d ∈ D,
            |((strictSiftedCarrier
                (sieveDilation A d.toPNat') (X ^ delta0)).card : Real) -
              lambda *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta0)).card : Real)|) +
            ∑ d ∈ D,
              lambda *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta0)).card : Real) := by
      calc
        _ <= ∑ d ∈ D,
            (|((strictSiftedCarrier
                (sieveDilation A d.toPNat') (X ^ delta0)).card : Real) -
              lambda *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta0)).card : Real)| +
              lambda *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta0)).card : Real)) := by
          apply Finset.sum_le_sum
          intro d hd
          exact hpointwise d hd
        _ = _ := by rw [Finset.sum_add_distrib]
    have hendpointBound :
        (∑ d ∈ D0,
          |((strictSiftedCarrier
              (sieveDilation A d.toPNat') (X ^ delta0)).card : Real) -
            lambda *
              ((strictSiftedCarrier
                (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                (X ^ delta0)).card : Real)|) <=
          Csmall * (A.card : Real) *
              Real.exp (-(delta0 ^ (-(2 / 3 : Real)))) / Real.log X +
            Csmall * (A.card : Real) / Real.log X ^ (100 : Nat) := by
      simpa [D0, A, lambda, X, delta0, alpha,
        div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hsmallRaw
    have hendpointRestriction :
        (∑ d ∈ D,
          |((strictSiftedCarrier
              (sieveDilation A d.toPNat') (X ^ delta0)).card : Real) -
            lambda *
              ((strictSiftedCarrier
                (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                (X ^ delta0)).card : Real)|) <=
          (∑ d ∈ D0,
            |((strictSiftedCarrier
                (sieveDilation A d.toPNat') (X ^ delta0)).card : Real) -
              lambda *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta0)).card : Real)|) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hDsubset
      intro d hdD0 hdD
      exact abs_nonneg _
    have hD0Data :
        ∀ d ∈ D0, 1 <= d ∧ (d : Real) < X ^ alpha := by
      intro d hd
      rcases mem_maynardStrictRoughCarrier.mp (by simpa [D0] using hd) with
        ⟨hdOne, hdCut, _⟩
      exact ⟨hdOne, hdCut⟩
    have hcorrectionRestriction :
        (∑ d ∈ D,
          lambda *
            ((strictSiftedCarrier
              (sieveDilation (maynardAmbientCarrier X) d.toPNat')
              (X ^ delta0)).card : Real)) <=
          ∑ d ∈ D0,
            lambda *
              ((strictSiftedCarrier
                (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                (X ^ delta0)).card : Real) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hDsubset
      intro d hdD0 hdD
      positivity
    obtain ⟨_, _, _, _, _, _, _, hdataDeltaAlpha⟩ :=
      fundamentalSieve_smallParameter_data hX hepsilon
        hepsilonSmall hepsilonRosser hdelta0 hdelta0Small hY0
    have hrecip := sum_inv_maynardStrictRoughCarrier_rpow_le
      (X := X) (delta := delta0) (alpha := alpha) hX hdelta0
      hdataDeltaAlpha (by linarith [hY0])
    have hrecipD0 :
        (∑ d ∈ D0, (d : Real)⁻¹) <=
          Real.exp (16 / Real.log 2) * (alpha / delta0) ^ (16 : Nat) := by
      simpa [D0, alpha] using hrecip
    have hambientPointwise :
        ∀ d ∈ D0,
          lambda *
              ((strictSiftedCarrier
                (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                (X ^ delta0)).card : Real) <=
            lambda * Kambient * X /
              ((d : Real) * Real.log X) := by
      intro d hd
      have hdData := hD0Data d hd
      have hbound := hlengthAmbient length hlengthAmbient' d hdData.1
        hdData.2
      have hbound' :
          ((strictSiftedCarrier
            (sieveDilation (maynardAmbientCarrier X) d.toPNat')
            (X ^ delta0)).card : Real) <=
            Kambient * X / ((d : Real) * Real.log X) := by
        simpa [X, delta0] using hbound
      calc
        _ <= lambda * (Kambient * X /
            ((d : Real) * Real.log X)) :=
          mul_le_mul_of_nonneg_left hbound' hlambda
        _ = _ := by ring
    have hcorrectionBound :
        (∑ d ∈ D0,
          lambda *
            ((strictSiftedCarrier
              (sieveDilation (maynardAmbientCarrier X) d.toPNat')
              (X ^ delta0)).card : Real)) <=
          Kcorr * (A.card : Real) / Real.log X := by
      calc
        _ <= ∑ d ∈ D0,
            lambda * Kambient * X /
              ((d : Real) * Real.log X) := by
          apply Finset.sum_le_sum
          intro d hd
          exact hambientPointwise d hd
        _ = lambda * Kambient * X / Real.log X *
              (∑ d ∈ D0, (d : Real)⁻¹) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          ring
        _ <= lambda * Kambient * X / Real.log X *
              (Real.exp (16 / Real.log 2) * (alpha / delta0) ^ (16 : Nat)) := by
          gcongr
        _ <= Kcorr * (A.card : Real) / Real.log X := by
          dsimp [Kcorr, lambda]
          have hA : 0 <= (A.card : Real) := by positivity
          have hk : (restrictedDigitDensity digit : Real) <= 10 / 9 :=
            hDensity.2
          have hscale :
              (restrictedDigitDensity digit : Real) * (A.card : Real) / X *
                  Kambient * X / Real.log X *
                    (Real.exp (16 / Real.log 2) * (alpha / delta0) ^ (16 : Nat)) <=
                (10 / 9 : Real) * Kambient *
                  Real.exp (16 / Real.log 2) * (alpha / delta0) ^ (16 : Nat) *
                    (A.card : Real) / Real.log X := by
            field_simp [hXne, hlogX.ne']
            have hfactor : 0 <= (A.card : Real) * alpha ^ (16 : Nat) := by
              positivity
            have hineq := mul_le_mul_of_nonneg_right hk hfactor
            nlinarith
          exact hscale
    have hsumBound :
        (∑ d ∈ D,
          |((strictSiftedCarrier
              (sieveDilation A d.toPNat') (X ^ delta)).card : Real) -
              lambda *
                ((strictSiftedCarrier
                  (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                  (X ^ delta)).card : Real)|) <=
          Csmall * (A.card : Real) *
              Real.exp (-(delta0 ^ (-(2 / 3 : Real)))) / Real.log X +
            Csmall * (A.card : Real) / Real.log X ^ (100 : Nat) +
            Kcorr * (A.card : Real) / Real.log X := by
      calc
        _ <=
            (∑ d ∈ D,
              |((strictSiftedCarrier
                  (sieveDilation A d.toPNat') (X ^ delta0)).card : Real) -
                lambda *
                  ((strictSiftedCarrier
                    (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                    (X ^ delta0)).card : Real)|) +
              ∑ d ∈ D,
                lambda *
                  ((strictSiftedCarrier
                    (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                    (X ^ delta0)).card : Real) := hpointSum
        _ <=
            (Csmall * (A.card : Real) *
                Real.exp (-(delta0 ^ (-(2 / 3 : Real)))) / Real.log X +
              Csmall * (A.card : Real) / Real.log X ^ (100 : Nat)) +
              Kcorr * (A.card : Real) / Real.log X := by
          have hfirst := add_le_add_right hendpointRestriction
            (∑ d ∈ D, lambda *
              ((strictSiftedCarrier
                (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                (X ^ delta0)).card : Real))
          have hsecond := add_le_add hendpointBound
            (hcorrectionRestriction.trans hcorrectionBound)
          calc
            _ <=
                (∑ d ∈ D0,
                  |((strictSiftedCarrier
                      (sieveDilation A d.toPNat') (X ^ delta0)).card : Real) -
                    lambda *
                      ((strictSiftedCarrier
                        (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                        (X ^ delta0)).card : Real)|) +
                  ∑ d ∈ D,
                    lambda *
                      ((strictSiftedCarrier
                        (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                        (X ^ delta0)).card : Real) := by
              simpa [add_comm, add_left_comm, add_assoc] using hfirst
            _ <=
                (Csmall * (A.card : Real) *
                    Real.exp (-(delta0 ^ (-(2 / 3 : Real)))) / Real.log X +
                  Csmall * (A.card : Real) / Real.log X ^ (100 : Nat)) +
                  Kcorr * (A.card : Real) / Real.log X := by
              simpa [add_comm, add_left_comm, add_assoc] using hsecond
        _ = _ := by ring
    have hcoef :
        Csmall + Kcorr * Real.exp (delta0 ^ (-(2 / 3 : Real))) <= C := by
      change Csmall + Kcorr * Real.exp (delta0 ^ (-(2 / 3 : Real))) <=
        Csmall + Kcorr * Real.exp (delta0 ^ (-(2 / 3 : Real))) + 1
      linarith
    have hCsmall_le : Csmall <= C := by
      change Csmall <= Csmall + Kcorr *
        Real.exp (delta0 ^ (-(2 / 3 : Real))) + 1
      have hprod : 0 <= Kcorr * Real.exp (delta0 ^ (-(2 / 3 : Real))) :=
        mul_nonneg hKcorr (Real.exp_pos _).le
      linarith [hprod]
    have hCsmallNonneg : 0 <= Csmall := by linarith
    calc
      _ <= Csmall * (A.card : Real) *
            Real.exp (-(delta0 ^ (-(2 / 3 : Real)))) / Real.log X +
          Csmall * (A.card : Real) / Real.log X ^ (100 : Nat) +
          Kcorr * (A.card : Real) / Real.log X := hsumBound
      _ <= C * (A.card : Real) *
            Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X +
          C * (A.card : Real) / Real.log X ^ (100 : Nat) :=
        largeDelta_error_terms_absorbed X delta0 delta Csmall Kcorr C
          (A.card : Real) hX hdelta0 (le_of_lt hdeltaLarge) (by positivity)
          hCsmallNonneg hKcorr hcoef hCsmall_le

end

end PrimesRestrictedDigits
