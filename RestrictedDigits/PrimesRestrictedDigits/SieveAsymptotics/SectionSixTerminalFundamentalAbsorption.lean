import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalFundamentalContribution
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLemma
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Eventual Fundamental absorption for Section 6 `T` terminals

The multiplicity is retained explicitly. The auxiliary parameter is selected after the
requested budget and before the eventual decimal length.
-/

open Filter
open scoped BigOperators Topology

namespace PrimesRestrictedDigits

noncomputable section

/-- The exact strict-rough residual sum used by the corrected Fundamental
Lemma.  This name exposes the finite analytic aggregate to later direct-base
and common-budget arguments without changing its cardinality formula. -/
noncomputable def sectionSixFundamentalResidual
    (digit : Fin 10) (epsilon delta : Real) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ D ∈ maynardStrictRoughCarrier (X ^ (50 / 77 - epsilon)) (X ^ delta),
    abs (((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) D.toPNat')
        (X ^ delta)).card : Real) -
      (restrictedDigitDensity digit : Real) *
        ((paddedRestrictedNumbers digit length).card : Real) / X *
        ((strictSiftedCarrier
          (sieveDilation (maynardAmbientCarrier X) D.toPNat')
          (X ^ delta)).card : Real))

private theorem exists_sectionSixTerminalTFundamentalRapidDelta
    (ell : Nat) (C deltaUpper deltaGap rho : Real)
    (hdeltaUpper : 0 < deltaUpper) (hdeltaGap : 0 < deltaGap)
    (hrho : 0 < rho) :
    ∃ delta : Real, 0 < delta ∧ delta < deltaUpper ∧ delta < deltaGap ∧
      2 * ((5 * (Nat.ceil (1 / delta)) ^ ell : Nat) : Real) * C *
          Real.exp (-(delta ^ (-(2 / 3 : Real)))) ≤ rho := by
  have hreal :
      Tendsto (fun x : Real => x ^ ell *
        Real.exp (-(x ^ (2 / 3 : Real)))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      ((3 / 2 : Real) * (ell : Real)) 1 one_pos).comp
        (tendsto_rpow_atTop (by norm_num : (0 : Real) < 2 / 3))
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : Real)] with x hx
    change (x ^ (2 / 3 : Real)) ^ ((3 / 2 : Real) * (ell : Real)) *
      Real.exp (-1 * (x ^ (2 / 3 : Real))) =
        x ^ ell * Real.exp (-(x ^ (2 / 3 : Real)))
    congr 1
    · rw [← Real.rpow_mul hx]
      rw [show (2 / 3 : Real) * ((3 / 2 : Real) * (ell : Real)) =
          (ell : Real) by ring]
      exact Real.rpow_natCast x ell
    · congr 1
      ring
  have hscaled :
      Tendsto (fun x : Real =>
        ((10 : Real) * C) * (x ^ ell *
          Real.exp (-(x ^ (2 / 3 : Real))))) atTop (𝓝 0) := by
    simpa using hreal.const_mul ((10 : Real) * C)
  have hnat : Tendsto (fun n : Nat =>
      (2 * ((5 * n ^ ell : Nat) : Real) * C *
        Real.exp (-((n : Real) ^ (2 / 3 : Real))))) atTop (𝓝 0) := by
    have hcomp := hscaled.comp tendsto_natCast_atTop_atTop
    convert hcomp using 1
    funext n
    norm_num [Nat.cast_pow]
    ring
  have hdecay : ∀ᶠ n : Nat in atTop,
      2 * ((5 * n ^ ell : Nat) : Real) * C *
        Real.exp (-((n : Real) ^ (2 / 3 : Real))) < rho :=
    hnat.eventually (Iio_mem_nhds hrho)
  have hinv : Tendsto (fun n : Nat => ((n : Real)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hdeltaSmall : ∀ᶠ n : Nat in atTop, ((n : Real)⁻¹) < deltaUpper :=
    hinv.eventually (Iio_mem_nhds hdeltaUpper)
  have hdeltaGapSmall : ∀ᶠ n : Nat in atTop, ((n : Real)⁻¹) < deltaGap :=
    hinv.eventually (Iio_mem_nhds hdeltaGap)
  have hall : ∀ᶠ n : Nat in atTop,
      1 ≤ n ∧ ((n : Real)⁻¹) < deltaUpper ∧
        ((n : Real)⁻¹) < deltaGap ∧
          2 * ((5 * n ^ ell : Nat) : Real) * C *
            Real.exp (-((n : Real) ^ (2 / 3 : Real))) < rho := by
    filter_upwards [eventually_ge_atTop (1 : Nat), hdeltaSmall,
      hdeltaGapSmall, hdecay] with n hn hupper hgap hbound
    exact ⟨hn, hupper, hgap, hbound⟩
  rcases hall.exists with ⟨n, hn, hupper, hgap, hbound⟩
  have hn0 : n ≠ 0 := by omega
  refine ⟨(n : Real)⁻¹, by positivity, hupper, hgap, ?_⟩
  rw [one_div, inv_inv, Nat.ceil_natCast]
  rw [Real.rpow_neg_eq_inv_rpow, inv_inv]
  exact hbound.le

private theorem exists_sectionSixTerminalTFundamentalLogThreshold
    (ell : Nat) (C rho delta : Real) (hrho : 0 < rho)
    (hdelta : 0 < delta) :
    ∃ length0 : Nat, ∀ length : Nat, length0 ≤ length →
      1 ≤ Real.log ((10 ^ length : Nat) : Real) ∧
        2 * ((5 * (Nat.ceil (1 / delta)) ^ ell : Nat) : Real) * C ≤
          rho * Real.log ((10 ^ length : Nat) : Real) ^ (99 : Nat) := by
  let K : Real := ((5 * (Nat.ceil (1 / delta)) ^ ell : Nat) : Real)
  have hK : 0 ≤ K := by positivity
  have hlogPowTendsto :
      Tendsto (fun x : Real => Real.log x ^ (99 : Nat)) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (99 : Nat) ≠ 0)).comp
      Real.tendsto_log_atTop
  have hlogScalar : ∀ᶠ x : Real in atTop,
      2 * K * C ≤ rho * Real.log x ^ (99 : Nat) := by
    have hlarge := hlogPowTendsto.eventually_ge_atTop
      ((2 * K * C) / rho)
    filter_upwards [hlarge] with x hx
    have hx' : 2 * K * C ≤ Real.log x ^ (99 : Nat) * rho :=
      (div_le_iff₀ hrho).mp hx
    simpa only [mul_comm] using hx'
  have hlog : ∀ᶠ x : Real in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : Real)
  have hscale : Tendsto
      (fun length : Nat => ((10 ^ length : Nat) : Real)) atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  have hpull := hscale.eventually (hlog.and hlogScalar)
  apply eventually_atTop.mp
  filter_upwards [hpull] with length hlength
  simpa only [K] using hlength

theorem exists_sectionSixTerminalTFundamentalResidualAbsorptionDeltaThreshold
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) ≤ 1)
    (ell : Nat) (deltaUpper : Real) (hdeltaUpper : 0 < deltaUpper)
    (rho : Real) (hrho : 0 < rho) :
    ∃ (delta : Real) (_hdelta : 0 < delta)
      (_hdeltaUpper : delta < deltaUpper)
      (_hdeltaGap : delta < sectionSixThetaGap epsilon)
      (length0 : Nat) (_hlength0 : 1 ≤ length0),
      ∀ (length : Nat), length0 ≤ length → ∀ digit : Fin 10,
        ((5 * (Nat.ceil (1 / delta)) ^ ell : Nat) : Real) *
            sectionSixFundamentalResidual digit epsilon delta length ≤
          rho * ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log ((10 ^ length : Nat) : Real) := by
  obtain ⟨C, hC, lengthFund, hlengthFund, hFund⟩ :=
    exists_correctedFundamentalLemma epsilon hepsilon hepsilonSmall
      hepsilonRosser
  have hgapPos : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  obtain ⟨delta, hdelta, hdeltaUpper', hdeltaGap, hrapid⟩ :=
    exists_sectionSixTerminalTFundamentalRapidDelta ell C deltaUpper
      (sectionSixThetaGap epsilon) rho hdeltaUpper hgapPos hrho
  let K : Real := ((5 * (Nat.ceil (1 / delta)) ^ ell : Nat) : Real)
  obtain ⟨lengthEndpoint, hEndpoint⟩ :=
    exists_decimalEndpointThreshold delta hdelta
  obtain ⟨lengthScalar, hScalar⟩ :=
    exists_sectionSixTerminalTFundamentalLogThreshold ell C rho delta hrho
      hdelta
  let length0 : Nat :=
    max 1 (max lengthFund (max lengthEndpoint lengthScalar))
  have hlength0 : 1 ≤ length0 := by
    dsimp [length0]
    omega
  refine ⟨delta, hdelta, hdeltaUpper', hdeltaGap, length0, hlength0, ?_⟩
  intro length hlength digit
  have hlengthFund' : lengthFund ≤ length := by
    dsimp [length0] at hlength
    omega
  have hlengthEndpoint' : lengthEndpoint ≤ length := by
    dsimp [length0] at hlength
    omega
  have hlengthScalar' : lengthScalar ≤ length := by
    dsimp [length0] at hlength
    omega
  have hlengthOne : 1 ≤ length := hlength0.trans hlength
  have hendpoint := hEndpoint length hlengthEndpoint'
  have hscalar := hScalar length hlengthScalar'
  have hfundRaw := hFund length hlengthFund' digit delta hdelta
  dsimp at hfundRaw
  have hfund := hfundRaw hendpoint.2.1
  have hK : 0 ≤ K := by positivity
  have hA : 0 ≤ ((paddedRestrictedNumbers digit length).card : Real) := by
    positivity
  let X : Real := ((10 ^ length : Nat) : Real)
  let L : Real := Real.log X
  have hX : 1 < X := by
    dsimp [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hLPos : 0 < L := by
    dsimp [L, X]
    exact Real.log_pos hX
  have hrapidHalf : K * C *
      Real.exp (-(delta ^ (-(2 / 3 : Real)))) ≤ rho / 2 := by
    have := hrapid
    dsimp [K] at this ⊢
    nlinarith
  have hfirstScalar : K * C *
      Real.exp (-(delta ^ (-(2 / 3 : Real)))) / L ≤ rho / (2 * L) :=
    (div_le_div_of_nonneg_right hrapidHalf hLPos.le).trans_eq (by ring)
  have hlogScalar : K * C / L ^ (100 : Nat) ≤ rho / (2 * L) := by
    apply (div_le_div_iff₀ (pow_pos hLPos 100)
      (mul_pos (by norm_num) hLPos)).2
    have hmul := mul_le_mul_of_nonneg_right hscalar.2 hLPos.le
    calc
      K * C * (2 * L) = (2 * K * C) * L := by ring
      _ ≤ (rho * L ^ (99 : Nat)) * L := hmul
      _ = rho * L ^ (100 : Nat) := by ring
  have hfirstMass := mul_le_mul_of_nonneg_right hfirstScalar hA
  have hlogMass := mul_le_mul_of_nonneg_right hlogScalar hA
  have hbudget :
      K * (C * ((paddedRestrictedNumbers digit length).card : Real) *
          Real.exp (-(delta ^ (-(2 / 3 : Real)))) / L +
        C * ((paddedRestrictedNumbers digit length).card : Real) /
          L ^ (100 : Nat)) ≤
        rho * ((paddedRestrictedNumbers digit length).card : Real) / L := by
    calc
      _ = (K * C * Real.exp (-(delta ^ (-(2 / 3 : Real)))) / L) *
            ((paddedRestrictedNumbers digit length).card : Real) +
          (K * C / L ^ (100 : Nat)) *
            ((paddedRestrictedNumbers digit length).card : Real) := by
        ring
      _ ≤ (rho / (2 * L)) *
            ((paddedRestrictedNumbers digit length).card : Real) +
          (rho / (2 * L)) *
            ((paddedRestrictedNumbers digit length).card : Real) :=
        add_le_add hfirstMass hlogMass
      _ = rho * ((paddedRestrictedNumbers digit length).card : Real) / L := by
        ring
  have hweighted := mul_le_mul_of_nonneg_left hfund hK
  have hresidual :
      K * sectionSixFundamentalResidual digit epsilon delta length ≤
        rho * ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log ((10 ^ length : Nat) : Real) := by
    simpa only [sectionSixFundamentalResidual, X, L, K] using
      hweighted.trans hbudget
  simpa only [K] using hresidual

theorem exists_sectionSixTerminalTSignedContributionAbsorptionDeltaThreshold
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) ≤ 1)
    (ell : Nat) (deltaUpper : Real) (hdeltaUpper : 0 < deltaUpper)
    (rho : Real) (hrho : 0 < rho) :
    ∃ (delta : Real) (_hdelta : 0 < delta)
      (_hdeltaUpper' : delta < deltaUpper)
      (hdeltaGap : delta < sectionSixThetaGap epsilon)
      (length0 : Nat) (hlength0 : 1 ≤ length0),
      ∀ (length : Nat) (hlength : length0 ≤ length), ∀ digit : Fin 10,
        ∀ region : Set (Fin ell → Real), ∀ band : SectionSixStateBand,
          abs (sectionSixSourceBandSelectedSignedContribution (delta := delta)
            (ell := ell) (length := length) digit region
            hepsilon hepsilonSmall (by omega : 1 ≤ length)
            hdeltaGap.le band sectionSixTerminalTPredicate) ≤
            rho * ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log ((10 ^ length : Nat) : Real) := by
  obtain ⟨delta, hdelta, hdeltaUpper', hdeltaGap, length0, hlength0,
      hResidual⟩ :=
    exists_sectionSixTerminalTFundamentalResidualAbsorptionDeltaThreshold
      epsilon hepsilon hepsilonSmall hepsilonRosser ell deltaUpper
        hdeltaUpper rho hrho
  refine ⟨delta, hdelta, hdeltaUpper', hdeltaGap, length0, hlength0, ?_⟩
  intro length hlength digit region band
  have hfinite := abs_sectionSixSourceBandTSignedContribution_le_fundamentalResidual
    (ell := ell) (length := length) digit region hepsilon hepsilonSmall
      (hlength0.trans hlength) hdelta
      hdeltaGap.le hdeltaGap band
  have hres := hResidual length hlength digit
  exact hfinite.trans (by
    simpa only [sectionSixFundamentalResidual] using hres)

end

end PrimesRestrictedDigits
