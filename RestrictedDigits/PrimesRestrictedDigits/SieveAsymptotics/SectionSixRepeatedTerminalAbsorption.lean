import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRepeatedTypeILevel
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRepeatedTerminalValueBound
import PrimesRestrictedDigits.SieveAsymptotics.SourceFundamentalSieveAggregateBridges
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalTypeILevel
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaPreparation
import PrimesRestrictedDigits.SieveAsymptotics.TypeIICellSupportMass
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Repeated terminal Type I absorption

For fixed positive `delta`, the incidence factor is constant before the decimal length.
Proposition 7.1 with saving `100` controls its progression error, while the squareful main
terms decay like `X^(-delta)`.
-/

open Filter Asymptotics
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- At sufficiently large decimal lengths, the fixed repeated-state incidence
factor satisfies both scalar inequalities needed for the `rho / log X` split. -/
theorem exists_sectionSixRepeatedTerminalScalarThreshold
    (ell : Nat) (rho : Real) (hrho : 0 < rho)
    (delta : Real) (hdelta : 0 < delta) :
    ∃ length0 : Nat, ∀ length : Nat, length0 ≤ length →
      let X : Real := ((10 ^ length : Nat) : Real)
      let M : Nat := Nat.ceil (1 / delta)
      let KNat : Nat := (5 * M ^ ell) * 2 ^ M
      let K : Real := (KNat : Real)
      let CI : Real := 4 * (26400 * largeSieveConstant + 720)
      1 ≤ Real.log X ∧
        10 * K * Real.log X ≤ rho * X ^ delta ∧
        2 * K * CI ≤ rho * Real.log X ^ (99 : Nat) := by
  let M : Nat := Nat.ceil (1 / delta)
  let KNat : Nat := (5 * M ^ ell) * 2 ^ M
  let K : Real := (KNat : Real)
  let CI : Real := 4 * (26400 * largeSieveConstant + 720)
  have hK : 0 ≤ K := by positivity
  have hCI : 0 ≤ CI := by
    dsimp [CI, largeSieveConstant]
    norm_num
  have hpowerReal : ∀ᶠ x : Real in atTop,
      10 * K * Real.log x ≤ rho * x ^ delta := by
    have hbound :=
      ((isLittleO_log_rpow_rpow_atTop (1 : Real) hdelta).const_mul_left
        (10 * K)).bound hrho
    filter_upwards [hbound, eventually_ge_atTop (1 : Real)] with x hx hxOne
    have hlogNonneg : 0 ≤ Real.log x := Real.log_nonneg hxOne
    have hleftNonneg : 0 ≤ 10 * K * Real.log x := by positivity
    have hrightNonneg : 0 ≤ x ^ delta := by positivity
    simpa only [Real.rpow_one, Real.norm_of_nonneg hleftNonneg,
      Real.norm_of_nonneg hrightNonneg] using hx
  have hlogPowTendsto :
      Tendsto (fun x : Real => Real.log x ^ (99 : Nat)) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (99 : Nat) ≠ 0)).comp
      Real.tendsto_log_atTop
  have hlogPowerReal : ∀ᶠ x : Real in atTop,
      2 * K * CI ≤ rho * Real.log x ^ (99 : Nat) := by
    have hlarge := hlogPowTendsto.eventually_ge_atTop ((2 * K * CI) / rho)
    filter_upwards [hlarge] with x hx
    have hx' : 2 * K * CI ≤ Real.log x ^ (99 : Nat) * rho :=
      (div_le_iff₀ hrho).mp hx
    simpa only [mul_comm] using hx'
  have hlogReal : ∀ᶠ x : Real in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : Real)
  have hscale : Tendsto
      (fun length : Nat => ((10 ^ length : Nat) : Real)) atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  have hpull := hscale.eventually (hlogReal.and (hpowerReal.and hlogPowerReal))
  apply eventually_atTop.mp
  filter_upwards [hpull] with length hlength
  simpa only [M, KNat, K, CI] using hlength

/--
For every fixed admissible `delta`, the unsigned repeated-terminal sum is eventually absorbed
into an arbitrary per-band `rho / log X` budget, uniformly in the digit, source region, and
band.
-/
theorem exists_sectionSixRepeatedTerminalAbsorptionThreshold
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (ell : Nat) (rho : Real) (hrho : 0 < rho)
    (delta : Real) (hdelta : 0 < delta)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon) :
    ∃ (length0 : Nat) (hlength0 : 1 ≤ length0),
      ∀ (length : Nat) (hlength : length0 ≤ length)
        (digit : Fin 10) (region : Set (Fin ell → Real))
        (band : SectionSixStateBand),
        (∑ state ∈ sectionSixSourceBandTerminalStateFinset region
            hepsilon hepsilonSmall (hlength0.trans hlength) hdeltaGap band,
          abs (sectionSixRepeatedTerminalStateValue digit length
            (((10 ^ length : Nat) : Real) ^ delta) state)) ≤
          rho * ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log (((10 ^ length : Nat) : Real)) := by
  obtain ⟨lengthTypeI, hTypeI⟩ :=
    exists_typeIProgressionEstimate (100 : Real) (by norm_num)
  obtain ⟨lengthLevel, hLevel⟩ :=
    exists_fundamentalTypeILevel_threshold epsilon hepsilon
  obtain ⟨lengthEndpoint, hEndpoint⟩ :=
    exists_decimalEndpointThreshold (delta / 2) (by positivity)
  obtain ⟨lengthScalar, hScalar⟩ :=
    exists_sectionSixRepeatedTerminalScalarThreshold ell rho hrho delta hdelta
  let length0 : Nat :=
    max 1 (max lengthTypeI (max lengthLevel (max lengthEndpoint lengthScalar)))
  have hlength0 : 1 ≤ length0 := by
    dsimp [length0]
    omega
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit region band
  have hlengthOne : 1 ≤ length := hlength0.trans hlength
  have hlengthTypeI : lengthTypeI ≤ length := by
    have : lengthTypeI ≤ length0 := by
      dsimp [length0]
      omega
    exact this.trans hlength
  have hlengthLevel : lengthLevel ≤ length := by
    have : lengthLevel ≤ length0 := by
      dsimp [length0]
      omega
    exact this.trans hlength
  have hlengthEndpoint : lengthEndpoint ≤ length := by
    have : lengthEndpoint ≤ length0 := by
      dsimp [length0]
      omega
    exact this.trans hlength
  have hlengthScalar : lengthScalar ≤ length := by
    have : lengthScalar ≤ length0 := by
      dsimp [length0]
      omega
    exact this.trans hlength
  let X : Real := ((10 ^ length : Nat) : Real)
  let Y : Real := X ^ delta
  let Q : Real := X ^ (50 / 77 - epsilon / 2)
  let L : Real := Real.log X
  let A : Real := ((paddedRestrictedNumbers digit length).card : Real)
  let M : Nat := Nat.ceil (1 / delta)
  let KNat : Nat := (5 * M ^ ell) * 2 ^ M
  let K : Real := (KNat : Real)
  let CI : Real := 4 * (26400 * largeSieveConstant + 720)
  let kappaP : Real := (typeIProgressionDensity digit : Real)
  let kappaA : Real := (restrictedDigitDensity digit : Real)
  let E : Real := ∑ r ∈ typeIModuliBelow Q,
    |realTypeIProgressionError digit length r|
  have hX : 1 < X := by
    dsimp [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hXPos : 0 < X := zero_lt_one.trans hX
  have hYPos : 0 < Y := by
    dsimp [Y]
    positivity
  have hK : 0 ≤ K := by positivity
  have hA : 0 ≤ A := by positivity
  have hCI : 0 ≤ CI := by
    dsimp [CI, largeSieveConstant]
    norm_num
  have hendpointRaw := hEndpoint length hlengthEndpoint
  have hhalf : 5 ≤ X ^ (delta / 2) := by
    simpa only [X] using hendpointRaw.2.1
  have hstrictEndpoint : 5 < Y := by
    apply hhalf.trans_lt
    dsimp only [Y]
    exact Real.rpow_lt_rpow_of_exponent_lt hX (by linarith)
  have hscalarRaw := hScalar length hlengthScalar
  have hscalars :
      1 ≤ L ∧
        10 * K * L ≤ rho * Y ∧
        2 * K * CI ≤ rho * L ^ (99 : Nat) := by
    simpa only [X, Y, L, M, KNat, K, CI] using hscalarRaw
  have hLPos : 0 < L := zero_lt_one.trans_le hscalars.1
  have hlevelRaw := hLevel length hlengthLevel
  have hQLevel :
      Q ≤ (((10 ^ length : Nat) : Real) ^ (50 / 77 : Real)) *
        Real.log (((10 ^ length : Nat) : Real)) ^
          (-2 * (100 : Real) - 2) := by
    simpa only [Q, X] using hlevelRaw
  have herrorRpowRaw := sourceFundamental_typeI_sum_normalized
    (length0 := lengthTypeI) (length := length) hlengthTypeI digit Q
    hQLevel hTypeI
  have herrorRpow : E ≤ CI * A * L ^ (-100 : Real) := by
    simpa only [E, CI, A, L, X] using herrorRpowRaw
  have hnegativePower : L ^ (-100 : Real) =
      (L ^ (100 : Nat))⁻¹ := by
    rw [Real.rpow_neg hLPos.le]
    exact congrArg Inv.inv (Real.rpow_natCast L 100)
  have herror : E ≤ CI * A / L ^ (100 : Nat) := by
    rw [hnegativePower] at herrorRpow
    simpa only [div_eq_mul_inv] using herrorRpow
  have hcutoff : ∀ q,
      q ∈ sievePrimeInterval Y
        (X ^ sectionSixThetaGap epsilon) →
      ((q * q : Nat) : Real) < Q := by
    intro q hq
    exact sectionSixPrimeSquare_lt_repeatedTypeILevel hepsilon hX hq
  have hW105Raw :=
    sum_abs_sectionSixSourceBandRepeatedTerminalStateValue_typeI_le
      digit region hepsilon hepsilonSmall hlengthOne hdelta hdeltaGap band
      hstrictEndpoint hcutoff
  have hW105 :
      (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
          hepsilonSmall hlengthOne hdeltaGap band,
        abs (sectionSixRepeatedTerminalStateValue digit length Y state)) ≤
        K * (2 * kappaP * A / Y + E) +
          kappaA * (A / X) * (K * (2 * X / Y)) := by
    simpa only [X, Y, Q, A, M, KNat, K, kappaP, kappaA, E] using hW105Raw
  have hW105Error :
      (∑ state ∈ sectionSixSourceBandTerminalStateFinset region hepsilon
          hepsilonSmall hlengthOne hdeltaGap band,
        abs (sectionSixRepeatedTerminalStateValue digit length Y state)) ≤
        K * (2 * kappaP * A / Y + CI * A / L ^ (100 : Nat)) +
          kappaA * (A / X) * (K * (2 * X / Y)) := by
    apply hW105.trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left (add_le_add le_rfl herror) hK
    · exact le_rfl
  have hkappaP := sourceFundamental_typeIProgressionDensity_bounds digit
  have hkappaA0 := restrictedDigitDensity_nonneg digit
  have hkappaAUpper := restrictedDigitDensity_le_ten_ninths digit
  have hcoefficient : 2 * kappaP + 2 * kappaA ≤ 5 := by
    dsimp only [kappaP, kappaA]
    linarith
  have hfactorNonneg : 0 ≤ K * A / Y := by positivity
  have hcompact :
      K * (2 * kappaP * A / Y + CI * A / L ^ (100 : Nat)) +
          kappaA * (A / X) * (K * (2 * X / Y)) =
        (2 * kappaP + 2 * kappaA) * (K * A / Y) +
          K * CI * A / L ^ (100 : Nat) := by
    field_simp [hXPos.ne', hYPos.ne', hLPos.ne']; ring
  have hmainBound :
      K * (2 * kappaP * A / Y + CI * A / L ^ (100 : Nat)) +
          kappaA * (A / X) * (K * (2 * X / Y)) ≤
        5 * K * A / Y + K * CI * A / L ^ (100 : Nat) := by
    rw [hcompact]
    calc
      (2 * kappaP + 2 * kappaA) * (K * A / Y) +
            K * CI * A / L ^ (100 : Nat) ≤
          5 * (K * A / Y) + K * CI * A / L ^ (100 : Nat) :=
        add_le_add
          (mul_le_mul_of_nonneg_right hcoefficient hfactorNonneg) le_rfl
      _ = 5 * K * A / Y + K * CI * A / L ^ (100 : Nat) := by ring
  have hpowerScalar : 5 * K / Y ≤ rho / (2 * L) := by
    apply (div_le_div_iff₀ hYPos (mul_pos (by norm_num) hLPos)).2
    calc
      5 * K * (2 * L) = 10 * K * L := by ring
      _ ≤ rho * Y := hscalars.2.1
  have hlogScalar : K * CI / L ^ (100 : Nat) ≤ rho / (2 * L) := by
    apply (div_le_div_iff₀ (pow_pos hLPos 100)
      (mul_pos (by norm_num) hLPos)).2
    have hmul := mul_le_mul_of_nonneg_right hscalars.2.2 hLPos.le
    calc
      K * CI * (2 * L) = (2 * K * CI) * L := by ring
      _ ≤ (rho * L ^ (99 : Nat)) * L := hmul
      _ = rho * L ^ (100 : Nat) := by ring
  have hpowerMass := mul_le_mul_of_nonneg_right hpowerScalar hA
  have hlogMass := mul_le_mul_of_nonneg_right hlogScalar hA
  have hbudget :
      5 * K * A / Y + K * CI * A / L ^ (100 : Nat) ≤ rho * A / L := by
    calc
      5 * K * A / Y + K * CI * A / L ^ (100 : Nat) =
          (5 * K / Y) * A + (K * CI / L ^ (100 : Nat)) * A := by ring
      _ ≤ (rho / (2 * L)) * A + (rho / (2 * L)) * A :=
        add_le_add hpowerMass hlogMass
      _ = rho * A / L := by
        field_simp [hLPos.ne']; ring
  exact hW105Error.trans (hmainBound.trans hbudget)

end

end PrimesRestrictedDigits
