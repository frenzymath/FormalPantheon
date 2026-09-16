import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectQuarterTieCardinality
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRepeatedTerminalAbsorption
import PrimesRestrictedDigits.Fourier.HybridResidualDecay

/-!
# Fixed-quarter target-tie absorption

For fixed positive `delta`, every fixed natural multiple of the weighted quarter-tie value
charge is eventually absorbed into an arbitrary `#A / log X` budget, uniformly in the excluded
digit.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A fixed natural multiple of the common quarter-tie value charge is
eventually negligible relative to the restricted-digit logarithmic scale. -/
theorem exists_sectionSixDirectQuarterTieChargeAbsorptionThreshold
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (K : Nat) (budget : Real) (hbudget : 0 < budget)
    (delta : Real) (hdelta : 0 < delta) :
    ∃ (length0 : Nat) (_hlength0 : 1 ≤ length0),
      ∀ (length : Nat), length0 ≤ length →
        ∀ digit : Fin 10,
          (K : Real) *
              sectionSixDirectQuarterTieCharge digit length delta ≤
            budget *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log (((10 ^ length : Nat) : Real)) := by
  let beta : Real := min delta (17 / 84)
  have hbeta : 0 < beta := by
    dsimp only [beta]
    exact lt_min hdelta (by norm_num)
  let M : Nat := Nat.ceil (1 / beta)
  let K0Nat : Nat := (5 * M ^ 0) * 2 ^ M
  let K0 : Real := (K0Nat : Real)
  have hK0 : 0 < K0 := by
    dsimp only [K0, K0Nat]
    positivity
  let rho : Real := budget * K0 / (2 * ((K : Real) + 1))
  have hrho : 0 < rho := by
    dsimp only [rho]
    positivity
  obtain ⟨lengthTypeI, hTypeI⟩ :=
    exists_typeIProgressionEstimate (100 : Real) (by norm_num)
  obtain ⟨lengthLevel, hLevel⟩ :=
    exists_fundamentalTypeILevel_threshold epsilon hepsilon
  obtain ⟨lengthDelta, hDeltaEndpoint⟩ :=
    exists_decimalEndpointThreshold (delta / 2) (by positivity)
  obtain ⟨lengthQuarter, hQuarterEndpoint⟩ :=
    exists_decimalEndpointThreshold (1 / 4) (by norm_num)
  obtain ⟨lengthScalar, hScalar⟩ :=
    exists_sectionSixRepeatedTerminalScalarThreshold 0 rho hrho beta hbeta
  let length0 : Nat := max 1
    (max lengthTypeI
      (max lengthLevel (max lengthDelta (max lengthQuarter lengthScalar))))
  have hlength0 : 1 ≤ length0 := by
    dsimp only [length0]
    omega
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  have hlengthOne : 1 ≤ length := hlength0.trans hlength
  have hlengthTypeI : lengthTypeI ≤ length := by
    have : lengthTypeI ≤ length0 := by
      dsimp only [length0]
      omega
    exact this.trans hlength
  have hlengthLevel : lengthLevel ≤ length := by
    have : lengthLevel ≤ length0 := by
      dsimp only [length0]
      omega
    exact this.trans hlength
  have hlengthDelta : lengthDelta ≤ length := by
    have : lengthDelta ≤ length0 := by
      dsimp only [length0]
      omega
    exact this.trans hlength
  have hlengthQuarter : lengthQuarter ≤ length := by
    have : lengthQuarter ≤ length0 := by
      dsimp only [length0]
      omega
    exact this.trans hlength
  have hlengthScalar : lengthScalar ≤ length := by
    have : lengthScalar ≤ length0 := by
      dsimp only [length0]
      omega
    exact this.trans hlength
  let X : Real := ((10 ^ length : Nat) : Real)
  let Y : Real := X ^ delta
  let Z : Real := X ^ (1 / 4 : Real)
  let G : Real := X ^ (17 / 84 : Real)
  let L : Real := Real.log X
  let A : Real := ((paddedRestrictedNumbers digit length).card : Real)
  let Q : Real := X ^ (50 / 77 - epsilon / 2)
  let E : Real := ∑ r ∈ typeIModuliBelow Q,
    |realTypeIProgressionError digit length r|
  let CI : Real := 4 * (26400 * largeSieveConstant + 720)
  let kappaP : Real := (typeIProgressionDensity digit : Real)
  let kappaA : Real := (restrictedDigitDensity digit : Real)
  let lambda : Real := kappaA * A / X
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hXPos : 0 < X := zero_lt_one.trans hX
  have hYPos : 0 < Y := by dsimp only [Y]; positivity
  have hZPos : 0 < Z := by dsimp only [Z]; positivity
  have hGPos : 0 < G := by dsimp only [G]; positivity
  have hANonneg : 0 ≤ A := by positivity
  have hKNonneg : 0 ≤ (K : Real) := by positivity
  have hCINonneg : 0 ≤ CI := by
    dsimp only [CI, largeSieveConstant]
    norm_num
  have hdeltaEndpoint := hDeltaEndpoint length hlengthDelta
  have hdeltaHalf : 5 ≤ X ^ (delta / 2) := by
    simpa only [X] using hdeltaEndpoint.2.1
  have hstrictY : 5 < Y := by
    apply hdeltaHalf.trans_lt
    dsimp only [Y]
    exact Real.rpow_lt_rpow_of_exponent_lt hX (by linarith)
  have hquarterEndpoint := hQuarterEndpoint length hlengthQuarter
  have hquarterFive : 5 ≤ Z := by
    simpa only [X, Z] using hquarterEndpoint.2.1
  have hquarterTwo : 2 ≤ Z := by linarith
  have hscalarRaw := hScalar length hlengthScalar
  have hscalars :
      1 ≤ L ∧
        10 * K0 * L ≤ rho * X ^ beta ∧
        2 * K0 * CI ≤ rho * L ^ (99 : Nat) := by
    simpa only [X, L, beta, M, K0Nat, K0, CI, Nat.pow_zero,
      Nat.mul_one] using hscalarRaw
  have hLPos : 0 < L := zero_lt_one.trans_le hscalars.1
  have hbetaDelta : beta ≤ delta := by
    dsimp only [beta]
    exact min_le_left _ _
  have hbetaGap : beta ≤ (17 / 84 : Real) := by
    dsimp only [beta]
    exact min_le_right _ _
  have hbetaQuarter : beta ≤ (1 / 4 : Real) :=
    hbetaGap.trans (by norm_num)
  have hXBetaDelta : X ^ beta ≤ Y := by
    dsimp only [Y]
    exact Real.rpow_le_rpow_of_exponent_le hX.le hbetaDelta
  have hXBetaGap : X ^ beta ≤ G := by
    dsimp only [G]
    exact Real.rpow_le_rpow_of_exponent_le hX.le hbetaGap
  have hXBetaQuarter : X ^ beta ≤ Z := by
    dsimp only [Z]
    exact Real.rpow_le_rpow_of_exponent_le hX.le hbetaQuarter
  have hmasterPower : 20 * (K : Real) * L ≤ budget * X ^ beta := by
    have hmul := mul_le_mul_of_nonneg_left hscalars.2.1
      (show 0 ≤ 2 * ((K : Real) + 1) by positivity)
    have hK0Cancel :
        K0 * (20 * ((K : Real) + 1) * L) ≤
          K0 * (budget * X ^ beta) := by
      calc
        K0 * (20 * ((K : Real) + 1) * L) =
            (2 * ((K : Real) + 1)) * (10 * K0 * L) := by ring
        _ ≤ (2 * ((K : Real) + 1)) * (rho * X ^ beta) := hmul
        _ = K0 * (budget * X ^ beta) := by
          dsimp only [rho]
          field_simp
    have hplus : 20 * ((K : Real) + 1) * L ≤ budget * X ^ beta :=
      le_of_mul_le_mul_left hK0Cancel hK0
    have hKL : 0 ≤ (K : Real) * L := mul_nonneg hKNonneg hLPos.le
    calc
      20 * (K : Real) * L ≤ 20 * ((K : Real) + 1) * L := by
        nlinarith
      _ ≤ budget * X ^ beta := hplus
  have hmasterLog : 4 * (K : Real) * CI ≤ budget * L ^ (99 : Nat) := by
    have hmul := mul_le_mul_of_nonneg_left hscalars.2.2
      (show 0 ≤ 2 * ((K : Real) + 1) by positivity)
    have hK0Cancel :
        K0 * (4 * ((K : Real) + 1) * CI) ≤
          K0 * (budget * L ^ (99 : Nat)) := by
      calc
        K0 * (4 * ((K : Real) + 1) * CI) =
            (2 * ((K : Real) + 1)) * (2 * K0 * CI) := by ring
        _ ≤ (2 * ((K : Real) + 1)) *
            (rho * L ^ (99 : Nat)) := hmul
        _ = K0 * (budget * L ^ (99 : Nat)) := by
          dsimp only [rho]
          field_simp
    have hplus : 4 * ((K : Real) + 1) * CI ≤
        budget * L ^ (99 : Nat) :=
      le_of_mul_le_mul_left hK0Cancel hK0
    calc
      4 * (K : Real) * CI ≤ 4 * ((K : Real) + 1) * CI := by
        nlinarith
      _ ≤ budget * L ^ (99 : Nat) := hplus
  have hgateY : 20 * (K : Real) * L ≤ budget * Y :=
    hmasterPower.trans
      (mul_le_mul_of_nonneg_left hXBetaDelta hbudget.le)
  have hgateG : 8 * (K : Real) * L ≤ budget * G := by
    calc
      8 * (K : Real) * L ≤ 20 * (K : Real) * L := by nlinarith
      _ ≤ budget * X ^ beta := hmasterPower
      _ ≤ budget * G := mul_le_mul_of_nonneg_left hXBetaGap hbudget.le
  have hgateZ : 12 * (K : Real) * L ≤ budget * Z := by
    calc
      12 * (K : Real) * L ≤ 20 * (K : Real) * L := by nlinarith
      _ ≤ budget * X ^ beta := hmasterPower
      _ ≤ budget * Z :=
        mul_le_mul_of_nonneg_left hXBetaQuarter hbudget.le
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
  have hchargeRaw := sectionSixDirectQuarterTieCharge_le digit
    hepsilonSmall hlengthOne hstrictY hquarterTwo
  have hcharge : sectionSixDirectQuarterTieCharge digit length delta ≤
      (2 * kappaP * A / Y + E + 2 * X / Z) +
        lambda * (2 * X / Y + 2 * X / Z) := by
    simpa only [X, Y, Z, Q, E, A, kappaP, kappaA, lambda]
      using hchargeRaw
  have hchargeError : sectionSixDirectQuarterTieCharge digit length delta ≤
      (2 * kappaP * A / Y + CI * A / L ^ (100 : Nat) + 2 * X / Z) +
        lambda * (2 * X / Y + 2 * X / Z) := by
    apply hcharge.trans
    gcongr
  have hkappaP := sourceFundamental_typeIProgressionDensity_bounds digit
  have hkappaANonneg : 0 ≤ kappaA := by
    dsimp only [kappaA]
    rw [restrictedDigitDensity_eq]
    split_ifs <;> norm_num
  have hkappaAUpper : kappaA ≤ 10 / 9 := by
    dsimp only [kappaA]
    rw [restrictedDigitDensity_eq]
    split_ifs <;> norm_num
  have hsmallCoefficient : 2 * kappaP + 2 * kappaA ≤ 5 := by
    linarith
  have hlargeCoefficient : 2 * kappaA ≤ 3 := by linarith
  have hsmallTerm :
      (2 * kappaP + 2 * kappaA) * A / Y ≤ 5 * A / Y := by
    have hfactor : 0 ≤ A / Y := div_nonneg hANonneg hYPos.le
    calc
      (2 * kappaP + 2 * kappaA) * A / Y =
          (2 * kappaP + 2 * kappaA) * (A / Y) := by ring
      _ ≤ 5 * (A / Y) :=
        mul_le_mul_of_nonneg_right hsmallCoefficient hfactor
      _ = 5 * A / Y := by ring
  have hweightedLargeTerm : 2 * kappaA * A / Z ≤ 3 * A / Z := by
    have hfactor : 0 ≤ A / Z := div_nonneg hANonneg hZPos.le
    calc
      2 * kappaA * A / Z = (2 * kappaA) * (A / Z) := by ring
      _ ≤ 3 * (A / Z) :=
        mul_le_mul_of_nonneg_right hlargeCoefficient hfactor
      _ = 3 * A / Z := by ring
  have hdecimalPower : X ^ hybridResidualDecay ≤ A := by
    simpa only [X, A, card_paddedRestrictedNumbers, Nat.cast_pow,
      Nat.cast_ofNat] using
        decimalPower_rpow_hybridResidualDecay_le_nine_pow length
  have hpowerIdentity : X / Z * G = X ^ hybridResidualDecay := by
    dsimp only [Z, G, hybridResidualDecay]
    rw [show (20 / 21 : Real) = 1 - 1 / 4 + 17 / 84 by norm_num]
    rw [Real.rpow_add hXPos, Real.rpow_sub hXPos, Real.rpow_one]
  have hlargeRatio : X / Z ≤ A / G := by
    apply (le_div_iff₀ hGPos).2
    rw [hpowerIdentity]
    exact hdecimalPower
  have hunweightedLargeTerm : 2 * X / Z ≤ 2 * A / G := by
    calc
      2 * X / Z = 2 * (X / Z) := by ring
      _ ≤ 2 * (A / G) := mul_le_mul_of_nonneg_left hlargeRatio (by norm_num)
      _ = 2 * A / G := by ring
  have hcompact :
      (2 * kappaP * A / Y + CI * A / L ^ (100 : Nat) + 2 * X / Z) +
          lambda * (2 * X / Y + 2 * X / Z) =
        (2 * kappaP + 2 * kappaA) * A / Y +
          CI * A / L ^ (100 : Nat) + 2 * X / Z +
            2 * kappaA * A / Z := by
    dsimp only [lambda]
    field_simp [hXPos.ne', hYPos.ne', hZPos.ne', hLPos.ne']
    ring
  have hmain : sectionSixDirectQuarterTieCharge digit length delta ≤
      5 * A / Y + CI * A / L ^ (100 : Nat) +
        2 * A / G + 3 * A / Z := by
    apply hchargeError.trans
    rw [hcompact]
    linarith
  have hYScalar : 5 * (K : Real) / Y ≤ budget / (4 * L) := by
    apply (div_le_div_iff₀ hYPos (mul_pos (by norm_num) hLPos)).2
    calc
      5 * (K : Real) * (4 * L) = 20 * (K : Real) * L := by ring
      _ ≤ budget * Y := hgateY
  have hLogScalar : (K : Real) * CI / L ^ (100 : Nat) ≤
      budget / (4 * L) := by
    apply (div_le_div_iff₀ (pow_pos hLPos 100)
      (mul_pos (by norm_num) hLPos)).2
    have hmul := mul_le_mul_of_nonneg_right hmasterLog hLPos.le
    calc
      (K : Real) * CI * (4 * L) =
          (4 * (K : Real) * CI) * L := by ring
      _ ≤ (budget * L ^ (99 : Nat)) * L := hmul
      _ = budget * L ^ (100 : Nat) := by ring
  have hGScalar : 2 * (K : Real) / G ≤ budget / (4 * L) := by
    apply (div_le_div_iff₀ hGPos (mul_pos (by norm_num) hLPos)).2
    calc
      2 * (K : Real) * (4 * L) = 8 * (K : Real) * L := by ring
      _ ≤ budget * G := hgateG
  have hZScalar : 3 * (K : Real) / Z ≤ budget / (4 * L) := by
    apply (div_le_div_iff₀ hZPos (mul_pos (by norm_num) hLPos)).2
    calc
      3 * (K : Real) * (4 * L) = 12 * (K : Real) * L := by ring
      _ ≤ budget * Z := hgateZ
  have hYMass := mul_le_mul_of_nonneg_right hYScalar hANonneg
  have hLogMass := mul_le_mul_of_nonneg_right hLogScalar hANonneg
  have hGMass := mul_le_mul_of_nonneg_right hGScalar hANonneg
  have hZMass := mul_le_mul_of_nonneg_right hZScalar hANonneg
  have hbudgetBound :
      (K : Real) *
          (5 * A / Y + CI * A / L ^ (100 : Nat) +
            2 * A / G + 3 * A / Z) ≤
        budget * A / L := by
    calc
      (K : Real) *
          (5 * A / Y + CI * A / L ^ (100 : Nat) +
            2 * A / G + 3 * A / Z) =
          (5 * (K : Real) / Y) * A +
            ((K : Real) * CI / L ^ (100 : Nat)) * A +
              (2 * (K : Real) / G) * A +
                (3 * (K : Real) / Z) * A := by ring
      _ ≤ (budget / (4 * L)) * A +
            (budget / (4 * L)) * A +
              (budget / (4 * L)) * A +
                (budget / (4 * L)) * A := by
        gcongr
      _ = budget * A / L := by
        field_simp [hLPos.ne']
        ring
  exact (mul_le_mul_of_nonneg_left hmain hKNonneg).trans hbudgetBound

end

end PrimesRestrictedDigits
