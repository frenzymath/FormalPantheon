import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectRepeatedTypeI
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRepeatedTerminalAbsorption
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Direct repeated-term Type I absorption

For fixed positive `delta`, the exact direct incidence factor is constant before the decimal
length. The saving-100 Type I estimate and the squareful main-term decay absorb either direct
band into an arbitrary logarithmic budget.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_sectionSixDirectRangeRepeatedAbsorptionThreshold
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (ell : Nat) (rho : Real) (hrho : 0 < rho)
    (delta : Real) (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon) :
    ∃ (length0 : Nat) (_hlength0 : 1 ≤ length0),
      ∀ (length : Nat), length0 ≤ length →
        ∀ (digit : Fin 10) (region : Set (Fin ell → Real))
          (band : SectionSixDirectBand),
          abs (sectionSixDirectRangeRepeatedContribution digit epsilon delta
            ell length region band) ≤
            rho * ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log (((10 ^ length : Nat) : Real)) := by
  obtain ⟨lengthTypeI, hTypeI⟩ :=
    exists_typeIProgressionEstimate (100 : Real) (by norm_num)
  obtain ⟨lengthLevel, hLevel⟩ :=
    exists_fundamentalTypeILevel_threshold epsilon hepsilon
  obtain ⟨lengthEndpoint, hEndpoint⟩ :=
    exists_decimalEndpointThreshold (delta / 2) (by positivity)
  obtain ⟨lengthScalar, hScalar⟩ :=
    exists_sectionSixRepeatedTerminalScalarThreshold 0 rho hrho delta hdelta
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
  let K : Real := ((2 ^ M : Nat) : Real)
  let CI : Real := 4 * (26400 * largeSieveConstant + 720)
  let kappaP : Real := (typeIProgressionDensity digit : Real)
  let kappaA : Real := (restrictedDigitDensity digit : Real)
  let E : Real := ∑ r ∈ typeIModuliBelow Q,
    abs (realTypeIProgressionError digit length r)
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
  have hscalarsFive :
      1 ≤ L ∧
        10 * (5 * K) * L ≤ rho * Y ∧
        2 * (5 * K) * CI ≤ rho * L ^ (99 : Nat) := by
    simpa only [X, Y, L, M, K, CI, Nat.pow_zero, Nat.mul_one,
      Nat.cast_mul, Nat.cast_ofNat] using hscalarRaw
  have hLNonneg : 0 ≤ L := zero_le_one.trans hscalarsFive.1
  have hKFive : K ≤ 5 * K := by nlinarith
  have hscalars :
      1 ≤ L ∧
        10 * K * L ≤ rho * Y ∧
        2 * K * CI ≤ rho * L ^ (99 : Nat) := by
    refine ⟨hscalarsFive.1, ?_, ?_⟩
    · exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hKFive (by norm_num)) hLNonneg).trans
          hscalarsFive.2.1
    · exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hKFive (by norm_num)) hCI).trans
          hscalarsFive.2.2
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
      q ∈ sievePrimeInterval Y (X ^ sectionSixThetaGap epsilon) →
        ((q * q : Nat) : Real) < Q := by
    intro q hq
    exact sectionSixPrimeSquare_lt_repeatedTypeILevel hepsilon hX hq
  have hfiniteRaw :=
    abs_sectionSixDirectRangeRepeatedContribution_typeI_le digit region
      hlengthOne hdelta hdeltaGapStrict band hstrictEndpoint hcutoff
  have hfinite :
      abs (sectionSixDirectRangeRepeatedContribution digit epsilon delta ell
        length region band) ≤
        K * (2 * kappaP * A / Y + E) +
          kappaA * (A / X) * (K * (2 * X / Y)) := by
    simpa only [X, Y, Q, A, M, K, kappaP, kappaA, E] using hfiniteRaw
  have hfiniteError :
      abs (sectionSixDirectRangeRepeatedContribution digit epsilon delta ell
        length region band) ≤
        K * (2 * kappaP * A / Y + CI * A / L ^ (100 : Nat)) +
          kappaA * (A / X) * (K * (2 * X / Y)) := by
    apply hfinite.trans
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
    field_simp [hXPos.ne', hYPos.ne', hLPos.ne']
    ring
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
        field_simp [hLPos.ne']
        ring
  exact hfiniteError.trans (hmainBound.trans hbudget)

end

end PrimesRestrictedDigits
