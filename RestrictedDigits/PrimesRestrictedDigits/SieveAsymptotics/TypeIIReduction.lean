import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLemma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The restricted sifted-count input to the Type II reduction

This file packages the restricted-set consequence used in Maynard's Eq. (9.11). The cutoff
remains strict, as in the source definition of `S(C, z)`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_admissibleFundamentalEpsilon_le_etaQuarter
    (eta : Real) (heta : 0 < eta) :
    ∃ epsilon : Real,
      0 < epsilon ∧
      epsilon <= 1 / 64 ∧
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1 ∧
      epsilon ^ (4 : Nat) <= eta / 4 := by
  let M : Real := 2 * (Real.exp 5000 + 2)
  let epsilon : Real := min (1 / 64) (min M⁻¹ (eta / 4))
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hfirst : 0 < (1 / 64 : Real) := by norm_num
  have hsecond : 0 < min M⁻¹ (eta / 4) := by
    exact lt_min (by positivity) (by linarith)
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact lt_min hfirst hsecond
  have hepsilonSmall : epsilon <= 1 / 64 := by
    dsimp [epsilon]
    exact min_le_left _ _
  have hepsilonM : epsilon <= M⁻¹ := by
    dsimp [epsilon]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hepsilonEta : epsilon <= eta / 4 := by
    dsimp [epsilon]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hepsilonOne : epsilon <= 1 := by linarith
  have hepsilonCube : epsilon ^ (3 : Nat) <= epsilon := by
    have hepsilonSquare : epsilon ^ (2 : Nat) <= (1 : Real) := by
      have h := pow_le_pow_left₀ hepsilon.le hepsilonOne 2
      simpa using h
    calc
      epsilon ^ (3 : Nat) = epsilon * epsilon ^ (2 : Nat) := by ring
      _ <= epsilon * 1 :=
        mul_le_mul_of_nonneg_left hepsilonSquare hepsilon.le
      _ = epsilon := by ring
  have hepsilonRosser : M * epsilon ^ (3 : Nat) <= 1 := by
    calc
      M * epsilon ^ (3 : Nat) <= M * epsilon :=
        mul_le_mul_of_nonneg_left hepsilonCube hM.le
      _ <= M * M⁻¹ := mul_le_mul_of_nonneg_left hepsilonM hM.le
      _ = 1 := by field_simp [hM.ne']
  have hepsilonFourth : epsilon ^ (4 : Nat) <= eta / 4 := by
    have hfourth :=
      (fundamentalLargeDelta_parameter_bounds epsilon hepsilon
        hepsilonSmall).2.2.1
    exact hfourth.trans hepsilonEta
  exact ⟨epsilon, hepsilon, hepsilonSmall, by simpa [M] using hepsilonRosser,
    hepsilonFourth⟩

/-
The ambient half of Eq. (9.11), with its coefficient chosen after eta and before the decimal
length.
-/
theorem exists_maynardAmbientSiftedCount_eta_upper
    (eta : Real) (heta : 0 < eta) :
    ∃ K : Real, 0 < K ∧
      ∃ length0 : Nat, 1 <= length0 ∧
        ∀ length : Nat, length0 <= length ->
          let X : Real := ((10 ^ length : Nat) : Real)
          ((strictSiftedCarrier
              (maynardAmbientCarrier X)
              (X ^ (eta / 4))).card : Real) <=
            K * X / Real.log X := by
  obtain ⟨epsilon, hepsilon, hepsilonSmall, hepsilonRosser,
      hepsilonFourth⟩ :=
    exists_admissibleFundamentalEpsilon_le_etaQuarter eta heta
  obtain ⟨K, hK, lengthAmbient, hlengthAmbient, hAmbient⟩ :=
    exists_largeDeltaAmbientSiftedCount_upper epsilon hepsilon
      hepsilonSmall hepsilonRosser
  refine ⟨K, hK, lengthAmbient, hlengthAmbient, ?_⟩
  intro length hlength
  dsimp
  let X : Real := ((10 ^ length : Nat) : Real)
  have hlengthOne : 1 <= length := hlengthAmbient.trans hlength
  have hX : 1 < X := by
    dsimp [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have halpha : 0 < 50 / 77 - epsilon := by linarith
  have houter : 1 < X ^ (50 / 77 - epsilon) :=
    Real.one_lt_rpow hX halpha
  have htoPNatOne : (1 : Nat).toPNat' = (1 : PNat) := by rfl
  have hendpoint := hAmbient length hlength 1 (by norm_num)
    (by simpa [X] using houter)
  rw [htoPNatOne, sieveDilation_one] at hendpoint
  have hthreshold :
      X ^ (epsilon ^ (4 : Nat)) <= X ^ (eta / 4) :=
    Real.rpow_le_rpow_of_exponent_le hX.le hepsilonFourth
  calc
    ((strictSiftedCarrier
        (maynardAmbientCarrier X) (X ^ (eta / 4))).card : Real) <=
        ((strictSiftedCarrier
          (maynardAmbientCarrier X)
          (X ^ (epsilon ^ (4 : Nat)))).card : Real) :=
      card_strictSiftedCarrier_threshold_le_real
        (maynardAmbientCarrier X) hthreshold
    _ <= K * X / Real.log X := by simpa [X] using hendpoint

set_option maxHeartbeats 1200000 in
theorem exists_paddedRestrictedSiftedCount_eta_upper
    (eta : Real) (heta : 0 < eta) :
    ∃ C : Real, 0 < C ∧
      ∃ length0 : Nat, 1 <= length0 ∧
        ∀ length : Nat, length0 <= length ->
          ∀ digit : Fin 10,
            let X : Real := ((10 ^ length : Nat) : Real)
            ((strictSiftedCarrier
                (paddedRestrictedNumbers digit length)
                (X ^ (eta / 4))).card : Real) <=
              C * ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log X := by
  obtain ⟨epsilon, hepsilon, hepsilonSmall, hepsilonRosser,
      hepsilonFourth⟩ :=
    exists_admissibleFundamentalEpsilon_le_etaQuarter eta heta
  obtain ⟨CF, hCF, lengthFundamental, hlengthFundamental,
      hFundamental⟩ :=
    exists_correctedFundamentalLemma epsilon hepsilon hepsilonSmall
      hepsilonRosser
  obtain ⟨K, hK, lengthAmbient, hlengthAmbient, hAmbient⟩ :=
    exists_largeDeltaAmbientSiftedCount_upper epsilon hepsilon
      hepsilonSmall hepsilonRosser
  have hepsilonFourthPos : 0 < epsilon ^ (4 : Nat) := by positivity
  obtain ⟨lengthEndpoint, hEndpoint⟩ :=
    exists_decimalEndpointThreshold (epsilon ^ (4 : Nat))
      hepsilonFourthPos
  let C : Real := 2 * CF + (10 / 9 : Real) * K
  have hC : 0 < C := by
    dsimp [C]
    nlinarith
  refine ⟨C, hC, ?_⟩
  let length0 : Nat :=
    max 1 (max lengthFundamental (max lengthAmbient lengthEndpoint))
  refine ⟨length0, ?_, ?_⟩
  · dsimp [length0]
    omega
  · intro length hlength digit
    dsimp
    let X : Real := ((10 ^ length : Nat) : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let z : Real := X ^ (eta / 4)
    let z0 : Real := X ^ (epsilon ^ (4 : Nat))
    let rho : Real := restrictedDigitDensity digit
    let lambda : Real := rho * (A.card : Real) / X
    let a : Real := ((strictSiftedCarrier A z).card : Real)
    let b : Real :=
      ((strictSiftedCarrier (maynardAmbientCarrier X) z).card : Real)
    let b0 : Real :=
      ((strictSiftedCarrier (maynardAmbientCarrier X) z0).card : Real)
    let D : Finset Nat := maynardStrictRoughCarrier
      (X ^ (50 / 77 - epsilon)) z
    let residual : Nat -> Real := fun d =>
      |((strictSiftedCarrier
          (sieveDilation A d.toPNat') z).card : Real) -
        rho * (A.card : Real) / X *
          ((strictSiftedCarrier
            (sieveDilation (maynardAmbientCarrier X) d.toPNat')
            z).card : Real)|
    have hrest :
        max lengthFundamental (max lengthAmbient lengthEndpoint) <= length :=
      (Nat.le_max_right 1 _).trans hlength
    have hlengthFundamental' : lengthFundamental <= length :=
      (Nat.le_max_left _ _).trans hrest
    have hlengthAmbient' : lengthAmbient <= length :=
      (Nat.le_max_left _ _).trans
        ((Nat.le_max_right lengthFundamental _).trans hrest)
    have hlengthEndpoint' : lengthEndpoint <= length :=
      (Nat.le_max_right _ _).trans
        ((Nat.le_max_right lengthFundamental _).trans hrest)
    have hendpoint := hEndpoint length hlengthEndpoint'
    have hlengthOne : 1 <= length := hendpoint.1
    have hz0Five : 5 <= z0 := by
      simpa [z0, X] using hendpoint.2.1
    have hlogOne : 1 <= Real.log X := by
      simpa [X] using hendpoint.2.2
    have hX : 1 < X := by
      dsimp [X]
      exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
        (by norm_num : 1 < (10 : Nat))
    have hXpos : 0 < X := by linarith
    have hlogPos : 0 < Real.log X := by linarith
    have hetaQuarter : 0 < eta / 4 := by linarith
    have hz0z : z0 <= z := by
      dsimp [z0, z]
      exact Real.rpow_le_rpow_of_exponent_le hX.le hepsilonFourth
    have hzFive : 5 <= z := hz0Five.trans hz0z
    have halpha : 0 < 50 / 77 - epsilon := by
      linarith
    have houter : 1 < X ^ (50 / 77 - epsilon) :=
      Real.one_lt_rpow hX halpha
    have hunit : (1 : Nat) ∈ D := by
      dsimp [D]
      rw [mem_maynardStrictRoughCarrier]
      exact ⟨by norm_num, by exact_mod_cast houter,
        strictRoughPredicate_one _⟩
    have htoPNatOne : (1 : Nat).toPNat' = (1 : PNat) := by rfl
    have hsumBoundRaw :=
      hFundamental length hlengthFundamental' digit (eta / 4)
        hetaQuarter
    dsimp at hsumBoundRaw
    have hsumBoundRaw := hsumBoundRaw (by simpa [X, z] using hzFive)
    have hsumBound :
        (∑ d ∈ D, residual d) <=
          CF * (A.card : Real) *
              Real.exp (-((eta / 4) ^ (-(2 / 3 : Real)))) /
                Real.log X +
            CF * (A.card : Real) / Real.log X ^ (100 : Nat) := by
      simpa only [D, residual, A, X, z, rho] using hsumBoundRaw
    have hunitLeSum : residual 1 <= ∑ d ∈ D, residual d :=
      Finset.single_le_sum (f := residual)
        (fun d hd => by dsimp [residual]; exact abs_nonneg _) hunit
    have hunitValue : residual 1 = |a - lambda * b| := by
      dsimp [residual, a, lambda, b]
      rw [htoPNatOne, sieveDilation_one, sieveDilation_one]
    have hresidual :
        |a - lambda * b| <=
          CF * (A.card : Real) *
              Real.exp (-((eta / 4) ^ (-(2 / 3 : Real)))) /
                Real.log X +
            CF * (A.card : Real) / Real.log X ^ (100 : Nat) := by
      rw [← hunitValue]
      exact hunitLeSum.trans hsumBound
    have hb0Upper : b0 <= K * X / Real.log X := by
      have h := hAmbient length hlengthAmbient' 1 (by norm_num)
        (by simpa [X] using houter)
      rw [htoPNatOne, sieveDilation_one] at h
      simpa [b0, X, z0] using h
    have hbb0 : b <= b0 := by
      dsimp [b, b0]
      exact card_strictSiftedCarrier_threshold_le_real
        (maynardAmbientCarrier X) hz0z
    have hbUpper : b <= K * X / Real.log X := hbb0.trans hb0Upper
    have hrhoNonneg : 0 <= rho := by
      dsimp [rho]
      rw [restrictedDigitDensity_eq]
      split_ifs <;> norm_num
    have hrhoUpper : rho <= (10 / 9 : Real) := by
      dsimp [rho]
      rw [restrictedDigitDensity_eq]
      split_ifs <;> norm_num
    have hlambda : 0 <= lambda := by
      dsimp [lambda]
      positivity
    have hcorrectionInitial :
        lambda * b <= lambda * (K * X / Real.log X) :=
      mul_le_mul_of_nonneg_left hbUpper hlambda
    have hcorrectionRewrite :
        lambda * (K * X / Real.log X) =
          rho * K * (A.card : Real) / Real.log X := by
      dsimp [lambda]
      field_simp [hXpos.ne', hlogPos.ne']
    have hcorrection :
        lambda * b <=
          (10 / 9 : Real) * K * (A.card : Real) / Real.log X := by
      calc
        lambda * b <= lambda * (K * X / Real.log X) :=
          hcorrectionInitial
        _ = rho * K * (A.card : Real) / Real.log X :=
          hcorrectionRewrite
        _ <= (10 / 9 : Real) * K * (A.card : Real) /
              Real.log X := by
          rw [show rho * K * (A.card : Real) / Real.log X =
              rho * (K * (A.card : Real) / Real.log X) by ring]
          rw [show (10 / 9 : Real) * K * (A.card : Real) / Real.log X =
              (10 / 9 : Real) *
                (K * (A.card : Real) / Real.log X) by ring]
          exact mul_le_mul_of_nonneg_right hrhoUpper (by positivity)
    have hrapid :
        Real.exp (-((eta / 4) ^ (-(2 / 3 : Real)))) <= 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (neg_nonpos.mpr (Real.rpow_nonneg hetaQuarter.le _))
    have hfirstError :
        CF * (A.card : Real) *
              Real.exp (-((eta / 4) ^ (-(2 / 3 : Real)))) /
                Real.log X <=
          CF * (A.card : Real) / Real.log X := by
      apply (div_le_div_iff_of_pos_right hlogPos).2
      have hfactor : 0 <= CF * (A.card : Real) := by positivity
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hrapid hfactor)
    have hlogPower : Real.log X <= Real.log X ^ (100 : Nat) := by
      simpa only [pow_one] using
        (pow_le_pow_right₀ hlogOne (by norm_num : (1 : Nat) <= 100))
    have hsecondError :
        CF * (A.card : Real) / Real.log X ^ (100 : Nat) <=
          CF * (A.card : Real) / Real.log X := by
      exact div_le_div_of_nonneg_left (by positivity) hlogPos hlogPower
    have hresidualUpper :
        |a - lambda * b| <=
          2 * CF * (A.card : Real) / Real.log X := by
      calc
        |a - lambda * b| <=
            CF * (A.card : Real) *
                Real.exp (-((eta / 4) ^ (-(2 / 3 : Real)))) /
                  Real.log X +
              CF * (A.card : Real) / Real.log X ^ (100 : Nat) :=
          hresidual
        _ <= CF * (A.card : Real) / Real.log X +
              CF * (A.card : Real) / Real.log X :=
          add_le_add hfirstError hsecondError
        _ = 2 * CF * (A.card : Real) / Real.log X := by ring
    have haTriangle : a <= |a - lambda * b| + lambda * b := by
      linarith [le_abs_self (a - lambda * b)]
    have hfinal : a <= C * (A.card : Real) / Real.log X := by
      calc
        a <= |a - lambda * b| + lambda * b := haTriangle
        _ <= 2 * CF * (A.card : Real) / Real.log X +
              (10 / 9 : Real) * K * (A.card : Real) / Real.log X :=
          add_le_add hresidualUpper hcorrection
        _ = C * (A.card : Real) / Real.log X := by
          dsimp [C]
          ring
    simpa [a, A, X, z] using hfinal

end

end PrimesRestrictedDigits
