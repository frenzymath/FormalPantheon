import PrimesRestrictedDigits.SieveAsymptotics.SourceFundamentalSievePointwise
import PrimesRestrictedDigits.SieveAsymptotics.SourceFundamentalSieveAggregateBridges
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalErrorAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalRemainderBridge
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalTypeILevel
import PrimesRestrictedDigits.SieveAsymptotics.RoughReciprocalBound
import PrimesRestrictedDigits.BasicEstimates.PrimeProductBounds
import PrimesRestrictedDigits.TypeI.PropositionSevenOne
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Corrected source fundamental-sieve aggregate

This sums the pointwise coprime-source estimate over the strict rough outer carrier. The
ambient split and the large-delta branch are intentionally separate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_correctedSourceFundamentalSplit :
    ∃ C : Real, 1 <= C ∧
      ∀ epsilon : Real, 0 < epsilon -> epsilon <= 1 / 64 ->
        2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1 ->
        ∃ length0 : Nat, 1 <= length0 ∧
          ∀ length : Nat, length0 <= length ->
            ∀ (digit : Fin 10) (delta : Real),
              0 < delta -> delta <= epsilon ^ (4 : Nat) ->
              let X : Real := ((10 ^ length : Nat) : Real)
              5 <= X ^ delta ->
              (∑ d ∈ maynardStrictRoughCarrier
                  (X ^ (50 / 77 - epsilon)) (X ^ delta),
                |((strictSiftedCarrier
                      (sieveDilation
                        ((paddedRestrictedNumbers digit length).filter
                          (fun n => n.Coprime 10)) d.toPNat')
                      (X ^ delta)).card : Real) -
                    (typeIProgressionDensity digit : Real) *
                      ((paddedRestrictedNumbers digit length).card : Real) /
                        (d : Real) *
                      decimalExcludedPrimeProduct (X ^ delta)|) <=
                C * ((paddedRestrictedNumbers digit length).card : Real) *
                    Real.exp (-(delta ^ (-(2 / 3 : Real)))) /
                      Real.log X +
                  C * ((paddedRestrictedNumbers digit length).card : Real) /
                    Real.log X ^ (100 : Nat) := by
  obtain ⟨CPoint, hCPoint, hPoint⟩ :=
    exists_sourceFundamentalSieve_pointwise
  obtain ⟨lengthType, hType⟩ :=
    exists_typeIProgressionEstimate (100 : Real) (by norm_num)
  let KType : Real := 4 * (26400 * largeSieveConstant + 720)
  let KRaw : Real :=
    (Nat.factorial 26 : Real) * (5 / 2 : Real) * CPoint *
      Real.exp (16 / Real.log 2)
  let C : Real := max CPoint (max KType (KRaw + 1))
  have hC : 1 <= C := by
    have hCPointOne : 1 <= CPoint := hCPoint
    exact hCPointOne.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro epsilon hepsilon hepsilonSmall hepsilonRosser
  obtain ⟨lengthPower, hPower⟩ :=
    exists_fundamentalTypeILevel_threshold epsilon hepsilon
  let length0 : Nat := max 1 (max lengthType lengthPower)
  refine ⟨length0, ?_, ?_⟩
  · dsimp [length0]
    omega
  · intro length hlength digit delta hdelta hdeltaEpsilon
    dsimp
    intro hcutoff
    let X : Real := ((10 ^ length : Nat) : Real)
    have hlengthOne : 1 <= length := by
      have hOne : 1 <= length0 := by
        dsimp [length0]
        omega
      exact hOne.trans hlength
    have hXnat : 1 < 10 ^ length := by
      exact Nat.one_lt_pow (by omega) (by norm_num)
    have hX : 1 < X := by
      dsimp [X]
      exact_mod_cast hXnat
    have hlengthType : lengthType <= length := by
      have hMax : lengthType <= max lengthType lengthPower :=
        Nat.le_max_left _ _
      exact hMax.trans (show max lengthType lengthPower <= length by
        exact (Nat.le_max_right 1 (max lengthType lengthPower)).trans hlength)
    have hlengthPower : lengthPower <= length := by
      have hMax : lengthPower <= max lengthType lengthPower :=
        Nat.le_max_right _ _
      exact hMax.trans (show max lengthType lengthPower <= length by
        exact (Nat.le_max_right 1 (max lengthType lengthPower)).trans hlength)
    have hLevel := hPower length hlengthPower
    have hQ :
        X ^ (50 / 77 - epsilon / 2) <=
          X ^ (50 / 77 : Real) *
            Real.log X ^ (-2 * (100 : Real) - 2) := by
      simpa [X] using hLevel
    have hTypeBound := hType length hlengthType digit
      (X ^ (50 / 77 - epsilon / 2)) hQ
    have hTypeNorm :
        (∑ q ∈ typeIModuliBelow (X ^ (50 / 77 - epsilon / 2)),
          |realTypeIProgressionError digit length q|) <=
          KType * ((paddedRestrictedNumbers digit length).card : Real) *
            Real.log X ^ (-100 : Real) := by
      have hTypeExpanded := sourceFundamental_typeI_sum_normalized
        (length0 := lengthType) (length := length) hlengthType digit
        (X ^ (50 / 77 - epsilon / 2)) hQ
        (by
          intro l hl d Q hQ'
          exact hType l hl d Q hQ')
      simpa [KType, X] using hTypeExpanded
    have hTypeNormNat :
        (∑ q ∈ typeIModuliBelow (X ^ (50 / 77 - epsilon / 2)),
          |realTypeIProgressionError digit length q|) <=
          KType * ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X ^ (100 : Nat) := by
      have hlog : 0 < Real.log X := Real.log_pos hX
      have hpow : Real.log X ^ (-100 : Real) =
          (Real.log X ^ (100 : Nat))⁻¹ := by
        rw [Real.rpow_neg hlog.le]
        exact congrArg Inv.inv (Real.rpow_natCast (Real.log X) 100)
      rw [hpow] at hTypeNorm
      simpa [KType, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
        using hTypeNorm
    have hRem := sum_abs_fundamentalRemainders_le_typeI digit length
      (X := X) (epsilon := epsilon) (delta := delta)
      (by positivity : 0 < X) hcutoff
    have hRemainder :
        (∑ d ∈ maynardStrictRoughCarrier
            (X ^ (50 / 77 - epsilon)) (X ^ delta),
          ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
            |realTypeIProgressionError digit length (d * e)|) <=
          KType * ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X ^ (100 : Nat) := by
      exact hRem.trans hTypeNormNat
    let D := maynardStrictRoughCarrier
      (X ^ (50 / 77 - epsilon)) (X ^ delta)
    have hDMain :
        (∑ d ∈ D,
          |((strictSiftedCarrier
                (sieveDilation
                  ((paddedRestrictedNumbers digit length).filter
                    (fun n => n.Coprime 10)) d.toPNat')
                (X ^ delta)).card : Real) -
            (typeIProgressionDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real) /
                (d : Real) * decimalExcludedPrimeProduct (X ^ delta)|) <=
        ∑ d ∈ D,
          (sourceBoundingSieve digit length d.toPNat' (X ^ delta)).totalMass *
              (decimalExcludedPrimeProduct (X ^ delta) /
                  (epsilon / (2 * delta)) *
                (CPoint * Real.exp (-(epsilon / (2 * delta))))) +
            ∑ d ∈ D, ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
              |realTypeIProgressionError digit length (d * e)| := by
      calc
        _ <= ∑ d ∈ D,
            ((sourceBoundingSieve digit length d.toPNat' (X ^ delta)).totalMass *
                (decimalExcludedPrimeProduct (X ^ delta) /
                    (epsilon / (2 * delta)) *
                  (CPoint * Real.exp (-(epsilon / (2 * delta))))) +
              ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
                |realTypeIProgressionError digit length (d * e)|) := by
          apply Finset.sum_le_sum
          intro d hd
          have hdCoercion := sourceFundamental_toPNat'_coe_of_mem hd
          have h := hPoint digit length d.toPNat'
            (X := X) (epsilon := epsilon) (delta := delta)
            hX hepsilon hepsilonSmall hepsilonRosser hdelta hdeltaEpsilon
            hcutoff
          simpa [D, hdCoercion, X] using h
        _ = _ := by rw [Finset.sum_add_distrib]
    have hDRem :
        (∑ d ∈ D, ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
          |realTypeIProgressionError digit length (d * e)|) <=
          KType * ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X ^ (100 : Nat) := by
      simpa [D] using hRemainder
    have hDensity := sourceFundamental_typeIProgressionDensity_bounds digit
    have hMassMain :
        (∑ d ∈ D,
          (sourceBoundingSieve digit length d.toPNat' (X ^ delta)).totalMass *
              (decimalExcludedPrimeProduct (X ^ delta) /
                  (epsilon / (2 * delta)) *
                (CPoint * Real.exp (-(epsilon / (2 * delta))))) ) <=
          ((5 / 2 : Real) * CPoint *
              Real.exp (16 / Real.log 2)) *
            ((paddedRestrictedNumbers digit length).card : Real) *
              (delta⁻¹ ^ (17 : Nat) *
                Real.exp (-epsilon / (2 * delta))) / Real.log X := by
      have hdata := fundamentalSieve_smallParameter_data hX hepsilon
        hepsilonSmall hepsilonRosser hdelta hdeltaEpsilon hcutoff
      dsimp at hdata
      rcases hdata with ⟨hlevel, hz, _, hlarge, _, halpha, halphaOne,
        hdeltaAlpha⟩
      have hlog : 0 < Real.log X := Real.log_pos hX
      have hs : 0 < epsilon / (2 * delta) :=
        div_pos hepsilon (mul_pos (by norm_num) hdelta)
      have hV : 0 <= decimalExcludedPrimeProduct (X ^ delta) :=
        sourceFundamental_decimalExcludedPrimeProduct_nonneg hcutoff
      have hEta : 0 <=
          decimalExcludedPrimeProduct (X ^ delta) /
              (epsilon / (2 * delta)) *
            (CPoint * Real.exp (-(epsilon / (2 * delta)))) := by
        positivity
      have hKrough : 0 <= Real.exp (16 / Real.log 2) := by positivity
      have hsumRaw := sum_inv_maynardStrictRoughCarrier_rpow_le
        (X := X) (delta := delta) (alpha := 50 / 77 - epsilon)
        hX hdelta hdeltaAlpha (by linarith : 2 <= X ^ delta)
      have hRatio := fundamentalSieve_roughRatio_pow_le hdelta halpha
        halphaOne
      have hsumInv :
          (∑ d ∈ D, (d : Real)⁻¹) <=
            Real.exp (16 / Real.log 2) * delta⁻¹ ^ (16 : Nat) := by
        calc
          (∑ d ∈ D, (d : Real)⁻¹) <=
              Real.exp (16 / Real.log 2) *
                ((50 / 77 - epsilon) / delta) ^ (16 : Nat) := by
            simpa [D] using hsumRaw
          _ <= Real.exp (16 / Real.log 2) * delta⁻¹ ^ (16 : Nat) := by
            gcongr
      have hMassTerm :
          (∑ d ∈ D,
            (sourceBoundingSieve digit length d.toPNat' (X ^ delta)).totalMass *
                (decimalExcludedPrimeProduct (X ^ delta) /
                    (epsilon / (2 * delta)) *
                  (CPoint * Real.exp (-(epsilon / (2 * delta)))))) <=
            ((paddedRestrictedNumbers digit length).card : Real) *
              (decimalExcludedPrimeProduct (X ^ delta) /
                  (epsilon / (2 * delta)) *
                (CPoint * Real.exp (-(epsilon / (2 * delta))))) *
              (∑ d ∈ D, (d : Real)⁻¹) := by
        calc
          _ <= ∑ d ∈ D,
              ((paddedRestrictedNumbers digit length).card : Real) *
                (decimalExcludedPrimeProduct (X ^ delta) /
                    (epsilon / (2 * delta)) *
                  (CPoint * Real.exp (-(epsilon / (2 * delta))))) *
                (d : Real)⁻¹ := by
            apply Finset.sum_le_sum
            intro d hd
            have hdCoercion := sourceFundamental_toPNat'_coe_of_mem hd
            have hd0 : 0 < d := by
              exact lt_of_lt_of_le Nat.zero_lt_one
                (mem_maynardStrictRoughCarrier.mp hd).1
            have hmassLe :
                (sourceBoundingSieve digit length d.toPNat' (X ^ delta)).totalMass <=
                  ((paddedRestrictedNumbers digit length).card : Real) *
                    (d : Real)⁻¹ := by
              rw [sourceBoundingSieve_totalMass, hdCoercion]
              have hA : 0 <=
                  ((paddedRestrictedNumbers digit length).card : Real) := by
                positivity
              have hkA :
                  (typeIProgressionDensity digit : Real) *
                      ((paddedRestrictedNumbers digit length).card : Real) <=
                    ((paddedRestrictedNumbers digit length).card : Real) := by
                have hmul := mul_le_mul_of_nonneg_right hDensity.2 hA
                simpa using hmul
              calc
                (typeIProgressionDensity digit : Real) *
                      ((paddedRestrictedNumbers digit length).card : Real) /
                    (d : Real) <=
                    ((paddedRestrictedNumbers digit length).card : Real) /
                      (d : Real) := by
                  exact (div_le_div_iff_of_pos_right (by exact_mod_cast hd0)).2
                    hkA
                _ = ((paddedRestrictedNumbers digit length).card : Real) *
                    (d : Real)⁻¹ := by rw [div_eq_mul_inv]
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              mul_le_mul_of_nonneg_right hmassLe hEta
          _ = _ := by
            rw [Finset.mul_sum]
      have hMassBound :
          (∑ d ∈ D,
            (sourceBoundingSieve digit length d.toPNat' (X ^ delta)).totalMass *
                (decimalExcludedPrimeProduct (X ^ delta) /
                    (epsilon / (2 * delta)) *
                  (CPoint * Real.exp (-(epsilon / (2 * delta)))))) <=
            ((paddedRestrictedNumbers digit length).card : Real) *
              (decimalExcludedPrimeProduct (X ^ delta) /
                  (epsilon / (2 * delta)) *
                (CPoint * Real.exp (-(epsilon / (2 * delta))))) *
              (Real.exp (16 / Real.log 2) * delta⁻¹ ^ (16 : Nat)) := by
        exact hMassTerm.trans
          (mul_le_mul_of_nonneg_left hsumInv (by positivity))
      have hEtaDrop :
          decimalExcludedPrimeProduct (X ^ delta) /
              (epsilon / (2 * delta)) *
            (CPoint * Real.exp (-(epsilon / (2 * delta)))) <=
          decimalExcludedPrimeProduct (X ^ delta) *
            (CPoint * Real.exp (-(epsilon / (2 * delta)))) := by
        have hsOne : 1 <= epsilon / (2 * delta) := by
          have hKLower : (1 : Real) <= Real.exp 5000 + 2 := by
            have := Real.add_one_le_exp (5000 : Real)
            linarith
          linarith
        calc
          _ = decimalExcludedPrimeProduct (X ^ delta) *
                (1 / (epsilon / (2 * delta))) *
                (CPoint * Real.exp (-(epsilon / (2 * delta)))) := by ring
          _ <= decimalExcludedPrimeProduct (X ^ delta) * 1 *
                (CPoint * Real.exp (-(epsilon / (2 * delta)))) := by
            gcongr
            exact (div_le_iff₀ hs).2 (by simpa using hsOne)
          _ = _ := by ring
      have hDropped :
          ((paddedRestrictedNumbers digit length).card : Real) *
              (decimalExcludedPrimeProduct (X ^ delta) /
                  (epsilon / (2 * delta)) *
                (CPoint * Real.exp (-(epsilon / (2 * delta))))) *
              (Real.exp (16 / Real.log 2) * delta⁻¹ ^ (16 : Nat)) <=
            ((paddedRestrictedNumbers digit length).card : Real) *
              (decimalExcludedPrimeProduct (X ^ delta) *
                (CPoint * Real.exp (-(epsilon / (2 * delta))))) *
              (Real.exp (16 / Real.log 2) * delta⁻¹ ^ (16 : Nat)) := by
        gcongr
      have hVBound := sourceFundamental_decimalExcludedPrimeProduct_mul_inv_le hX hdelta
        hcutoff
      calc
        _ <=
            ((paddedRestrictedNumbers digit length).card : Real) *
              (decimalExcludedPrimeProduct (X ^ delta) *
                (CPoint * Real.exp (-(epsilon / (2 * delta))))) *
              (Real.exp (16 / Real.log 2) * delta⁻¹ ^ (16 : Nat)) :=
          hMassBound.trans hDropped
        _ <=
            ((paddedRestrictedNumbers digit length).card : Real) *
              (5 / (2 * delta * Real.log X) *
                (CPoint * Real.exp (-(epsilon / (2 * delta))))) *
              (Real.exp (16 / Real.log 2) * delta⁻¹ ^ (16 : Nat)) := by
          gcongr
        _ = ((5 / 2 : Real) * CPoint *
              Real.exp (16 / Real.log 2)) *
            ((paddedRestrictedNumbers digit length).card : Real) *
              (delta⁻¹ ^ (17 : Nat) *
                Real.exp (-epsilon / (2 * delta))) / Real.log X := by
          field_simp [hdelta.ne', hlog.ne']
    have hTotal :
        (∑ d ∈ D,
          |((strictSiftedCarrier
                (sieveDilation
                  ((paddedRestrictedNumbers digit length).filter
                    (fun n => n.Coprime 10)) d.toPNat')
                (X ^ delta)).card : Real) -
            (typeIProgressionDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real) /
                (d : Real) * decimalExcludedPrimeProduct (X ^ delta)|) <=
          ((Nat.factorial 26 : Real) * (5 / 2 : Real) * CPoint *
              Real.exp (16 / Real.log 2)) *
            ((paddedRestrictedNumbers digit length).card : Real) *
              Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X +
            KType * ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log X ^ (100 : Nat) := by
      have hAbs := epsilon_fourth_inv_pow_mass_div_log hepsilon
        hepsilonSmall hdelta hdeltaEpsilon hX
        (by positivity : 0 <=
          ((5 / 2 : Real) * CPoint * Real.exp (16 / Real.log 2)) *
            ((paddedRestrictedNumbers digit length).card : Real))
      have hMainAbs := hMassMain
      have hRem' := hDRem
      calc
        _ <=
            ∑ d ∈ D,
              (sourceBoundingSieve digit length d.toPNat' (X ^ delta)).totalMass *
                (decimalExcludedPrimeProduct (X ^ delta) /
                    (epsilon / (2 * delta)) *
                  (CPoint * Real.exp (-(epsilon / (2 * delta))))) +
              ∑ d ∈ D, ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
                |realTypeIProgressionError digit length (d * e)| := hDMain
        _ <=
            ((5 / 2 : Real) * CPoint * Real.exp (16 / Real.log 2)) *
              ((paddedRestrictedNumbers digit length).card : Real) *
                (delta⁻¹ ^ (17 : Nat) *
                  Real.exp (-epsilon / (2 * delta))) / Real.log X +
              KType * ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log X ^ (100 : Nat) := by
          exact add_le_add hMainAbs hRem'
        _ <=
            ((Nat.factorial 26 : Real) * (5 / 2 : Real) * CPoint *
                Real.exp (16 / Real.log 2)) *
              ((paddedRestrictedNumbers digit length).card : Real) *
                Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X +
              KType * ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log X ^ (100 : Nat) := by
          have hAbs' := hAbs
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            add_le_add_right hAbs'
              (KType * ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log X ^ (100 : Nat))
    have hCraw :
        (Nat.factorial 26 : Real) * (5 / 2 : Real) * CPoint *
            Real.exp (16 / Real.log 2) <= C := by
      have hRaw : KRaw <= KRaw + 1 := by linarith
      have hInner : KRaw + 1 <= max KType (KRaw + 1) :=
        le_max_right _ _
      have hOuter : max KType (KRaw + 1) <= C := by
        change max KType (KRaw + 1) <=
          max CPoint (max KType (KRaw + 1))
        exact le_max_right _ _
      have hKRaw : KRaw <= C := hRaw.trans (hInner.trans hOuter)
      simpa [KRaw] using hKRaw
    have hCtype : KType <= C := by
      exact le_trans (le_max_left KType (KRaw + 1))
        (le_max_right CPoint (max KType (KRaw + 1)))
    have hrapidNonneg : 0 <=
        ((paddedRestrictedNumbers digit length).card : Real) *
          Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X := by
      positivity
    have htypeNonneg : 0 <=
        ((paddedRestrictedNumbers digit length).card : Real) /
          Real.log X ^ (100 : Nat) := by positivity
    calc
      _ <=
          ((Nat.factorial 26 : Real) * (5 / 2 : Real) * CPoint *
              Real.exp (16 / Real.log 2)) *
            ((paddedRestrictedNumbers digit length).card : Real) *
              Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X +
            KType * ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log X ^ (100 : Nat) := hTotal
      _ <= C * ((paddedRestrictedNumbers digit length).card : Real) *
            Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X +
          C * ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X ^ (100 : Nat) := by
        gcongr

end

end PrimesRestrictedDigits
