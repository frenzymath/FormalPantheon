import PrimesRestrictedDigits.SieveAsymptotics.AmbientFundamentalSievePointwise
import PrimesRestrictedDigits.SieveAsymptotics.AmbientTypeIAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalErrorAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalRemainderBridge
import PrimesRestrictedDigits.SieveAsymptotics.RoughReciprocalBound
import PrimesRestrictedDigits.SieveAsymptotics.SourceFundamentalSieveAggregateBridges
import PrimesRestrictedDigits.BasicEstimates.PrimeProductBounds
import PrimesRestrictedDigits.SieveAsymptotics.RoughSmoothTypeIBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Corrected coprime ambient fundamental-sieve aggregate

This sums the ambient pointwise estimate for Maynard's Eq. (7.8).  The fixed
progression discrepancy is paid only after the injective rough/smooth product
reindexing, then absorbed by the ambient Type-I threshold.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_correctedAmbientFundamentalSplit :
    ∃ C : Real, 1 <= C ∧
      ∀ epsilon : Real, 0 < epsilon -> epsilon <= 1 / 64 ->
        2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1 ->
        ∃ length0 : Nat, 1 <= length0 ∧
          ∀ length : Nat, length0 <= length ->
            ∀ delta : Real, 0 < delta -> delta <= epsilon ^ (4 : Nat) ->
              let X : Real := ((10 ^ length : Nat) : Real)
              5 <= X ^ delta ->
              (∑ d ∈ maynardStrictRoughCarrier
                  (X ^ (50 / 77 - epsilon)) (X ^ delta),
                |((strictSiftedCarrier
                    (sieveDilation
                      (maynardCoprimeAmbientCarrier
                        ((10 ^ length : Nat) : Real)) d.toPNat')
                    (X ^ delta)).card : Real) -
                  ((maynardCoprimeAmbientCarrier
                    ((10 ^ length : Nat) : Real)).card : Real) /
                    (d : Real) * decimalExcludedPrimeProduct (X ^ delta)|) <=
                C * ((maynardCoprimeAmbientCarrier
                    ((10 ^ length : Nat) : Real)).card : Real) *
                    Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X +
                  C * ((maynardCoprimeAmbientCarrier
                    ((10 ^ length : Nat) : Real)).card : Real) /
                    Real.log X ^ (100 : Nat) := by
  obtain ⟨CPoint, hCPoint, hPoint⟩ :=
    exists_ambientFundamentalSieve_pointwise
  let KBase : Real := (5 / 2 : Real) * CPoint *
    Real.exp (16 / Real.log 2)
  let KRaw : Real := (Nat.factorial 26 : Real) * KBase
  let C : Real := max CPoint (KRaw + 1)
  have hC : 1 <= C := by
    exact hCPoint.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro epsilon hepsilon hepsilonSmall hepsilonRosser
  obtain ⟨lengthAmbient, hLengthAmbientOne, hLengthAmbientBound⟩ :=
    exists_ambientTypeIModuli_card_threshold epsilon hepsilon
  let length0 : Nat := max 1 lengthAmbient
  refine ⟨length0, ?_, ?_⟩
  · dsimp [length0]
    omega
  · intro length hlength delta hdelta hdeltaEpsilon
    dsimp
    intro hcutoff
    let X : Real := ((10 ^ length : Nat) : Real)
    let Bcard : Real :=
      ((maynardCoprimeAmbientCarrier ((10 ^ length : Nat) : Real)).card : Real)
    let D := maynardStrictRoughCarrier
      (X ^ (50 / 77 - epsilon)) (X ^ delta)
    let E := fundamentalSmoothModuli X epsilon delta
    let V : Real := decimalExcludedPrimeProduct (X ^ delta)
    let s : Real := epsilon / (2 * delta)
    have hlengthOne : 1 <= length := by
      exact (show 1 <= length0 by dsimp [length0]; omega).trans hlength
    have hXnat : 1 < 10 ^ length :=
      Nat.one_lt_pow (by omega) (by norm_num)
    have hX : 1 < X := by
      dsimp [X]
      exact_mod_cast hXnat
    have hBnonneg : 0 <= Bcard := by positivity
    have hpointSum :
        (∑ d ∈ D,
          |((strictSiftedCarrier
              (sieveDilation
                (maynardCoprimeAmbientCarrier
                  ((10 ^ length : Nat) : Real)) d.toPNat')
              (X ^ delta)).card : Real) -
            Bcard / (d : Real) * V|) <=
          ∑ d ∈ D,
            (ambientBoundingSieve length d.toPNat' (X ^ delta)).totalMass *
                (V / s * (CPoint * Real.exp (-s))) +
          ∑ d ∈ D, ∑ e ∈ E,
            |ambientSieveProgressionError length (d * e)| := by
      calc
        _ <= ∑ d ∈ D,
            ((ambientBoundingSieve length d.toPNat' (X ^ delta)).totalMass *
                (V / s * (CPoint * Real.exp (-s))) +
              ∑ e ∈ E, |ambientSieveProgressionError length (d * e)|) := by
          apply Finset.sum_le_sum
          intro d hd
          have hdCoercion := sourceFundamental_toPNat'_coe_of_mem hd
          have h := hPoint length d.toPNat'
            (X := X) (epsilon := epsilon) (delta := delta)
            hX hepsilon hepsilonSmall hepsilonRosser hdelta hdeltaEpsilon
            hcutoff
          simpa [D, E, Bcard, V, s, hdCoercion, X] using h
        _ = _ := by rw [Finset.sum_add_distrib]
    have hErrorPointwise :
        (∑ d ∈ D, ∑ e ∈ E,
          |ambientSieveProgressionError length (d * e)|) <=
          ∑ d ∈ D, ∑ e ∈ E, (10 : Real) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      have hdData := mem_maynardStrictRoughCarrier.mp hd
      have heData := mem_fundamentalSmoothModuli.mp he
      have hdTen := strictRoughPredicate_coprime_ten hcutoff hdData.2.2
      have he0 : e ≠ 0 := by
        intro heZero
        subst e
        norm_num [Nat.Coprime] at heData
      have hePos : 0 < e := Nat.pos_of_ne_zero he0
      have hqPos : 0 < d * e := Nat.mul_pos
        (Nat.pos_of_ne_zero (by omega)) hePos
      have hqTen : (d * e).Coprime 10 :=
        Nat.coprime_mul_iff_left.mpr ⟨hdTen, heData.2.1⟩
      exact ambientSieveProgressionError_abs_le hlengthOne hqPos hqTen
    have hInjectConst :
        (∑ d ∈ D, ∑ e ∈ E, (10 : Real)) <=
          ∑ q ∈ typeIModuliBelow
              (X ^ (50 / 77 - epsilon / 2)), (10 : Real) := by
      apply sum_rough_smooth_products_le_typeIModuliBelow
        (D := D) (E := E) (X := X) (epsilon := epsilon)
        (z := X ^ delta) (f := fun _ => (10 : Real))
        (by positivity : 0 < X) hcutoff
      · intro d hd
        exact (mem_maynardStrictRoughCarrier.mp hd).1
      · intro d hd
        exact (mem_maynardStrictRoughCarrier.mp hd).2.1
      · intro d hd
        exact (mem_maynardStrictRoughCarrier.mp hd).2.2
      · intro e he
        exact (mem_fundamentalSmoothModuli.mp he).1
      · intro e he
        exact (mem_fundamentalSmoothModuli.mp he).2.2
      · intro e he
        exact (mem_fundamentalSmoothModuli.mp he).2.1
      · intro q hq
        norm_num
    have hInject :
        (∑ d ∈ D, ∑ e ∈ E,
          |ambientSieveProgressionError length (d * e)|) <=
          ∑ q ∈ typeIModuliBelow
              (X ^ (50 / 77 - epsilon / 2)), (10 : Real) := by
      exact hErrorPointwise.trans hInjectConst
    have hRemBound :
        (∑ d ∈ D, ∑ e ∈ E,
          |ambientSieveProgressionError length (d * e)|) <=
          Bcard / Real.log X ^ (100 : Nat) := by
      have hAbsorb := hLengthAmbientBound length
        (show lengthAmbient <= length by
          exact (Nat.le_max_right 1 lengthAmbient).trans hlength)
      calc
        _ <= ∑ q ∈ typeIModuliBelow
              (X ^ (50 / 77 - epsilon / 2)), (10 : Real) := hInject
        _ = 10 * ((typeIModuliBelow
              (X ^ (50 / 77 - epsilon / 2))).card : Real) := by
          simp
          ring
        _ <= Bcard / Real.log X ^ (100 : Nat) := by
          simpa [X, Bcard] using hAbsorb
    have hdata := fundamentalSieve_smallParameter_data hX hepsilon
      hepsilonSmall hepsilonRosser hdelta hdeltaEpsilon hcutoff
    dsimp at hdata
    rcases hdata with ⟨hlevel, hz, _, hlarge, _, halpha, halphaOne,
      hdeltaAlpha⟩
    have hlog : 0 < Real.log X := Real.log_pos hX
    have hs : 0 < s := by
      dsimp [s]
      exact div_pos hepsilon (mul_pos (by norm_num) hdelta)
    have hV : 0 <= V := by
      dsimp [V]
      exact sourceFundamental_decimalExcludedPrimeProduct_nonneg hcutoff
    have hsumRaw := sum_inv_maynardStrictRoughCarrier_rpow_le
      (X := X) (delta := delta) (alpha := 50 / 77 - epsilon)
      hX hdelta hdeltaAlpha (by linarith : 2 <= X ^ delta)
    have hsumInv : (∑ d ∈ D, (d : Real)⁻¹) <=
        Real.exp (16 / Real.log 2) * delta⁻¹ ^ (16 : Nat) := by
      have hRatio : (50 / 77 - epsilon) / delta <= delta⁻¹ := by
        rw [← one_div]
        exact (div_le_div_iff_of_pos_right hdelta).2 halphaOne
      calc
        _ <= Real.exp (16 / Real.log 2) *
            ((50 / 77 - epsilon) / delta) ^ (16 : Nat) := by
          simpa [D] using hsumRaw
        _ <= _ := by
          gcongr
    have hEtaDrop :
        V / s * (CPoint * Real.exp (-s)) <=
          V * (CPoint * Real.exp (-s)) := by
      have hsOne : 1 <= s := by
        dsimp [s]
        have hK : Real.exp 5000 + 2 <= s := hlarge
        have hOne : (1 : Real) <= Real.exp 5000 + 2 := by
          have := Real.add_one_le_exp (5000 : Real)
          linarith
        linarith
      calc
        V / s * (CPoint * Real.exp (-s)) =
            V * (1 / s) * (CPoint * Real.exp (-s)) := by ring
        _ <= V * 1 * (CPoint * Real.exp (-s)) := by
          gcongr
          exact (div_le_iff₀ hs).2 (by simpa using hsOne)
        _ = _ := by ring
    have hMassEq :
        (∑ d ∈ D,
          (ambientBoundingSieve length d.toPNat' (X ^ delta)).totalMass *
            (V / s * (CPoint * Real.exp (-s)))) =
          Bcard * (V / s * (CPoint * Real.exp (-s))) *
            (∑ d ∈ D, (d : Real)⁻¹) := by
      calc
        _ = ∑ d ∈ D,
            (Bcard / (d : Real)) *
              (V / s * (CPoint * Real.exp (-s))) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdCoercion := sourceFundamental_toPNat'_coe_of_mem hd
          rw [ambientBoundingSieve_totalMass, hdCoercion]
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          ring
    have hMassBound :
        (∑ d ∈ D,
          (ambientBoundingSieve length d.toPNat' (X ^ delta)).totalMass *
            (V / s * (CPoint * Real.exp (-s)))) <=
          KBase * Bcard *
            (delta⁻¹ ^ (17 : Nat) * Real.exp (-epsilon / (2 * delta))) /
              Real.log X := by
      have hVBound := decimalExcludedPrimeProduct_rpow_le hX hdelta hcutoff
      rw [hMassEq]
      calc
        _ <= Bcard * (V * (CPoint * Real.exp (-s))) *
            (Real.exp (16 / Real.log 2) * delta⁻¹ ^ (16 : Nat)) := by
          gcongr
        _ <= Bcard * (5 / (2 * delta * Real.log X) *
              (CPoint * Real.exp (-s))) *
            (Real.exp (16 / Real.log 2) * delta⁻¹ ^ (16 : Nat)) := by
          gcongr
        _ = _ := by
          dsimp [KBase, s]
          field_simp [hdelta.ne', hlog.ne']
    have hMainAbs := epsilon_fourth_inv_pow_mass_div_log hepsilon
      hepsilonSmall hdelta hdeltaEpsilon hX
      (by positivity : 0 <= KBase * Bcard)
    have hTotal :
        (∑ d ∈ D,
          |((strictSiftedCarrier
              (sieveDilation
                (maynardCoprimeAmbientCarrier
                  ((10 ^ length : Nat) : Real)) d.toPNat')
              (X ^ delta)).card : Real) -
            Bcard / (d : Real) * V|) <=
          KRaw * Bcard *
              Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X +
            Bcard / Real.log X ^ (100 : Nat) := by
      calc
        _ <=
            (∑ d ∈ D,
              (ambientBoundingSieve length d.toPNat' (X ^ delta)).totalMass *
                (V / s * (CPoint * Real.exp (-s)))) +
              ∑ d ∈ D, ∑ e ∈ E,
                |ambientSieveProgressionError length (d * e)| := hpointSum
        _ <= KBase * Bcard *
              (delta⁻¹ ^ (17 : Nat) * Real.exp (-epsilon / (2 * delta))) /
                Real.log X + Bcard / Real.log X ^ (100 : Nat) := by
          exact add_le_add hMassBound hRemBound
        _ <= _ := by
          simpa [KRaw, mul_assoc, mul_comm, mul_left_comm] using
            add_le_add_right hMainAbs (Bcard / Real.log X ^ (100 : Nat))
    have hKRaw : KRaw <= C := by
      exact le_trans (le_add_of_nonneg_right (by norm_num))
        (le_max_right _ _)
    have hrapidNonneg : 0 <=
        Bcard * Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X := by
      positivity
    have htypeNonneg : 0 <= Bcard / Real.log X ^ (100 : Nat) := by
      positivity
    calc
      _ <= KRaw * Bcard *
            Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X +
          Bcard / Real.log X ^ (100 : Nat) := hTotal
      _ <= C * Bcard *
            Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X +
          C * Bcard / Real.log X ^ (100 : Nat) := by
        gcongr
        nlinarith [hC, hBnonneg]

end

end PrimesRestrictedDigits
