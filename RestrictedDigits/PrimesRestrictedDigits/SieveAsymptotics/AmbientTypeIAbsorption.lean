import PrimesRestrictedDigits.SieveAsymptotics.DecimalAmbientBoundingSieve
import PrimesRestrictedDigits.TypeI.ModulusAggregation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ambient Type-I carrier absorption

The elementary ambient progression error is bounded by ten for each Type-I modulus. This file
absorbs the resulting carrier cardinality into the `log(X)^(-100)` budget at decimal powers.
-/

open Filter Asymptotics

namespace PrimesRestrictedDigits

noncomputable section

private theorem eventually_fifty_log_pow_le_rpow :
    ∀ᶠ x : Real in atTop,
      50 * Real.log x ^ (100 : Nat) <= x ^ (27 / 77 : Real) := by
  have hbound :=
    (isLittleO_log_rpow_rpow_atTop (100 : Real)
      (by norm_num : (0 : Real) < 27 / 77)).bound
        (by norm_num : (0 : Real) < 1 / 50)
  filter_upwards [hbound, eventually_gt_atTop (1 : Real)] with x hgrowth hx
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hlogRpow : 0 < Real.log x ^ (100 : Real) :=
    Real.rpow_pos_of_pos hlog _
  have hxRpow : 0 < x ^ (27 / 77 : Real) :=
    Real.rpow_pos_of_pos hx0 _
  rw [Real.norm_of_nonneg hlogRpow.le,
    Real.norm_of_nonneg hxRpow.le] at hgrowth
  have heq : Real.log x ^ (100 : Real) =
      Real.log x ^ (100 : Nat) := Real.rpow_natCast _ _
  rw [heq] at hgrowth
  nlinarith

/-- Ten times the ambient Type-I modulus count is eventually absorbed by the
ambient coprime mass with saving `100`.  The constructed threshold is in fact
independent of `epsilon`; positivity is used only to enlarge the cutoff
exponent to `50/77`. -/
theorem exists_ambientTypeIModuli_card_threshold
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        let X : Real := ((10 ^ length : Nat) : Real)
        10 * ((typeIModuliBelow
            (X ^ (50 / 77 - epsilon / 2))).card : Real) <=
          ((maynardCoprimeAmbientCarrier X).card : Real) /
            Real.log X ^ (100 : Nat) := by
  let X : Nat -> Real := fun length => ((10 ^ length : Nat) : Real)
  have hXtendsto : Tendsto X atTop atTop := by
    simpa only [X, Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  obtain ⟨lengthPower, hPower⟩ := eventually_atTop.mp
    (hXtendsto.eventually eventually_fifty_log_pow_le_rpow)
  refine ⟨max 1 lengthPower, Nat.le_max_left _ _, ?_⟩
  intro length hlength
  dsimp
  let x : Real := ((10 ^ length : Nat) : Real)
  have hlengthOne : 1 <= length :=
    (Nat.le_max_left 1 lengthPower).trans hlength
  have hlengthPower : lengthPower <= length :=
    (Nat.le_max_right 1 lengthPower).trans hlength
  have hxNat : 1 < 10 ^ length :=
    Nat.one_lt_pow (by omega) (by norm_num)
  have hx : 1 < x := by
    dsimp [x]
    exact_mod_cast hxNat
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hlogPow : 0 < Real.log x ^ (100 : Nat) := pow_pos hlog _
  have hLogBound :
      50 * Real.log x ^ (100 : Nat) <= x ^ (27 / 77 : Real) := by
    simpa [X, x] using hPower length hlengthPower
  let Q : Real := x ^ (50 / 77 - epsilon / 2)
  have hQ0 : 0 <= Q := by
    dsimp [Q]
    positivity
  have hcardNat : (typeIModuliBelow Q).card <= Nat.ceil Q := by
    simpa [typeIModuliBelow] using
      Finset.card_filter_le (Finset.range (Nat.ceil Q))
        (fun q => Nat.Coprime q 10)
  have hcardCeil : ((typeIModuliBelow Q).card : Real) <=
      (Nat.ceil Q : Nat) := by
    exact_mod_cast hcardNat
  have hceil : ((Nat.ceil Q : Nat) : Real) < Q + 1 :=
    Nat.ceil_lt_add_one hQ0
  have hQle : Q <= x ^ (50 / 77 : Real) := by
    dsimp [Q]
    apply Real.rpow_le_rpow_of_exponent_le hx.le
    linarith
  have hbaseOne : 1 <= x ^ (50 / 77 : Real) :=
    Real.one_le_rpow hx.le (by norm_num)
  have hcard : ((typeIModuliBelow Q).card : Real) <=
      2 * x ^ (50 / 77 : Real) := by
    linarith
  have hpowProduct :
      x ^ (50 / 77 : Real) * x ^ (27 / 77 : Real) = x := by
    calc
      x ^ (50 / 77 : Real) * x ^ (27 / 77 : Real) =
          x ^ ((50 / 77 : Real) + 27 / 77) :=
        (Real.rpow_add hx0 _ _).symm
      _ = x ^ (1 : Real) := by norm_num
      _ = x := Real.rpow_one x
  have hscalar :
      10 * ((typeIModuliBelow Q).card : Real) *
          Real.log x ^ (100 : Nat) <=
        (2 / 5 : Real) * x := by
    calc
      _ <= 10 * (2 * x ^ (50 / 77 : Real)) *
          Real.log x ^ (100 : Nat) := by gcongr
      _ <= 10 * (2 * x ^ (50 / 77 : Real)) *
          (x ^ (27 / 77 : Real) / 50) := by
        gcongr
        nlinarith
      _ = (2 / 5 : Real) * x := by
        rw [show 10 * (2 * x ^ (50 / 77 : Real)) *
            (x ^ (27 / 77 : Real) / 50) =
          (2 / 5 : Real) *
            (x ^ (50 / 77 : Real) * x ^ (27 / 77 : Real)) by ring,
          hpowProduct]
  have hAmbient : ((maynardCoprimeAmbientCarrier x).card : Real) =
      (2 / 5 : Real) * x := by
    dsimp [x]
    rw [card_maynardCoprimeAmbientCarrier_powerTen_real_ratio
      (Nat.zero_lt_of_lt hlengthOne), card_maynardAmbientCarrier_natCast]
    have htotient : Nat.totient 10 = 4 := by decide
    rw [htotient]
    norm_num
  apply (le_div_iff₀ hlogPow).2
  change 10 * ((typeIModuliBelow Q).card : Real) *
      Real.log x ^ (100 : Nat) <=
    ((maynardCoprimeAmbientCarrier x).card : Real)
  rw [hAmbient]
  exact hscalar

end

end PrimesRestrictedDigits
