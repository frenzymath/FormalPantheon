import PrimesRestrictedDigits.SieveDecomposition.RoughBridge
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalSieveParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ambient strict-rough estimate for the large-delta reduction

For one fixed admissible epsilon, the ambient sifted carrier at the endpoint `X^(epsilon^4)`
is bounded pointwise by `X/(d*log X)`. The compact Buchstab constant is allowed to depend on
epsilon, as required by the source notation.
-/

open Filter

namespace PrimesRestrictedDigits

noncomputable section

private theorem largeDeltaAmbient_scalar_bound
    {delta0 C Y X d L LY omega : Real}
    (hdelta0 : 0 < delta0) (hC : 0 ≤ C)
    (hY : 0 ≤ Y) (hd : 0 < d) (hYeq : Y = X / d)
    (hL : 1 ≤ L) (hLY : delta0 * L ≤ LY)
    (homega : omega ≤ 1) :
    omega * Y / (delta0 * L) + C * (Y / LY ^ 2) ≤
      (delta0⁻¹ + C * delta0⁻¹ ^ 2) * (X / (d * L)) := by
  have hLYpos : 0 < LY := by
    have hdelta0L : 0 < delta0 * L := mul_pos hdelta0 (by linarith)
    exact hdelta0L.trans_le hLY
  have hdelta0Lpos : 0 < delta0 * L :=
    mul_pos hdelta0 (by linarith)
  have hLpos : 0 < L := by linarith
  have homegaY : omega * Y ≤ Y := by
    calc
      omega * Y ≤ 1 * Y := mul_le_mul_of_nonneg_right homega hY
      _ = Y := by ring
  have hmain0 : omega * Y / (delta0 * L) ≤ Y / (delta0 * L) :=
    div_le_div_of_nonneg_right homegaY (le_of_lt hdelta0Lpos)
  have hmainEq : Y / (delta0 * L) =
      delta0⁻¹ * (X / (d * L)) := by
    rw [hYeq]
    field_simp [hdelta0.ne', hd.ne', hLpos.ne']
  have hdeltaLsq : (delta0 * L) ^ (2 : Nat) <= LY ^ (2 : Nat) :=
    pow_le_pow_left₀ (mul_nonneg hdelta0.le hLpos.le) hLY 2
  have hLsq : L <= L ^ (2 : Nat) := by
    nlinarith
  have hdenomOrder : delta0 ^ (2 : Nat) * L <= LY ^ (2 : Nat) := by
    calc
      delta0 ^ (2 : Nat) * L <= delta0 ^ (2 : Nat) * L ^ (2 : Nat) := by
        gcongr
      _ = (delta0 * L) ^ (2 : Nat) := by ring
      _ <= LY ^ (2 : Nat) := hdeltaLsq
  have hdeltaSqLpos : 0 < delta0 ^ (2 : Nat) * L := by positivity
  have hrem0 : Y / LY ^ (2 : Nat) <=
      Y / (delta0 ^ (2 : Nat) * L) :=
    div_le_div_of_nonneg_left hY hdeltaSqLpos hdenomOrder
  have hremEq : Y / (delta0 ^ (2 : Nat) * L) =
      delta0⁻¹ ^ (2 : Nat) * (X / (d * L)) := by
    rw [hYeq]
    field_simp [hdelta0.ne', hd.ne', hLpos.ne']
  have hremBase : Y / LY ^ (2 : Nat) <=
      delta0⁻¹ ^ (2 : Nat) * (X / (d * L)) := hrem0.trans_eq hremEq
  have hrem : C * (Y / LY ^ (2 : Nat)) <=
      C * (delta0⁻¹ ^ (2 : Nat) * (X / (d * L))) :=
    mul_le_mul_of_nonneg_left hremBase hC
  calc
    omega * Y / (delta0 * L) + C * (Y / LY ^ 2) <=
        Y / (delta0 * L) +
          C * (delta0⁻¹ ^ (2 : Nat) * (X / (d * L))) := by
      exact add_le_add hmain0 hrem
    _ = (delta0⁻¹ + C * delta0⁻¹ ^ (2 : Nat)) *
          (X / (d * L)) := by
      rw [hmainEq]
      ring

/-
This module is kept at the fixed-epsilon quantifier order.
-/
theorem exists_largeDeltaAmbientSiftedCount_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1) :
    ∃ K : Real, 0 < K ∧
      ∃ length0 : Nat, 1 <= length0 ∧
        ∀ length : Nat, length0 <= length ->
          ∀ d : Nat, 1 <= d ->
            ((d : Real) <
              ((10 ^ length : Nat) : Real) ^ (50 / 77 - epsilon)) ->
            ((strictSiftedCarrier
                (sieveDilation
                  (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
                  d.toPNat')
                (((10 ^ length : Nat) : Real) ^ (epsilon ^ (4 : Nat)))).card : Real)
              <=
                K * ((10 ^ length : Nat) : Real) /
                  ((d : Real) *
                    Real.log ((10 ^ length : Nat) : Real)) := by
  let delta0 : Real := epsilon ^ (4 : Nat)
  let alpha : Real := 50 / 77 - epsilon
  have hdelta0 : 0 < delta0 := by
    dsimp [delta0]
    positivity
  have hepsilonOne : epsilon <= 1 := by
    linarith
  have hdelta0LeEpsilon : delta0 <= epsilon := by
    dsimp [delta0]
    have hepsilonCube : epsilon ^ (3 : Nat) <= (1 : Real) := by
      have h := pow_le_pow_left₀ (show 0 <= epsilon by linarith)
        hepsilonOne 3
      simpa using h
    calc
      epsilon ^ (4 : Nat) = epsilon * epsilon ^ (3 : Nat) := by ring
      _ <= epsilon * 1 := by
        exact mul_le_mul_of_nonneg_left hepsilonCube hepsilon.le
      _ = epsilon := by ring
  have hdelta0LeOne : delta0 <= 1 := hdelta0LeEpsilon.trans hepsilonOne
  have hU : (1 : Real) <= delta0⁻¹ := by
    rw [← one_div]
    exact (one_le_div hdelta0).2 hdelta0LeOne
  obtain ⟨Crough, hCrough, hrough⟩ :=
    exists_maynardStrictRoughCount_upper delta0⁻¹ hU
  let K : Real := delta0⁻¹ + Crough * delta0⁻¹ ^ (2 : Nat)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  let Xfun : Nat -> Real := fun length =>
    ((10 ^ length : Nat) : Real)
  have hXfunTendsto : Tendsto Xfun atTop atTop := by
    simpa only [Xfun, Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  have hpowTendsto :
      Tendsto (fun length : Nat => Xfun length ^ delta0) atTop atTop := by
    exact (tendsto_rpow_atTop hdelta0).comp hXfunTendsto
  have hlogTendsto :
      Tendsto (fun length : Nat => Real.log (Xfun length)) atTop atTop := by
    exact Real.tendsto_log_atTop.comp hXfunTendsto
  have hguards : ∀ᶠ length : Nat in atTop,
      1 <= length ∧ 5 <= Xfun length ^ delta0 ∧
        1 <= Real.log (Xfun length) := by
    filter_upwards [eventually_ge_atTop (1 : Nat),
      hpowTendsto.eventually_ge_atTop (5 : Real),
      hlogTendsto.eventually_ge_atTop (1 : Real)] with length hlen hy hlog
    exact ⟨hlen, hy, hlog⟩
  obtain ⟨lengthThreshold, hlengthThreshold⟩ :=
    eventually_atTop.mp hguards
  let length0 : Nat := max 1 lengthThreshold
  refine ⟨K, hK, length0, ?_, ?_⟩
  · dsimp [length0]
    exact Nat.le_max_left _ _
  · intro length hlength d hdOne hdCut
    let X : Real := ((10 ^ length : Nat) : Real)
    let y : Real := X ^ delta0
    let Y : Real := X / (d : Real)
    let u : Real := Real.log Y / Real.log y
    have hlengthThreshold' : lengthThreshold <= length := by
      exact (Nat.le_max_right 1 lengthThreshold).trans hlength
    have hguard := hlengthThreshold length hlengthThreshold'
    have hlengthOne : 1 <= length := hguard.1
    have hy5 : 5 <= y := by
      simpa [X, Xfun, y] using hguard.2.1
    have hlogXOne : 1 <= Real.log X := by
      simpa [X, Xfun] using hguard.2.2
    have hX : 1 < X := by
      dsimp [X]
      exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
        (by norm_num : 1 < (10 : Nat))
    have hXpos : 0 < X := by linarith
    have hdeltaAlpha : delta0 <= alpha := by
      have hdata := fundamentalSieve_smallParameter_data
        (X := X) (epsilon := epsilon) (delta := delta0) hX hepsilon
        hepsilonSmall hepsilonRosser hdelta0 le_rfl hy5
      dsimp at hdata
      exact hdata.2.2.2.2.2.2.2
    have hAlphaPos : 0 < alpha := lt_of_lt_of_le hdelta0 hdeltaAlpha
    have hAlphaSum : delta0 + alpha <= 1 := by
      dsimp [alpha]
      linarith [hdelta0LeEpsilon, hAlphaPos]
    have hdRone : (1 : Real) <= (d : Real) := by exact_mod_cast hdOne
    have hdRpos : 0 < (d : Real) := lt_of_lt_of_le zero_lt_one hdRone
    have hYpos : 0 < Y := by
      dsimp [Y]
      exact div_pos hXpos hdRpos
    have hYleX : Y <= X := by
      dsimp [Y]
      apply (div_le_iff₀ hdRpos).2
      nlinarith [mul_le_mul_of_nonneg_left hdRone hXpos.le]
    have hYcut : (d : Real) < X ^ alpha := by
      simpa [X, alpha] using hdCut
    have hmulCut : (d : Real) * y < X ^ alpha * y := by
      exact mul_lt_mul_of_pos_right hYcut (by positivity : 0 < y)
    have hpowAdd : X ^ alpha * y = X ^ (alpha + delta0) := by
      dsimp [y]
      rw [← Real.rpow_add hXpos]
    have hpowLe : X ^ (alpha + delta0) <= X := by
      have h := Real.rpow_le_rpow_of_exponent_le hX.le hAlphaSum
      simpa [Real.rpow_one, add_comm] using h
    have hmulX : (d : Real) * y < X := hmulCut.trans_le (hpowAdd ▸ hpowLe)
    have hyY : y < Y := by
      dsimp [Y]
      apply (lt_div_iff₀ hdRpos).2
      simpa [mul_comm] using hmulX
    have hyPos : 0 < y := by positivity
    have hlogyPos : 0 < Real.log y := Real.log_pos (by linarith [hy5])
    have hlogYge : Real.log y <= Real.log Y :=
      Real.log_le_log hyPos hyY.le
    have hlogYleX : Real.log Y <= Real.log X :=
      Real.log_le_log hYpos hYleX
    have hlogyEq : Real.log y = delta0 * Real.log X := by
      dsimp [y]
      rw [Real.log_rpow hXpos]
    have hdeltaLogLe : delta0 * Real.log X <= Real.log Y := by
      rw [← hlogyEq]
      exact hlogYge
    have huOne : 1 <= u := by
      dsimp [u]
      exact (one_le_div hlogyPos).2 hlogYge
    have huUpper : u <= delta0⁻¹ := by
      dsimp [u]
      apply (div_le_iff₀ hlogyPos).2
      calc
        Real.log Y <= Real.log X := hlogYleX
        _ = delta0⁻¹ * Real.log y := by
          rw [hlogyEq]
          field_simp [hdelta0.ne']
    have hparam : u = Real.log Y / Real.log y := by rfl
    have hcount := hrough Y y u hYpos (by linarith [hy5]) huOne huUpper hparam
    have homega : buchstabFunction u <= 1 :=
      (buchstabFunction_mem_Icc huOne).2
    have hscalar := largeDeltaAmbient_scalar_bound
      (delta0 := delta0) (C := Crough) (Y := Y) (X := X)
      (d := (d : Real)) (L := Real.log X) (LY := Real.log Y)
      (omega := buchstabFunction u) hdelta0 hCrough.le hYpos.le hdRpos
      (by rfl) hlogXOne hdeltaLogLe homega
    have hcountBound : (maynardStrictRoughCount Y y : Real) <=
        K * (X / ((d : Real) * Real.log X)) := by
      dsimp [K]
      rw [hlogyEq] at hcount
      exact hcount.trans hscalar
    have hdPNat : ((d.toPNat' : PNat) : Nat) = d := by
      rw [Nat.toPNat'_coe, if_pos (Nat.zero_lt_of_lt hdOne)]
    have hcard := card_strictSiftedCarrier_sieveDilation_maynardAmbientCarrier
      (X := X) (z := y) d.toPNat' (by linarith [hy5])
    have hcardBound :
        ((strictSiftedCarrier
            (sieveDilation (maynardAmbientCarrier X) d.toPNat') y).card : Real) <=
          K * (X / ((d : Real) * Real.log X)) := by
      rw [hcard]
      simpa [Y, hdPNat] using hcountBound
    have hcardBound' := hcardBound
    rw [show K * (X / ((d : Real) * Real.log X)) =
        K * X / ((d : Real) * Real.log X) by ring] at hcardBound'
    simpa [X, y, delta0] using hcardBound'

end

end PrimesRestrictedDigits
