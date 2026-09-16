import PrimesRestrictedDigits.MajorArcs.M2Absorption
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Scalar thresholds for the Type II weak small-product tail

This file proves the sole asymptotic scalar input in Eq. (9.4): at decimal scales, the
exponential loss from the digit dimension eventually dominates `log X * log (log X)`.
-/

open Filter Asymptotics

namespace PrimesRestrictedDigits

noncomputable section

/-- The decimal restricted-digit exponent lies strictly between zero and
one. -/
theorem typeIIWeakSmallProductExponent_pos_lt_one :
    0 < Real.log (9 : Real) / Real.log (10 : Real) ∧
      Real.log (9 : Real) / Real.log (10 : Real) < 1 := by
  have hlogNine : 0 < Real.log (9 : Real) := Real.log_pos (by norm_num)
  have hlogTen : 0 < Real.log (10 : Real) := Real.log_pos (by norm_num)
  have hlt : Real.log (9 : Real) < Real.log (10 : Real) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  exact ⟨div_pos hlogNine hlogTen, (div_lt_one hlogTen).2 hlt⟩

/-- Cubic logarithmic growth gives the generic log-log tail absorption used
at decimal scales below. -/
private theorem exists_logLog_tail_absorption
    {c : Real} (hc : 0 < c) :
    ∃ X0 : Real, ∀ X : Real, X0 ≤ X →
      0 < Real.log (Real.log X) →
      X ^ (-(c / (Real.log (Real.log X)) ^ 2)) ≤
        (Real.log (Real.log X))⁻¹ / Real.log X := by
  let L : Real → Real := fun X => Real.log X
  have hX : Tendsto L atTop atTop := Real.tendsto_log_atTop
  have hcHalf : 0 < c / 2 := by positivity
  have hbound0 :=
    (isLittleO_log_rpow_rpow_atTop (3 : Real)
      (by norm_num : (0 : Real) < 1)).bound hcHalf
  have hevent : ∀ᶠ X : Real in atTop,
      1 < X ∧ Real.exp 1 ≤ L X ∧
        ‖Real.log (L X) ^ (3 : Real)‖ ≤
          (c / 2) * ‖L X ^ (1 : Real)‖ := by
    filter_upwards [eventually_gt_atTop (1 : Real),
      hX.eventually_ge_atTop (Real.exp 1),
      hX.eventually hbound0] with X hXone hlarge hpow
    exact ⟨hXone, hlarge, hpow⟩
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp hevent
  refine ⟨X0, ?_⟩
  intro X hXX hloglog
  have hlarge := hX0 X hXX
  have hXpos : 0 < X := zero_lt_one.trans hlarge.1
  have hLpos : 0 < L X := (Real.exp_pos 1).trans_le hlarge.2.1
  have huPos : 0 < Real.log (L X) := hloglog
  have hpow : Real.log (L X) ^ 3 ≤ (c / 2) * L X := by
    calc
      Real.log (L X) ^ 3 = Real.log (L X) ^ (3 : Real) :=
        (Real.rpow_natCast (Real.log (L X)) 3).symm
      _ = ‖Real.log (L X) ^ (3 : Real)‖ := by
        exact (Real.norm_of_nonneg
          (Real.rpow_nonneg huPos.le (3 : Real))).symm
      _ ≤ (c / 2) * ‖L X ^ (1 : Real)‖ := hlarge.2.2
      _ = (c / 2) * L X := by
        rw [Real.rpow_one, Real.norm_of_nonneg hLpos.le]
  have hscaled : 2 * Real.log (L X) ^ 3 ≤ c * L X := by
    nlinarith
  have hden : 0 < Real.log (L X) ^ 2 := sq_pos_of_pos huPos
  have hquot :
      2 * Real.log (L X) ≤ c * (L X / Real.log (L X) ^ 2) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hden).2
    calc
      2 * Real.log (L X) * Real.log (L X) ^ 2 =
          2 * Real.log (L X) ^ 3 := by ring
      _ ≤ c * L X := hscaled
  have hneg :
      -c * (L X / Real.log (L X) ^ 2) ≤
        -2 * Real.log (L X) := by
    linarith
  have hexp :
      Real.exp (-c * (L X / Real.log (L X) ^ 2)) ≤
        Real.exp (-2 * Real.log (L X)) :=
    Real.exp_le_exp.mpr hneg
  have hLpow :
      Real.exp (-2 * Real.log (L X)) = (L X) ^ (-2 : Real) := by
    rw [Real.rpow_def_of_pos hLpos]
    congr 1
    ring
  have hlogLe : Real.log (L X) ≤ L X := by
    have h := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hinv :
      (L X) ^ (-2 : Real) ≤ 1 / (L X * Real.log (L X)) := by
    rw [Real.rpow_neg hLpos.le, Real.rpow_two]
    rw [one_div]
    apply (inv_le_inv₀ (by positivity : 0 < (L X) ^ 2)
      (by positivity : 0 < L X * Real.log (L X))).2
    nlinarith [hlogLe]
  calc
    X ^ (-(c / Real.log (Real.log X) ^ 2)) =
        Real.exp (-c * (L X / Real.log (L X) ^ 2)) := by
      rw [Real.rpow_def_of_pos hXpos]
      dsimp [L]
      congr 1
      field_simp
    _ ≤ Real.exp (-2 * Real.log (L X)) := hexp
    _ = (L X) ^ (-2 : Real) := hLpow
    _ ≤ 1 / (L X * Real.log (L X)) := hinv
    _ = (Real.log (Real.log X))⁻¹ / Real.log X := by
      dsimp [L]
      field_simp

/-- One eventual decimal threshold supplies every scalar and endpoint fact
needed by the weak small-product carrier proof. -/
theorem exists_typeIIWeakSmallProductScaleThreshold :
    ∃ length0 : Nat, 1 ≤ length0 ∧
      ∀ length : Nat, length0 ≤ length →
        let XNat : Nat := 10 ^ length
        let X : Real := (XNat : Real)
        let delta : Real := majorArcM2LogLogDelta XNat
        let Y : Real := X ^ (1 - delta ^ 2)
        9 ≤ X ∧ 0 < delta ∧ delta ≤ 1 / 2 ∧
          3 ≤ Y ∧ Y < X ∧
            1 / X ^ ((Real.log (9 : Real) / Real.log (10 : Real)) *
                delta ^ 2) ≤
              delta / Real.log X := by
  let alpha : Real := Real.log (9 : Real) / Real.log (10 : Real)
  have halpha : 0 < alpha := by
    simpa only [alpha] using typeIIWeakSmallProductExponent_pos_lt_one.1
  obtain ⟨X0, hAbsorb⟩ := exists_logLog_tail_absorption halpha
  let scale : Nat → Real := fun length => ((10 ^ length : Nat) : Real)
  have hscale : Tendsto scale atTop atTop := by
    simpa only [scale, Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  have hlog : Tendsto (fun length => Real.log (scale length)) atTop atTop :=
    Real.tendsto_log_atTop.comp hscale
  have hloglog :
      Tendsto (fun length => Real.log (Real.log (scale length)))
        atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hevent : ∀ᶠ length : Nat in atTop,
      X0 ≤ scale length ∧
        2 ≤ Real.log (Real.log (scale length)) := by
    filter_upwards [hscale.eventually_ge_atTop X0,
      hloglog.eventually_ge_atTop 2] with length hX0 htwo
    exact ⟨hX0, htwo⟩
  obtain ⟨length1, hlength1⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 length1, le_max_left _ _, ?_⟩
  intro length hlength
  have hlengthPos : 1 ≤ length := (le_max_left 1 length1).trans hlength
  have hlarge := hlength1 length ((le_max_right 1 length1).trans hlength)
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let u : Real := Real.log (Real.log X)
  let delta : Real := majorArcM2LogLogDelta XNat
  let Y : Real := X ^ (1 - delta ^ 2)
  have hX0 : X0 ≤ X := by
    simpa only [scale, X, XNat] using hlarge.1
  have huTwo : 2 ≤ u := by
    simpa only [scale, u, X, XNat] using hlarge.2
  have huPos : 0 < u := by linarith
  have hXNatTen : 10 ≤ XNat := by
    dsimp only [XNat]
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 10) hlengthPos
  have hXTen : (10 : Real) ≤ X := by
    dsimp only [X]
    exact_mod_cast hXNatTen
  have hXNine : (9 : Real) ≤ X := by linarith
  have hXOne : (1 : Real) < X := by linarith
  have hdeltaEq : delta = u⁻¹ := by
    rfl
  have hdeltaPos : 0 < delta := by
    rw [hdeltaEq]
    exact inv_pos.mpr huPos
  have hdeltaHalf : delta ≤ 1 / 2 := by
    rw [hdeltaEq]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num : (0 : Real) < 2) huTwo
  have hexponentHalf : (1 / 2 : Real) ≤ 1 - delta ^ 2 := by
    nlinarith [sq_nonneg delta]
  have hroot : (3 : Real) ≤ X ^ (1 / 2 : Real) := by
    calc
      (3 : Real) = (9 : Real) ^ (1 / 2 : Real) := by norm_num
      _ ≤ X ^ (1 / 2 : Real) :=
        Real.rpow_le_rpow (by norm_num) hXNine (by norm_num)
  have hYThree : (3 : Real) ≤ Y := by
    exact hroot.trans <| by
      dsimp only [Y]
      exact Real.rpow_le_rpow_of_exponent_le hXOne.le hexponentHalf
  have hYLtX : Y < X := by
    have hexponentLt : 1 - delta ^ 2 < 1 := by
      nlinarith [sq_pos_of_pos hdeltaPos]
    dsimp only [Y]
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hXOne hexponentLt
  have hAbsorbAt := hAbsorb X hX0 huPos
  have hscalar :
      1 / X ^ (alpha * delta ^ 2) ≤ delta / Real.log X := by
    calc
      1 / X ^ (alpha * delta ^ 2) =
          X ^ (-(alpha / u ^ 2)) := by
        rw [one_div, ← Real.rpow_neg (zero_le_one.trans hXOne.le)]
        congr 1
        rw [hdeltaEq]
        field_simp [huPos.ne']
      _ ≤ u⁻¹ / Real.log X := by
        simpa only [u] using hAbsorbAt
      _ = delta / Real.log X := by rw [hdeltaEq]
  change 9 ≤ X ∧ 0 < delta ∧ delta ≤ 1 / 2 ∧
    3 ≤ Y ∧ Y < X ∧
      1 / X ^ ((Real.log (9 : Real) / Real.log (10 : Real)) *
          delta ^ 2) ≤ delta / Real.log X
  simpa only [alpha] using
    ⟨hXNine, hdeltaPos, hdeltaHalf, hYThree, hYLtX, hscalar⟩

end

end PrimesRestrictedDigits
