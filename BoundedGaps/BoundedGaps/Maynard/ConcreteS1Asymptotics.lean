import BoundedGaps.Maynard.ConcreteS1
import BoundedGaps.Maynard.ConcreteScaleBounds
import BoundedGaps.Maynard.AsymptoticEnvelopes

namespace BoundedGaps.Maynard

open Filter

set_option maxRecDepth 3000 in
theorem tendsto_engelsmaMaynardS1ExplicitEnvelope
    {alpha : ℝ} (halpha : 0 < alpha) (halphaQuarter : alpha < 1 / 4) :
    Tendsto
      (fun N : ℕ =>
        ((engelsmaMaynardRadius alpha N : ℝ) *
          (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
            Fintype.card BoundedGaps.engelsmaTuple) ^ 2 *
          ((engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
            (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
              (2 * Fintype.card BoundedGaps.engelsmaTuple)) ^ 2 /
            engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
  let eps : ℝ := (1 - 4 * alpha) / 212
  have heps : 0 < eps := by
    dsimp [eps]
    linarith
  have hexp : 4 * alpha + 106 * eps < 1 := by
    dsimp [eps]
    linarith
  have hscale := engelsmaMaynardScale_ge_rpow halpha heps
  have hscalePos := eventually_engelsmaMaynardScale_pos halpha
  have hNlarge : ∀ᶠ N : ℕ in atTop, 3 ≤ N := eventually_ge_atTop 3
  have hlogN : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    exact ht.eventually (eventually_ge_atTop 1)
  have hR : ∀ᶠ N : ℕ in atTop,
      (engelsmaMaynardRadius alpha N : ℝ) ≤ Real.rpow (N : ℝ) alpha := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    unfold engelsmaMaynardRadius maynardDivisorCutoff
    have hfloor :
        ((maynardDivisorCutoff alpha (N - 1) : ℕ) : ℝ) ≤
          Real.rpow ((N - 1 : ℕ) : ℝ) alpha := by
      unfold maynardDivisorCutoff
      exact Nat.floor_le (Real.rpow_nonneg (by positivity) alpha)
    have hsub : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.sub_le N 1
    exact hfloor.trans (Real.rpow_le_rpow (by positivity) hsub (le_of_lt halpha))
  have hlogR : ∀ᶠ N : ℕ in atTop,
      1 + Real.log (engelsmaMaynardRadius alpha N) ≤
        (1 + alpha) * Real.log (N : ℝ) := by
    filter_upwards [hR, hlogN, eventually_ge_atTop 2] with N hRN hLN hN
    have hlogbase : 0 ≤ Real.log (N : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ N by omega)
    by_cases hzero : engelsmaMaynardRadius alpha N = 0
    · simp [hzero]
      nlinarith [mul_nonneg (le_of_lt halpha) (by linarith : 0 ≤ Real.log (N : ℝ))]
    · have hRpos : 0 < (engelsmaMaynardRadius alpha N : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      have hlogmono : Real.log (engelsmaMaynardRadius alpha N) ≤
          Real.log (Real.rpow (N : ℝ) alpha) := by
        exact Real.strictMonoOn_log.monotoneOn
          (show (engelsmaMaynardRadius alpha N : ℝ) ∈ Set.Ioi 0 from hRpos)
          (show Real.rpow (N : ℝ) alpha ∈ Set.Ioi 0 from
            Real.rpow_pos_of_pos (by positivity) _)
          hRN
      have hlogpow : Real.log (Real.rpow (N : ℝ) alpha) =
          alpha * Real.log (N : ℝ) := by
        simpa using (Real.log_rpow (x := (N : ℝ)) (by positivity) alpha)
      rw [hlogpow] at hlogmono
      nlinarith
  let k : ℕ := Fintype.card BoundedGaps.engelsmaTuple
  let m : ℕ := 6 * k
  let C0 : ℝ := smallKCandidateBound ^ 2 * (1 + alpha) ^ (6 * k)
  have hANonneg : ∀ᶠ N : ℕ in atTop, 0 ≤
      1 + Real.log (engelsmaMaynardRadius alpha N) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    by_cases hz : engelsmaMaynardRadius alpha N = 0
    · simp [hz]
    · have hge : (1 : ℝ) ≤ (engelsmaMaynardRadius alpha N : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
      have hlognonneg : 0 ≤ Real.log (engelsmaMaynardRadius alpha N) :=
        Real.log_nonneg hge
      linarith
  have hClog_nonneg : ∀ᶠ N : ℕ in atTop, 0 ≤
      (1 + alpha) * Real.log (N : ℝ) := by
    filter_upwards [hlogN] with N hN
    positivity
  have hEbound : ∀ᶠ N : ℕ in atTop,
      ((engelsmaMaynardRadius alpha N : ℝ) *
          (1 + Real.log (engelsmaMaynardRadius alpha N)) ^ k) ^ 2 *
        ((engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
          (1 + Real.log (engelsmaMaynardRadius alpha N)) ^ (2 * k)) ^ 2 ≤
      C0 * (Real.rpow (N : ℝ) alpha) ^ 4 * (Real.log (N : ℝ)) ^ m := by
    filter_upwards [hR, hlogR, hANonneg, hClog_nonneg] with
      N hRN hLR hAnon hCnon
    have hpowA :
        (1 + Real.log (engelsmaMaynardRadius alpha N)) ^ k ≤
          ((1 + alpha) * Real.log (N : ℝ)) ^ k := by
      exact pow_le_pow_left₀ hAnon hLR k
    have hbase1 :
        (engelsmaMaynardRadius alpha N : ℝ) *
            (1 + Real.log (engelsmaMaynardRadius alpha N)) ^ k ≤
          Real.rpow (N : ℝ) alpha *
            ((1 + alpha) * Real.log (N : ℝ)) ^ k := by
      exact mul_le_mul hRN hpowA (pow_nonneg hAnon _)
        (Real.rpow_nonneg (by positivity) _)
    have hpow1 := pow_le_pow_left₀ (by positivity) hbase1 2
    have hpowA2 :
        (1 + Real.log (engelsmaMaynardRadius alpha N)) ^ (2 * k) ≤
          ((1 + alpha) * Real.log (N : ℝ)) ^ (2 * k) := by
      exact pow_le_pow_left₀ hAnon hLR (2 * k)
    have hbase2 :
        (engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
            (1 + Real.log (engelsmaMaynardRadius alpha N)) ^ (2 * k) ≤
          Real.rpow (N : ℝ) alpha * smallKCandidateBound *
            ((1 + alpha) * Real.log (N : ℝ)) ^ (2 * k) := by
      have hRB :
          (engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound ≤
            Real.rpow (N : ℝ) alpha * smallKCandidateBound :=
        mul_le_mul_of_nonneg_right hRN smallKCandidateBound_nonneg
      exact mul_le_mul hRB hpowA2 (pow_nonneg hAnon _)
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) smallKCandidateBound_nonneg)
    have hbase2_nonneg : 0 ≤
        (engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
          (1 + Real.log (engelsmaMaynardRadius alpha N)) ^ (2 * k) := by
      exact mul_nonneg
        (mul_nonneg (by positivity) smallKCandidateBound_nonneg)
        (by positivity)
    have hpow2 := pow_le_pow_left₀ hbase2_nonneg hbase2 2
    calc
      _ ≤ (Real.rpow (N : ℝ) alpha *
            ((1 + alpha) * Real.log (N : ℝ)) ^ k) ^ 2 *
          (Real.rpow (N : ℝ) alpha * smallKCandidateBound *
            ((1 + alpha) * Real.log (N : ℝ)) ^ (2 * k)) ^ 2 :=
        mul_le_mul hpow1 hpow2 (by positivity) (by positivity)
      _ = C0 * (Real.rpow (N : ℝ) alpha) ^ 4 *
          (Real.log (N : ℝ)) ^ m := by
        dsimp [C0, m]
        simp_rw [mul_pow]
        ring
  have hgeneric : Tendsto
      (fun N : ℕ => C0 * Real.rpow (N : ℝ) (4 * alpha + 106 * eps) *
        Real.rpow (Real.log (N : ℝ)) (m : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
    simpa [mul_assoc, mul_div_assoc] using
      (tendsto_natCast_rpow_mul_log_rpow_div
        (a := 4 * alpha + 106 * eps) (b := (m : ℝ)) hexp).const_mul C0
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hgeneric
  filter_upwards [hEbound, hscale, hscalePos, hlogN, eventually_ge_atTop 1] with
      N hEN hSN hSpos hLN hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hlowerpos : 0 < Real.rpow (N : ℝ) (1 - 106 * eps) :=
    Real.rpow_pos_of_pos hNpos _
  have hboundnonneg : 0 ≤
      C0 * (Real.rpow (N : ℝ) alpha) ^ 4 * (Real.log (N : ℝ)) ^ m := by
    dsimp [C0]
    positivity
  have hpow4 : (Real.rpow (N : ℝ) alpha) ^ 4 =
      Real.rpow (N : ℝ) (4 * alpha) := by
    calc
      (Real.rpow (N : ℝ) alpha) ^ 4 =
          (Real.rpow (N : ℝ) alpha) ^ (4 : ℝ) := by
            exact (Real.rpow_natCast (Real.rpow (N : ℝ) alpha) 4).symm
      _ = Real.rpow (N : ℝ) (alpha * (4 : ℝ)) :=
        (Real.rpow_mul (x := (N : ℝ)) hNpos.le alpha (4 : ℝ)).symm
      _ = Real.rpow (N : ℝ) (4 * alpha) := by
        congr 1
        ring
  have hlogpow : (Real.log (N : ℝ)) ^ m =
      Real.rpow (Real.log (N : ℝ)) (m : ℝ) := by
    exact (Real.rpow_natCast (Real.log (N : ℝ)) m).symm
  calc
    _ ≤ (C0 * (Real.rpow (N : ℝ) alpha) ^ 4 *
        (Real.log (N : ℝ)) ^ m) /
        engelsmaMaynardScale alpha N := by
      rw [abs_div, abs_of_nonneg (by positivity), abs_of_pos hSpos]
      apply div_le_div_of_nonneg_right hEN
      exact hSpos.le
    _ ≤ (C0 * (Real.rpow (N : ℝ) alpha) ^ 4 *
        (Real.log (N : ℝ)) ^ m) /
        Real.rpow (N : ℝ) (1 - 106 * eps) := by
      apply div_le_div_of_nonneg_left hboundnonneg hlowerpos
      exact hSN
    _ = C0 * Real.rpow (N : ℝ) (4 * alpha + 106 * eps) *
        Real.rpow (Real.log (N : ℝ)) (m : ℝ) / (N : ℝ) := by
      rw [hpow4, hlogpow]
      have hlowinv :
          (Real.rpow (N : ℝ) (1 - 106 * eps))⁻¹ =
            Real.rpow (N : ℝ) (-(1 - 106 * eps)) :=
        (Real.rpow_neg hNpos.le _).symm
      have hninv : (N : ℝ)⁻¹ = Real.rpow (N : ℝ) (-1) := by
        calc
          (N : ℝ)⁻¹ = (Real.rpow (N : ℝ) 1)⁻¹ := by
            congr 1
            exact (Real.rpow_one (N : ℝ)).symm
          _ = Real.rpow (N : ℝ) (-1) :=
            (Real.rpow_neg hNpos.le 1).symm
      simp only [div_eq_mul_inv, hlowinv, hninv]
      calc
        C0 * Real.rpow (N : ℝ) (4 * alpha) *
              Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              Real.rpow (N : ℝ) (-(1 - 106 * eps)) =
            C0 * Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              (Real.rpow (N : ℝ) (4 * alpha) *
                Real.rpow (N : ℝ) (-(1 - 106 * eps))) := by ring
        _ = C0 * Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              Real.rpow (N : ℝ) (4 * alpha + (-(1 - 106 * eps))) := by
          exact congrArg
            (fun t : ℝ => C0 * Real.rpow (Real.log (N : ℝ)) (m : ℝ) * t)
            (Real.rpow_add hNpos (4 * alpha) (-(1 - 106 * eps))).symm
        _ = C0 * Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              Real.rpow (N : ℝ) (4 * alpha + 106 * eps) *
              Real.rpow (N : ℝ) (-1) := by
          have hExp : 4 * alpha + (-(1 - 106 * eps)) =
              (4 * alpha + 106 * eps) + (-1) := by ring
          rw [hExp]
          simpa [mul_assoc] using congrArg
            (fun t : ℝ => C0 * Real.rpow (Real.log (N : ℝ)) (m : ℝ) * t)
            (Real.rpow_add hNpos (4 * alpha + 106 * eps) (-1))
        _ = C0 * Real.rpow (N : ℝ) (4 * alpha + 106 * eps) *
              Real.rpow (Real.log (N : ℝ)) (m : ℝ) *
              Real.rpow (N : ℝ) (-1) := by ring

end BoundedGaps.Maynard
