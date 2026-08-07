import BoundedGaps.Maynard.ConcreteParameters
import BoundedGaps.Maynard.AsymptoticEnvelopes

/-!
# Lower bounds for the frozen Maynard scale

The subpower primorial estimate from Maynard2013v3, Section 5 and source
lines 193--216, is combined with the exact definition of the normalized sieve
scale. Only the elementary lower bounds `phi(W) >= 1` and `log R >= 1` are
needed here.
-/

namespace BoundedGaps.Maynard

open Filter

theorem engelsmaMaynardModulus_le_rpow
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop,
      (engelsmaMaynardModulus N : ℝ) ≤ Real.rpow (N : ℝ) eps := by
  have hbase := eventually_primorial_tripleLogCutoff_le_rpow heps
  have hshift := (tendsto_sub_atTop_nat 1).eventually hbase
  filter_upwards [hshift, eventually_ge_atTop 2] with N hNshift hN2
  have hle : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.sub_le N 1
  change (primorial (tripleLogCutoff (N - 1)) : ℝ) ≤ _
  exact hNshift.trans
    (Real.rpow_le_rpow (by positivity) hle (le_of_lt heps))

theorem engelsmaMaynardScale_ge_rpow
    {alpha eps : ℝ} (halpha : 0 < alpha) (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop,
      Real.rpow (N : ℝ) (1 - 106 * eps) ≤ engelsmaMaynardScale alpha N := by
  have hW := engelsmaMaynardModulus_le_rpow heps
  have hreal : Tendsto
      (fun N : ℕ => engelsmaMaynardRealRadius alpha N) atTop atTop := by
    unfold engelsmaMaynardRealRadius maynardRealCutoff
    apply (tendsto_rpow_atTop halpha).comp
    exact tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
  have hlog : ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (engelsmaMaynardRealRadius alpha N) := by
    filter_upwards [hreal.eventually (eventually_ge_atTop (Real.exp 1))] with N hN
    have hlogmono : Real.log (Real.exp 1) ≤
        Real.log (engelsmaMaynardRealRadius alpha N) := by
      exact Real.strictMonoOn_log.monotoneOn
        (show Real.exp 1 ∈ Set.Ioi (0 : ℝ) from Real.exp_pos 1)
        (by exact lt_of_lt_of_le (by positivity) hN)
        hN
    simpa [Real.log_exp] using hlogmono
  filter_upwards [hW, hlog, eventually_ge_atTop 1] with N hW hlog hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hWpos : 0 < engelsmaMaynardModulus N := primorial_pos _
  have hphi : 1 ≤ (Nat.totient (engelsmaMaynardModulus N) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.totient_pos.mpr hWpos))
  have hRlog : 1 ≤ Real.log (engelsmaMaynardRealRadius alpha N) := hlog
  unfold engelsmaMaynardScale maynardSieveScale
  have hpowW :
      (engelsmaMaynardModulus N : ℝ) ^ (106 : ℕ) ≤
        (Real.rpow (N : ℝ) eps) ^ (106 : ℕ) := by
    exact pow_le_pow_left₀ (by positivity) hW 106
  have hnum : (N : ℝ) ≤
      (Nat.totient (engelsmaMaynardModulus N) : ℝ) ^ 105 * (N : ℝ) *
        (Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105 := by
    calc
      (N : ℝ) = 1 * (N : ℝ) * 1 := by ring
      _ ≤ (Nat.totient (engelsmaMaynardModulus N) : ℝ) ^ 105 *
          (N : ℝ) * (Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105 := by
        gcongr
        · exact one_le_pow₀ hphi
        · exact one_le_pow₀ hRlog
  have hdiv :
      (N : ℝ) / (Real.rpow (N : ℝ) eps) ^ 106 ≤
        ((Nat.totient (engelsmaMaynardModulus N) : ℝ) ^ 105 * (N : ℝ) *
          (Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105) /
          (engelsmaMaynardModulus N : ℝ) ^ 106 := by
    calc
      (N : ℝ) / (Real.rpow (N : ℝ) eps) ^ 106 ≤
          (N : ℝ) / (engelsmaMaynardModulus N : ℝ) ^ 106 := by
        apply div_le_div_of_nonneg_left (by positivity)
        · exact pow_pos (by exact_mod_cast hWpos) _
        · exact hpowW
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right hnum
        exact pow_nonneg (by exact_mod_cast hWpos.le) _
  calc
    Real.rpow (N : ℝ) (1 - 106 * eps) =
        (N : ℝ) / Real.rpow (N : ℝ) (106 * eps) := by
      rw [div_eq_mul_inv]
      have hinv : (Real.rpow (N : ℝ) (106 * eps))⁻¹ =
          Real.rpow (N : ℝ) (-(106 * eps)) :=
        (Real.rpow_neg hNpos.le _).symm
      rw [hinv]
      have hpow : Real.rpow (N : ℝ) (1 - 106 * eps) =
          (N : ℝ) * Real.rpow (N : ℝ) (-(106 * eps)) := by
        calc
          Real.rpow (N : ℝ) (1 - 106 * eps) =
              Real.rpow (N : ℝ) (1 + (-(106 * eps))) := by
                congr 1
          _ = Real.rpow (N : ℝ) 1 *
              Real.rpow (N : ℝ) (-(106 * eps)) :=
            Real.rpow_add hNpos 1 (-(106 * eps))
          _ = (N : ℝ) * Real.rpow (N : ℝ) (-(106 * eps)) := by
            change (N : ℝ) ^ (1 : ℝ) * Real.rpow (N : ℝ) (-(106 * eps)) = _
            rw [Real.rpow_one]
      rw [hpow]
    _ = (N : ℝ) / (Real.rpow (N : ℝ) eps) ^ (106 : ℕ) := by
      congr 2
      rw [show 106 * eps = eps * (106 : ℝ) by ring]
      rw [← Real.rpow_natCast (Real.rpow (N : ℝ) eps) 106]
      exact Real.rpow_mul (x := (N : ℝ)) (by positivity) eps (106 : ℝ)
    _ ≤ ((Nat.totient (engelsmaMaynardModulus N) : ℝ) ^ 105 * (N : ℝ) *
          (Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105) /
          (engelsmaMaynardModulus N : ℝ) ^ 106 := hdiv
    _ = engelsmaMaynardScale alpha N := by rfl

end BoundedGaps.Maynard
