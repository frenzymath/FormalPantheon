import BoundedGaps.Maynard.Parameters
import BoundedGaps.Maynard.Growth
import BoundedGaps.Maynard.SieveScale

/-!
# Subpower growth of the triple-log pre-sieve

Maynard chooses `W` as the primorial at `D₀ = log log log N`. The elementary
primorial bound and logarithmic power absorption show that this `W` is smaller
than every fixed positive power of `N`.
-/

namespace BoundedGaps.Maynard

open Filter

theorem tripleLogCutoff_cast_le_log_log {N : ℕ}
    (hll : 1 ≤ Real.log (Real.log (N : ℝ))) :
    (tripleLogCutoff N : ℝ) ≤ Real.log (Real.log (N : ℝ)) := by
  unfold tripleLogCutoff
  have hlogll : 0 ≤ Real.log (Real.log (Real.log (N : ℝ))) :=
    Real.log_nonneg hll
  exact (Nat.floor_le hlogll).trans
    (Real.log_le_self (zero_le_one.trans hll))

theorem four_pow_tripleLogCutoff_le_log_rpow {N : ℕ}
    (hll : 1 ≤ Real.log (Real.log (N : ℝ))) :
    ((4 ^ tripleLogCutoff N : ℕ) : ℝ) ≤
      Real.rpow (Real.log (N : ℝ)) (Real.log 4) := by
  have hNtwo : 2 ≤ N := by
    by_contra h
    have hNle : N ≤ 1 := by omega
    interval_cases N <;> norm_num at hll
  have hNone : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hNtwo
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos hNone
  have hD := tripleLogCutoff_cast_le_log_log hll
  calc
    ((4 ^ tripleLogCutoff N : ℕ) : ℝ) =
        Real.rpow (4 : ℝ) (tripleLogCutoff N : ℝ) := by
      push_cast
      exact (Real.rpow_natCast (4 : ℝ) (tripleLogCutoff N)).symm
    _ ≤ Real.rpow (4 : ℝ) (Real.log (Real.log (N : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hD
    _ = Real.rpow (Real.log (N : ℝ)) (Real.log 4) := by
      change (4 : ℝ) ^ Real.log (Real.log (N : ℝ)) =
        Real.log (N : ℝ) ^ Real.log 4
      rw [Real.rpow_def_of_pos (by norm_num),
        Real.rpow_def_of_pos hlogNpos]
      congr 1
      ring

theorem primorial_tripleLogCutoff_le_log_rpow {N : ℕ}
    (hll : 1 ≤ Real.log (Real.log (N : ℝ))) :
    (primorial (tripleLogCutoff N) : ℝ) ≤
      Real.rpow (Real.log (N : ℝ)) (Real.log 4) := by
  have hp := primorial_le_four_pow (tripleLogCutoff N)
  have hpR : (primorial (tripleLogCutoff N) : ℝ) ≤
      ((4 ^ tripleLogCutoff N : ℕ) : ℝ) := by exact_mod_cast hp
  exact hpR.trans (four_pow_tripleLogCutoff_le_log_rpow hll)

theorem eventually_primorial_tripleLogCutoff_le_rpow
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ N : ℕ in atTop,
      (primorial (tripleLogCutoff N) : ℝ) ≤
        Real.rpow (N : ℝ) eps := by
  have hll_tendsto : Tendsto
      (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hll : ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (Real.log (N : ℝ)) :=
    hll_tendsto.eventually (eventually_ge_atTop 1)
  obtain ⟨N₀, hN₀, hlogpow⟩ :=
    exists_log_rpow_le_rpow
      (θ := 1 - eps) (A := Real.log 4) (by linarith)
      (Real.log_nonneg (by norm_num))
  have hlogpow' : ∀ᶠ N : ℕ in atTop,
      Real.rpow (Real.log (N : ℝ)) (Real.log 4) ≤
        Real.rpow (N : ℝ) eps := by
    filter_upwards [eventually_ge_atTop N₀] with N hN
    simpa only [sub_sub_cancel] using hlogpow N hN
  filter_upwards [hll, hlogpow'] with N hllN hpowN
  exact (primorial_tripleLogCutoff_le_log_rpow hllN).trans hpowN

theorem eventually_tripleLogPrimorial_divisorCutoff_le_modulusCutoff
    {theta delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop,
      primorial (tripleLogCutoff N) *
          maynardDivisorCutoff (theta / 2 - delta) N *
          maynardDivisorCutoff (theta / 2 - delta) N ≤
        modulusCutoff theta N := by
  apply eventually_maynardDivisorCutoff_product_le_modulusCutoff
    (eps := delta) (alpha := theta / 2 - delta)
  · linarith
  · exact eventually_primorial_tripleLogCutoff_le_rpow hdelta

theorem eventually_shifted_tripleLogPrimorial_divisorCutoff
    {theta delta : ℝ} (hθ : 0 ≤ theta) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, ∀ h : ℕ,
      primorial (tripleLogCutoff (N - 1)) *
          maynardDivisorCutoff (theta / 2 - delta) (N - 1) *
          maynardDivisorCutoff (theta / 2 - delta) (N - 1) ≤
        modulusCutoff theta (N + h - 1) := by
  have hbase : ∀ᶠ N : ℕ in atTop,
      primorial (tripleLogCutoff (N - 1)) *
          maynardDivisorCutoff (theta / 2 - delta) (N - 1) *
          maynardDivisorCutoff (theta / 2 - delta) (N - 1) ≤
        modulusCutoff theta (N - 1) :=
    (tendsto_sub_atTop_nat 1).eventually
      (eventually_tripleLogPrimorial_divisorCutoff_le_modulusCutoff hdelta)
  filter_upwards [hbase, eventually_ge_atTop 1] with N hNbase hN
  intro h
  apply hNbase.trans
  apply modulusCutoff_mono hθ
  omega

theorem eventually_maynard_radius_le
    {theta delta : ℝ} (hθhalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hδlt : delta < theta / 2) :
    ∀ᶠ N : ℕ in atTop,
      maynardDivisorCutoff (theta / 2 - delta) (N - 1) ≤ N := by
  have hαlt : theta / 2 - delta ≤ 1 := by linarith
  filter_upwards [eventually_ge_atTop 2] with N hN
  unfold maynardDivisorCutoff
  apply Nat.floor_le_of_le
  have hbase : (1 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ N - 1 by omega)
  have hpow : Real.rpow ((N - 1 : ℕ) : ℝ) (theta / 2 - delta) ≤
      Real.rpow ((N - 1 : ℕ) : ℝ) 1 :=
    Real.rpow_le_rpow_of_exponent_le hbase hαlt
  calc
    Real.rpow ((N - 1 : ℕ) : ℝ) (theta / 2 - delta) ≤
        Real.rpow ((N - 1 : ℕ) : ℝ) 1 := hpow
    _ = ((N - 1 : ℕ) : ℝ) := by simp
    _ ≤ (N : ℝ) := by exact_mod_cast (Nat.sub_le N 1)

theorem eventually_exists_engelsma_maynard_parameters
    {theta delta : ℝ} (hθ : 0 ≤ theta) (hθhalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hδlt : delta < theta / 2) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ v : ℕ,
        v < primorial (tripleLogCutoff (N - 1)) ∧
        (∀ h ∈ BoundedGaps.engelsmaTuple,
          Nat.Coprime (v + h) (primorial (tripleLogCutoff (N - 1)))) ∧
        CoversShiftDifferencePrimes BoundedGaps.engelsmaTuple
          (primorial (tripleLogCutoff (N - 1))) ∧
        maynardDivisorCutoff (theta / 2 - delta) (N - 1) ≤ N ∧
        (∀ h : ℕ,
          primorial (tripleLogCutoff (N - 1)) *
              maynardDivisorCutoff (theta / 2 - delta) (N - 1) *
              maynardDivisorCutoff (theta / 2 - delta) (N - 1) ≤
            modulusCutoff theta (N + h - 1)) := by
  have hcoverage : ∀ᶠ N : ℕ in atTop,
      CoversShiftDifferencePrimes BoundedGaps.engelsmaTuple
        (primorial (tripleLogCutoff (N - 1))) := by
    obtain ⟨N₀, hN₀⟩ := eventually_engelsma_primorial_coverage
    have hev : ∀ᶠ M : ℕ in atTop,
        CoversShiftDifferencePrimes BoundedGaps.engelsmaTuple
          (primorial (tripleLogCutoff M)) := by
      rw [Filter.eventually_atTop]
      exact ⟨N₀, hN₀⟩
    exact (tendsto_sub_atTop_nat 1).eventually hev
  have hcutoff := eventually_shifted_tripleLogPrimorial_divisorCutoff hθ hdelta
  have hradius := eventually_maynard_radius_le hθhalf hdelta hδlt
  have hevent : ∀ᶠ N : ℕ in atTop,
      CoversShiftDifferencePrimes BoundedGaps.engelsmaTuple
          (primorial (tripleLogCutoff (N - 1))) ∧
        maynardDivisorCutoff (theta / 2 - delta) (N - 1) ≤ N ∧
        (∀ h : ℕ,
          primorial (tripleLogCutoff (N - 1)) *
              maynardDivisorCutoff (theta / 2 - delta) (N - 1) *
              maynardDivisorCutoff (theta / 2 - delta) (N - 1) ≤
            modulusCutoff theta (N + h - 1)) := by
    filter_upwards [hcoverage, hradius, hcutoff] with N hcov hrad hcut
    exact ⟨hcov, hrad, hcut⟩
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨N₀, hN₀⟩ := hevent
  refine ⟨max N₀ 2, ?_⟩
  intro N hN
  have hNbase : N₀ ≤ N := le_trans (le_max_left _ _) hN
  obtain ⟨hcov, hrad, hcut⟩ := hN₀ N hNbase
  obtain ⟨v, hvlt, hv⟩ :=
    exists_preSieveResidueClass_primorial
      BoundedGaps.engelsmaTuple_admissible (tripleLogCutoff (N - 1))
  exact ⟨v, hvlt, hv, hcov, hrad, hcut⟩

end BoundedGaps.Maynard
