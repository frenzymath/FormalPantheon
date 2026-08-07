import BoundedGaps.Maynard.IntervalDistribution

noncomputable section

namespace BoundedGaps.Maynard

open Filter

/-
Conditional ordinary-PNT specialization for the exact `[N,2*N)` interval.
The PNT hypothesis is deliberately an explicit theorem argument; see SEM-402
and Maynard2013v3, equations (5.15)--(5.17) and (5.26)--(5.27).
-/
theorem tendsto_primeCountTotalInInterval_div_mul_log_sub_of_pnt
    (hpnt : Tendsto
      (fun n : ℕ =>
        (primeCountTotal n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 1)) :
    Tendsto
      (fun N : ℕ =>
        (primeCountTotalInInterval N : ℝ) / (N : ℝ) *
          Real.log ((N - 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
  have hsubNat : Tendsto (fun N : ℕ => N - 1) atTop atTop :=
    tendsto_sub_atTop_nat 1
  have hdoubleNat : Tendsto (fun N : ℕ => 2 * N) atTop atTop := by
    have h : Tendsto (fun N : ℕ => 2 • N) atTop atTop :=
      (show Tendsto (fun N : ℕ => N) atTop atTop from tendsto_id).nsmul_atTop
        (show 0 < (2 : ℕ) by norm_num)
    simpa [two_nsmul] using h
  have hupperNat : Tendsto (fun N : ℕ => 2 * N - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hdoubleNat
  have hpntLower : Tendsto
      (fun N : ℕ =>
        (primeCountTotal (N - 1) : ℝ) *
          Real.log ((N - 1 : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
    simpa [Function.comp_def] using hpnt.comp hsubNat
  have hpntUpper : Tendsto
      (fun N : ℕ =>
        (primeCountTotal (2 * N - 1) : ℝ) *
          Real.log ((2 * N - 1 : ℕ) : ℝ) / ((2 * N - 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
    simpa [Function.comp_def] using hpnt.comp hupperNat
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ))
      atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat 1
  have hlowerRatio : Tendsto
      (fun N : ℕ => ((N - 1 : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (nhds 1)).sub hinv
    have heq : (fun N : ℕ => (1 : ℝ) - 1 / (N : ℝ)) =ᶠ[atTop]
        (fun N : ℕ => ((N - 1 : ℕ) : ℝ) / (N : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [Nat.cast_sub hN]
      have hN0 : (N : ℝ) ≠ 0 := by
        exact_mod_cast (show N ≠ 0 by omega)
      field_simp [hN0]
      norm_num
    simpa using h.congr' heq
  have hupperRatio : Tendsto
      (fun N : ℕ => ((2 * N - 1 : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds 2) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ))
      atTop (nhds 2)).sub hinv
    have heq : (fun N : ℕ => (2 : ℝ) - 1 / (N : ℝ)) =ᶠ[atTop]
        (fun N : ℕ => ((2 * N - 1 : ℕ) : ℝ) / (N : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [Nat.cast_sub (show 1 ≤ 2 * N by omega)]
      push_cast
      have hN0 : (N : ℝ) ≠ 0 := by
        exact_mod_cast (show N ≠ 0 by omega)
      field_simp [hN0]
    simpa using h.congr' heq
  have hbaseAtTop : Tendsto
      (fun N : ℕ => ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hsubNat
  have hupperAtTop : Tendsto
      (fun N : ℕ => ((2 * N - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hupperNat
  have hlogBase : Tendsto
      (fun N : ℕ => Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hbaseAtTop
  have hlogUpper : Tendsto
      (fun N : ℕ => Real.log ((2 * N - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hupperAtTop
  have hendpointRatio : Tendsto
      (fun N : ℕ =>
        ((2 * N - 1 : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ))
      atTop (nhds 2) := by
    have h := hupperRatio.div hlowerRatio one_ne_zero
    have heq :
        (fun N : ℕ =>
          (((2 * N - 1 : ℕ) : ℝ) / (N : ℝ)) /
            (((N - 1 : ℕ) : ℝ) / (N : ℝ))) =ᶠ[atTop]
        (fun N : ℕ =>
          ((2 * N - 1 : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)) := by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by
        exact_mod_cast (show N ≠ 0 by omega)
      have hsub0 : ((N - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show N - 1 ≠ 0 by omega)
      field_simp [hN0, hsub0]
    simpa using h.congr' heq
  have hlogEndpointRatio : Tendsto
      (fun N : ℕ => Real.log
        (((2 * N - 1 : ℕ) : ℝ) / ((N - 1 : ℕ) : ℝ)))
      atTop (nhds (Real.log 2)) :=
    (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp
      hendpointRatio
  have hlogDiff : Tendsto
      (fun N : ℕ =>
        Real.log ((2 * N - 1 : ℕ) : ℝ) -
          Real.log ((N - 1 : ℕ) : ℝ))
      atTop (nhds (Real.log 2)) := by
    apply hlogEndpointRatio.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    apply Real.log_div
    · exact_mod_cast (show 2 * N - 1 ≠ 0 by omega)
    · exact_mod_cast (show N - 1 ≠ 0 by omega)
  have hlogError : Tendsto
      (fun N : ℕ =>
        (Real.log ((2 * N - 1 : ℕ) : ℝ) -
          Real.log ((N - 1 : ℕ) : ℝ)) /
            Real.log ((2 * N - 1 : ℕ) : ℝ))
      atTop (nhds 0) :=
    hlogDiff.div_atTop hlogUpper
  have hlogRatio : Tendsto
      (fun N : ℕ =>
        Real.log ((N - 1 : ℕ) : ℝ) /
          Real.log ((2 * N - 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
      atTop (nhds 1)).sub hlogError
    have heq : (fun N : ℕ => (1 : ℝ) -
          (Real.log ((2 * N - 1 : ℕ) : ℝ) -
            Real.log ((N - 1 : ℕ) : ℝ)) /
              Real.log ((2 * N - 1 : ℕ) : ℝ)) =ᶠ[atTop]
        (fun N : ℕ =>
          Real.log ((N - 1 : ℕ) : ℝ) /
            Real.log ((2 * N - 1 : ℕ) : ℝ)) := by
      filter_upwards [hlogUpper.eventually (eventually_ne_atTop 0)]
        with N hlog0
      field_simp [hlog0]
      ring
    simpa using h.congr' heq
  have hupperTerm : Tendsto
      (fun N : ℕ =>
        (primeCountTotal (2 * N - 1) : ℝ) / (N : ℝ) *
          Real.log ((N - 1 : ℕ) : ℝ))
      atTop (nhds 2) := by
    have h := (hpntUpper.mul hupperRatio).mul hlogRatio
    have heq :
        (fun N : ℕ =>
          ((primeCountTotal (2 * N - 1) : ℝ) *
              Real.log ((2 * N - 1 : ℕ) : ℝ) /
                ((2 * N - 1 : ℕ) : ℝ)) *
            (((2 * N - 1 : ℕ) : ℝ) / (N : ℝ)) *
            (Real.log ((N - 1 : ℕ) : ℝ) /
              Real.log ((2 * N - 1 : ℕ) : ℝ))) =ᶠ[atTop]
        (fun N : ℕ =>
          (primeCountTotal (2 * N - 1) : ℝ) / (N : ℝ) *
            Real.log ((N - 1 : ℕ) : ℝ)) := by
      filter_upwards [eventually_ge_atTop 2,
        hlogUpper.eventually (eventually_ne_atTop 0)] with N hN hlog0
      have hN0 : (N : ℝ) ≠ 0 := by
        exact_mod_cast (show N ≠ 0 by omega)
      have hupper0 : ((2 * N - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show 2 * N - 1 ≠ 0 by omega)
      field_simp [hN0, hupper0, hlog0]
    simpa using h.congr' heq
  have hlowerTerm : Tendsto
      (fun N : ℕ =>
        (primeCountTotal (N - 1) : ℝ) / (N : ℝ) *
          Real.log ((N - 1 : ℕ) : ℝ))
      atTop (nhds 1) := by
    have h := hpntLower.mul hlowerRatio
    have heq :
        (fun N : ℕ =>
          ((primeCountTotal (N - 1) : ℝ) *
              Real.log ((N - 1 : ℕ) : ℝ) /
                ((N - 1 : ℕ) : ℝ)) *
            (((N - 1 : ℕ) : ℝ) / (N : ℝ))) =ᶠ[atTop]
        (fun N : ℕ =>
          (primeCountTotal (N - 1) : ℝ) / (N : ℝ) *
            Real.log ((N - 1 : ℕ) : ℝ)) := by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hN0 : (N : ℝ) ≠ 0 := by
        exact_mod_cast (show N ≠ 0 by omega)
      have hsub0 : ((N - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show N - 1 ≠ 0 by omega)
      field_simp [hN0, hsub0]
    simpa using h.congr' heq
  have hdiff := hupperTerm.sub hlowerTerm
  have heq :
      (fun N : ℕ =>
        (primeCountTotal (2 * N - 1) : ℝ) / (N : ℝ) *
            Real.log ((N - 1 : ℕ) : ℝ) -
          (primeCountTotal (N - 1) : ℝ) / (N : ℝ) *
            Real.log ((N - 1 : ℕ) : ℝ)) =ᶠ[atTop]
      (fun N : ℕ =>
        (primeCountTotalInInterval N : ℝ) / (N : ℝ) *
          Real.log ((N - 1 : ℕ) : ℝ)) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [cast_primeCountTotalInInterval (show 0 < N by omega)]
    ring
  convert hdiff.congr' heq using 1
  norm_num

end BoundedGaps.Maynard
