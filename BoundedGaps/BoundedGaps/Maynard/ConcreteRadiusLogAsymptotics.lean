import BoundedGaps.Maynard.ConcreteSquarefreeMeanLimit

noncomputable section

namespace BoundedGaps.Maynard

open Filter

/-! The natural floor radius has the same logarithmic scale as its real cutoff. -/

theorem tendsto_log_engelsmaMaynardRadius_div_log_sub
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      Real.log (engelsmaMaynardRadius alpha N) /
        Real.log ((N - 1 : ℕ) : ℝ))
      atTop (nhds alpha) := by
  have hX : Tendsto
      (fun N : ℕ => ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1)
  have hlogX : Tendsto
      (fun N : ℕ => Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hX
  have hY : Tendsto (fun N : ℕ =>
      Real.rpow ((N - 1 : ℕ) : ℝ) alpha) atTop atTop :=
    (tendsto_rpow_atTop halpha).comp hX
  have hdiff : Tendsto (fun N : ℕ =>
      Real.log (engelsmaMaynardRadius alpha N) /
          Real.log ((N - 1 : ℕ) : ℝ) - alpha)
      atTop (nhds 0) := by
    have hInv := tendsto_inv_atTop_zero.comp hlogX
    have hbound : ∀ᶠ N : ℕ in atTop,
        |Real.log (engelsmaMaynardRadius alpha N) -
            alpha * Real.log ((N - 1 : ℕ) : ℝ)| ≤ Real.log 2 := by
      filter_upwards [hY.eventually (eventually_ge_atTop 2),
        eventually_ge_atTop 3] with N hN2 hN3
      let X : ℝ := ((N - 1 : ℕ) : ℝ)
      have hXpos : 0 < X := by
        dsimp [X]
        exact_mod_cast (show 0 < N - 1 by omega)
      have hfloor : Real.rpow X alpha / 2 ≤
          (engelsmaMaynardRadius alpha N : ℝ) := by
        unfold engelsmaMaynardRadius maynardDivisorCutoff
        change Real.rpow X alpha / 2 ≤
          (Nat.floor (Real.rpow X alpha) : ℝ)
        have hsub : Real.rpow X alpha / 2 ≤
            Real.rpow X alpha - 1 := by linarith
        have hlt : Real.rpow X alpha - 1 <
            (Nat.floor (Real.rpow X alpha) : ℝ) :=
          Nat.sub_one_lt_floor (R := ℝ) (Real.rpow X alpha)
        exact hsub.trans hlt.le
      have hfloorPos : 0 <
          (engelsmaMaynardRadius alpha N : ℝ) :=
        (div_pos (Real.rpow_pos_of_pos hXpos alpha) (by norm_num)).trans_le hfloor
      have hfloorUpper :
          (engelsmaMaynardRadius alpha N : ℝ) ≤
            Real.rpow X alpha := by
        unfold engelsmaMaynardRadius maynardDivisorCutoff
        exact Nat.floor_le (Real.rpow_nonneg hXpos.le alpha)
      have hlogFloor : Real.log (Real.rpow X alpha / 2) ≤
          Real.log (engelsmaMaynardRadius alpha N) := by
        exact Real.strictMonoOn_log.monotoneOn
          (div_pos (Real.rpow_pos_of_pos hXpos alpha) (by norm_num))
          hfloorPos hfloor
      have hlogUpper : Real.log (engelsmaMaynardRadius alpha N) ≤
          alpha * Real.log X := by
        have h := Real.strictMonoOn_log.monotoneOn hfloorPos
          (Real.rpow_pos_of_pos hXpos alpha) hfloorUpper
        exact h.trans_eq (Real.log_rpow hXpos alpha)
      have hlogLower : alpha * Real.log X - Real.log 2 ≤
          Real.log (engelsmaMaynardRadius alpha N) := by
        rw [Real.log_div (x := Real.rpow X alpha) (y := (2 : ℝ))
          (Real.rpow_pos_of_pos hXpos alpha).ne' (by norm_num)] at hlogFloor
        have hlogpow : Real.log (Real.rpow X alpha) =
            alpha * Real.log X := Real.log_rpow hXpos alpha
        rw [hlogpow] at hlogFloor
        linarith
      rw [show ((N - 1 : ℕ) : ℝ) = X by rfl]
      rw [abs_le]
      constructor <;> linarith [hlogLower, hlogUpper]
    have hlogXpos : ∀ᶠ N : ℕ in atTop,
        0 < Real.log ((N - 1 : ℕ) : ℝ) :=
      hlogX.eventually (eventually_gt_atTop 0)
    have henv : Tendsto (fun N : ℕ =>
        Real.log 2 / Real.log ((N - 1 : ℕ) : ℝ))
        atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using hInv.const_mul (Real.log 2)
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henv
    filter_upwards [hbound, hlogXpos] with N hN hXpos
    have heq : Real.log (engelsmaMaynardRadius alpha N) /
          Real.log ((N - 1 : ℕ) : ℝ) - alpha =
        (Real.log (engelsmaMaynardRadius alpha N) -
          alpha * Real.log ((N - 1 : ℕ) : ℝ)) /
          Real.log ((N - 1 : ℕ) : ℝ) := by
      field_simp [ne_of_gt hXpos]
    rw [heq, abs_div, abs_of_pos hXpos]
    exact div_le_div_of_nonneg_right hN hXpos.le
  have hshift := hdiff.add_const alpha
  simpa [sub_add_cancel] using hshift

theorem tendsto_log_engelsmaMaynardRadius_ratio
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    Tendsto (fun N : ℕ =>
      Real.log (engelsmaMaynardRadius alpha N) /
        Real.log (engelsmaMaynardRadius beta N))
      atTop (nhds (alpha / beta)) := by
  have hbase := tendsto_log_engelsmaMaynardRadius_div_log_sub halpha
  have hother := tendsto_log_engelsmaMaynardRadius_div_log_sub hbeta
  have hdiv := hbase.div hother (ne_of_gt hbeta)
  apply hdiv.congr'
  have hlogX : Tendsto
      (fun N : ℕ => Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
  filter_upwards [hlogX.eventually (eventually_ne_atTop 0)] with N hXne
  change (Real.log (engelsmaMaynardRadius alpha N) /
      Real.log ((N - 1 : ℕ) : ℝ)) /
    (Real.log (engelsmaMaynardRadius beta N) /
      Real.log ((N - 1 : ℕ) : ℝ)) =
      Real.log (engelsmaMaynardRadius alpha N) /
        Real.log (engelsmaMaynardRadius beta N)
  field_simp [hXne]

set_option maxRecDepth 10000 in
theorem tendsto_log_engelsmaMaynardRadius_div_realRadius
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      Real.log (engelsmaMaynardRadius alpha N) /
        Real.log (engelsmaMaynardRealRadius alpha N))
      atTop (nhds 1) := by
  have hbase := tendsto_log_engelsmaMaynardRadius_div_log_sub halpha
  have hlog : Tendsto (fun N : ℕ =>
      Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
  have hreal : Tendsto (fun N : ℕ =>
      Real.log (engelsmaMaynardRealRadius alpha N) /
        Real.log ((N - 1 : ℕ) : ℝ)) atTop (nhds alpha) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => alpha) atTop
      (nhds alpha)).congr'
    filter_upwards [hlog.eventually (eventually_gt_atTop 0),
      eventually_ge_atTop 3] with N hlogN hN
    have hbasePos : 0 < ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < N - 1 by omega)
    unfold engelsmaMaynardRealRadius maynardRealCutoff
    have hlogpow : Real.log
        (Real.rpow ((N - 1 : ℕ) : ℝ) alpha) =
        alpha * Real.log ((N - 1 : ℕ) : ℝ) := by
      simpa only [Real.rpow_eq_pow] using Real.log_rpow hbasePos alpha
    change alpha = Real.log
      (Real.rpow ((N - 1 : ℕ) : ℝ) alpha) /
        Real.log ((N - 1 : ℕ) : ℝ)
    rw [hlogpow]
    field_simp [hlogN.ne']
  have hdiv : Tendsto (fun N : ℕ =>
      (Real.log (engelsmaMaynardRadius alpha N) /
        Real.log ((N - 1 : ℕ) : ℝ)) /
      (Real.log (engelsmaMaynardRealRadius alpha N) /
        Real.log ((N - 1 : ℕ) : ℝ))) atTop (nhds (alpha / alpha)) := by
    apply (hbase.div hreal (ne_of_gt halpha)).congr'
    exact Eventually.of_forall fun N => rfl
  have hdivOne : Tendsto (fun N : ℕ =>
      (Real.log (engelsmaMaynardRadius alpha N) /
        Real.log ((N - 1 : ℕ) : ℝ)) /
      (Real.log (engelsmaMaynardRealRadius alpha N) /
        Real.log ((N - 1 : ℕ) : ℝ))) atTop (nhds 1) := by
    simpa [div_self halpha.ne'] using hdiv
  apply hdivOne.congr'
  filter_upwards [hlog.eventually (eventually_ne_atTop 0),
    eventually_ge_atTop 3] with N hlogNe hN
  have hrealPos : 0 < Real.log (engelsmaMaynardRealRadius alpha N) := by
    apply Real.log_pos
    unfold engelsmaMaynardRealRadius maynardRealCutoff
    apply Real.one_lt_rpow
    · exact_mod_cast (show 1 < N - 1 by omega)
    · exact halpha
  field_simp [hlogNe, hrealPos.ne']

theorem tendsto_engelsmaSquarefreeMean_fractionalRadius
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    Tendsto (fun N : ℕ =>
      squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta) N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds beta) := by
  have hgamma : 0 < alpha * beta := mul_pos halpha hbeta
  have hmean :=
    tendsto_engelsmaSquarefreeMean_div_leadingTerm_one hgamma
  have hratio :=
    tendsto_log_engelsmaMaynardRadius_ratio hgamma halpha
  have hproduct : Tendsto (fun N : ℕ =>
      (squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta) N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius (alpha * beta) N))) *
      (Real.log (engelsmaMaynardRadius (alpha * beta) N) /
        Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds beta) := by
    simpa [ne_of_gt halpha] using hmean.mul hratio
  apply hproduct.congr'
  have hlogGamma := tendsto_log_engelsmaMaynardRadius_atTop hgamma
  have hlogAlpha := tendsto_log_engelsmaMaynardRadius_atTop halpha
  filter_upwards [hlogGamma.eventually (eventually_ne_atTop 0),
    hlogAlpha.eventually (eventually_ne_atTop 0)] with N hGamma hAlpha
  have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
  field_simp [hS.ne', hGamma, hAlpha]

end BoundedGaps.Maynard
