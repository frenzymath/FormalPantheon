import BoundedGaps.Maynard.ConcreteYDiagonalCollisionLimit

noncomputable section

namespace BoundedGaps.Maynard

open Filter

/-! The unweighted cross-coordinate collision mass is negligible after S1 scaling.

Source: `Maynard2013v3`, printed Section 6, `eq:S1CoprimeError`, source
lines 488--491. Semantic review: `SEM-211`.
-/

def engelsmaCollisionWeightMass (alpha : ℝ) (N : ℕ) : ℝ :=
  ∑ u ∈ preSievedSimplexCollisionSupport BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
    reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u

def normalizedEngelsmaCollisionWeightMass (alpha : ℝ) (N : ℕ) : ℝ :=
  (((N : ℝ) / engelsmaMaynardModulus N) *
      engelsmaCollisionWeightMass alpha N) /
    engelsmaMaynardScale alpha N

set_option maxRecDepth 10000 in
theorem eventually_normalized_engelsmaCollisionWeightMass_le
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop,
      normalizedEngelsmaCollisionWeightMass alpha N ≤
        ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
          (8 / (tripleLogCutoff (N - 1) : ℝ)) *
          (squarefreeCoprimeInvTotientMean
              (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N) /
            (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
              Real.log (engelsmaMaynardRadius alpha N))) ^ 105 *
          (Real.log (engelsmaMaynardRadius alpha N) /
            Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105 := by
  have hR := eventually_one_lt_engelsmaMaynardRadius halpha
  have hscale := eventually_engelsmaMaynardScale_pos halpha
  obtain ⟨N₀, hN₀⟩ := exists_tripleLogCutoff_ge 1
  filter_upwards [hR, hscale, eventually_ge_atTop (N₀ + 1),
    eventually_ge_atTop 3] with N hRN hscaleN hN hN3
  have hDge : 1 ≤ tripleLogCutoff (N - 1) :=
    hN₀ (N - 1) (by omega)
  have hD : 0 < tripleLogCutoff (N - 1) := lt_of_lt_of_le Nat.zero_lt_one hDge
  have hW : 0 < (engelsmaMaynardModulus N : ℝ) := by
    exact_mod_cast primorial_pos (tripleLogCutoff (N - 1))
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log (engelsmaMaynardRadius alpha N) :=
    Real.log_pos (by exact_mod_cast hRN)
  have hrealGt : 1 < engelsmaMaynardRealRadius alpha N := by
    unfold engelsmaMaynardRealRadius maynardRealCutoff
    apply Real.one_lt_rpow
    · exact_mod_cast (show 1 < N - 1 by omega)
    · exact halpha
  have hLreal : 0 < Real.log (engelsmaMaynardRealRadius alpha N) :=
    Real.log_pos hrealGt
  have hweight := collisionWeightSum_le_explicit
    (H := BoundedGaps.engelsmaTuple)
    (R := engelsmaMaynardRadius alpha N)
    (D := tripleLogCutoff (N - 1)) hD
  have hweight' :
      engelsmaCollisionWeightMass alpha N ≤
        ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
          (squarefreeCoprimeInvTotientMean
              (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N)) ^ 105 *
          (8 / (tripleLogCutoff (N - 1) : ℝ)) := by
    simpa only [engelsmaCollisionWeightMass, engelsmaMaynardModulus,
      Fintype.card_coe, BoundedGaps.engelsmaTuple_card] using hweight
  have hratioNonneg : 0 ≤ (N : ℝ) / engelsmaMaynardModulus N :=
    div_nonneg hNpos.le hW.le
  have hmassNonneg : 0 ≤ engelsmaCollisionWeightMass alpha N := by
    unfold engelsmaCollisionWeightMass
    apply Finset.sum_nonneg
    intro u hu
    unfold reciprocalTotientTupleWeight
    positivity
  have hbound : normalizedEngelsmaCollisionWeightMass alpha N ≤
      (((N : ℝ) / engelsmaMaynardModulus N) *
        (((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
            (squarefreeCoprimeInvTotientMean
                (engelsmaMaynardModulus N)
                (engelsmaMaynardRadius alpha N)) ^ 105 *
            (8 / (tripleLogCutoff (N - 1) : ℝ)))) /
        engelsmaMaynardScale alpha N := by
    unfold normalizedEngelsmaCollisionWeightMass
    apply div_le_div_of_nonneg_right _ hscaleN.le
    exact mul_le_mul_of_nonneg_left hweight' hratioNonneg
  calc
    normalizedEngelsmaCollisionWeightMass alpha N ≤
        (((N : ℝ) / engelsmaMaynardModulus N) *
          (((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
              (squarefreeCoprimeInvTotientMean
                  (engelsmaMaynardModulus N)
                  (engelsmaMaynardRadius alpha N)) ^ 105 *
              (8 / (tripleLogCutoff (N - 1) : ℝ)))) /
          engelsmaMaynardScale alpha N := hbound
    _ = ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
          (8 / (tripleLogCutoff (N - 1) : ℝ)) *
          (squarefreeCoprimeInvTotientMean
              (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N) /
            (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
              Real.log (engelsmaMaynardRadius alpha N))) ^ 105 *
          (Real.log (engelsmaMaynardRadius alpha N) /
            Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105 := by
      rw [preSieveSingularSeries_eq_totient_div]
      unfold engelsmaMaynardScale maynardSieveScale engelsmaMaynardModulus
      have hWprim : 0 < (primorial (tripleLogCutoff (N - 1)) : ℝ) := by
        exact_mod_cast primorial_pos (tripleLogCutoff (N - 1))
      have hphiprim : 0 <
          (Nat.totient (primorial (tripleLogCutoff (N - 1))) : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr
          (primorial_pos (tripleLogCutoff (N - 1)))
      field_simp [hW.ne', hWprim.ne', hphiprim.ne', hNpos.ne', hL.ne',
        hLreal.ne']
      ring

set_option maxRecDepth 10000 in
theorem tendsto_normalized_engelsmaCollisionWeightMass_zero
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ => normalizedEngelsmaCollisionWeightMass alpha N)
      atTop (nhds 0) := by
  have hratio : Tendsto (fun N : ℕ =>
      squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds 1) := tendsto_engelsmaSquarefreeMean_div_leadingTerm_one halpha
  have hpow := hratio.pow 105
  have hrealratio : Tendsto (fun N : ℕ =>
      Real.log (engelsmaMaynardRadius alpha N) /
        Real.log (engelsmaMaynardRealRadius alpha N)) atTop (nhds 1) := by
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
    have hdiv := hbase.div hreal (ne_of_gt halpha)
    have hdiv' : Tendsto (fun N : ℕ =>
        (Real.log (engelsmaMaynardRadius alpha N) /
          Real.log ((N - 1 : ℕ) : ℝ)) /
        (Real.log (engelsmaMaynardRealRadius alpha N) /
          Real.log ((N - 1 : ℕ) : ℝ))) atTop (nhds (alpha / alpha)) := by
      apply hdiv.congr'
      exact Eventually.of_forall (fun N => rfl)
    have hdivOne : Tendsto (fun N : ℕ =>
        (Real.log (engelsmaMaynardRadius alpha N) /
          Real.log ((N - 1 : ℕ) : ℝ)) /
        (Real.log (engelsmaMaynardRealRadius alpha N) /
          Real.log ((N - 1 : ℕ) : ℝ))) atTop (nhds 1) := by
      simpa [div_self halpha.ne'] using hdiv'
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
  have hcutoff : Tendsto (fun N : ℕ =>
      (8 : ℝ) / (tripleLogCutoff (N - 1) : ℝ)) atTop (nhds 0) := by
    change Tendsto ((fun n : ℕ => (8 : ℝ) / (n : ℝ)) ∘
      (fun N : ℕ => tripleLogCutoff (N - 1))) atTop (nhds 0)
    exact (tendsto_const_div_atTop_nhds_zero_nat (8 : ℝ)).comp
      tendsto_shifted_tripleLogCutoff
  have henvelope : Tendsto (fun N : ℕ =>
      ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
        (8 / (tripleLogCutoff (N - 1) : ℝ)) *
        (squarefreeCoprimeInvTotientMean
            (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N) /
          (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
            Real.log (engelsmaMaynardRadius alpha N))) ^ 105 *
        (Real.log (engelsmaMaynardRadius alpha N) /
          Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105)
      atTop (nhds 0) := by
    have hcombined := hcutoff.mul hpow
    have hcombined' := hcombined.mul (hrealratio.pow 105)
    have hscaled := hcombined'.const_mul
      ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ)
    have hscaledZero := hscaled
    simp only [one_pow, mul_one, mul_zero] at hscaledZero
    apply hscaledZero.congr'
    exact Eventually.of_forall fun N => by ring
  have hnonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ normalizedEngelsmaCollisionWeightMass alpha N := by
    filter_upwards [eventually_engelsmaMaynardScale_pos halpha] with N hscaleN
    unfold normalizedEngelsmaCollisionWeightMass
      engelsmaCollisionWeightMass
    apply div_nonneg
    · apply mul_nonneg
      · positivity
      · apply Finset.sum_nonneg
        intro u hu
        unfold reciprocalTotientTupleWeight
        positivity
    · exact hscaleN.le
  apply squeeze_zero' hnonneg ?_ henvelope
  exact eventually_normalized_engelsmaCollisionWeightMass_le halpha

end BoundedGaps.Maynard
