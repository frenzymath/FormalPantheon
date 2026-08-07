import BoundedGaps.Maynard.MaynardYDiagonalCollisionMass
import BoundedGaps.Maynard.ConcreteSquarefreeMeanLimit
import BoundedGaps.Maynard.ConcreteS1CrossLimit
import BoundedGaps.Maynard.ConcreteRadiusLogAsymptotics

noncomputable section

namespace BoundedGaps.Maynard

open Filter

/-! The normalized collision contribution vanishes in the frozen Engelsma family.

Source: `Maynard2013v3`, printed Section 6, `eq:S1CoprimeError`, source
lines 488--491. Semantic review: `SEM-205`.
-/

set_option maxRecDepth 10000 in
theorem eventually_abs_normalized_engelsmaCollisionQuadraticMoment_le
    {alpha : ℝ} (halpha : 0 < alpha) (b c : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      |normalizedEngelsmaCollisionQuadraticMoment alpha N b c| ≤
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
    eventually_ge_atTop 3] with
      N hRN hscaleN hN hN3
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
      (∑ u ∈ preSievedSimplexCollisionSupport BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
        reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u) ≤
        ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
          (squarefreeCoprimeInvTotientMean
              (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N)) ^ 105 *
          (8 / (tripleLogCutoff (N - 1) : ℝ)) := by
    simpa only [engelsmaMaynardModulus, Fintype.card_coe,
      BoundedGaps.engelsmaTuple_card] using hweight
  have hcollision := abs_engelsmaCollisionQuadraticMomentSum_le_weight
    (alpha := alpha) (N := N) (b := b) (c := c) hRN
  have habs :
      |normalizedEngelsmaCollisionQuadraticMoment alpha N b c| =
        (((N : ℝ) / engelsmaMaynardModulus N) *
          |engelsmaCollisionQuadraticMomentSum alpha N b c|) /
            engelsmaMaynardScale alpha N := by
    unfold normalizedEngelsmaCollisionQuadraticMoment
    rw [abs_div, abs_mul, abs_div, abs_of_nonneg (Nat.cast_nonneg N),
      abs_of_pos hW, abs_of_pos hscaleN]
  have hbound :
      |normalizedEngelsmaCollisionQuadraticMoment alpha N b c| ≤
        (((N : ℝ) / engelsmaMaynardModulus N) *
          (((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
              (squarefreeCoprimeInvTotientMean
                  (engelsmaMaynardModulus N)
                  (engelsmaMaynardRadius alpha N)) ^ 105 *
              (8 / (tripleLogCutoff (N - 1) : ℝ)))) /
          engelsmaMaynardScale alpha N := by
    rw [habs]
    apply div_le_div_of_nonneg_right _ hscaleN.le
    calc
      ((N : ℝ) / engelsmaMaynardModulus N) *
          |engelsmaCollisionQuadraticMomentSum alpha N b c| ≤
          ((N : ℝ) / engelsmaMaynardModulus N) *
            (∑ u ∈ preSievedSimplexCollisionSupport BoundedGaps.engelsmaTuple
                (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
              reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u) :=
        mul_le_mul_of_nonneg_left hcollision
          (div_nonneg (Nat.cast_nonneg N) hW.le)
      _ ≤ ((N : ℝ) / engelsmaMaynardModulus N) *
          (((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
            (squarefreeCoprimeInvTotientMean
                (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N)) ^ 105 *
            (8 / (tripleLogCutoff (N - 1) : ℝ))) := by
        calc
          _ ≤ ((N : ℝ) / engelsmaMaynardModulus N) *
              (((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
                (squarefreeCoprimeInvTotientMean
                    (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N)) ^ 105 *
                (8 / (tripleLogCutoff (N - 1) : ℝ))) :=
            mul_le_mul_of_nonneg_left hweight'
              (div_nonneg (Nat.cast_nonneg N) hW.le)
          _ = _ := by ring
  calc
    |normalizedEngelsmaCollisionQuadraticMoment alpha N b c| ≤
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
theorem tendsto_normalized_engelsmaCollisionQuadraticMoment_zero
    {alpha : ℝ} (halpha : 0 < alpha) (b c : ℕ) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaCollisionQuadraticMoment alpha N b c)
      atTop (nhds 0) := by
  have hratio : Tendsto (fun N : ℕ =>
      squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds 1) :=
    tendsto_engelsmaSquarefreeMean_div_leadingTerm_one halpha
  have hpow : Tendsto (fun N : ℕ =>
      (squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N))) ^ 105)
      atTop (nhds 1) := by
    simpa using hratio.pow 105
  have hrealratio : Tendsto (fun N : ℕ =>
      Real.log (engelsmaMaynardRadius alpha N) /
        Real.log (engelsmaMaynardRealRadius alpha N))
      atTop (nhds 1) := by
    have hbase : Tendsto (fun N : ℕ =>
        Real.log (engelsmaMaynardRadius alpha N) /
          Real.log ((N - 1 : ℕ) : ℝ))
        atTop (nhds alpha) :=
      tendsto_log_engelsmaMaynardRadius_div_log_sub halpha
    have hlog : Tendsto (fun N : ℕ =>
        Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
    have hreal : Tendsto (fun N : ℕ =>
        Real.log (engelsmaMaynardRealRadius alpha N) /
          Real.log ((N - 1 : ℕ) : ℝ))
        atTop (nhds alpha) := by
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
          Real.log ((N - 1 : ℕ) : ℝ)))
        atTop (nhds (alpha / alpha)) := by
      apply hdiv.congr'
      exact Eventually.of_forall (fun N => rfl)
    have hdivOne : Tendsto (fun N : ℕ =>
        (Real.log (engelsmaMaynardRadius alpha N) /
          Real.log ((N - 1 : ℕ) : ℝ)) /
        (Real.log (engelsmaMaynardRealRadius alpha N) /
          Real.log ((N - 1 : ℕ) : ℝ)))
        atTop (nhds 1) := by
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
      (8 : ℝ) / (tripleLogCutoff (N - 1) : ℝ))
      atTop (nhds 0) := by
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
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henvelope
  exact eventually_abs_normalized_engelsmaCollisionQuadraticMoment_le halpha b c

end BoundedGaps.Maynard
