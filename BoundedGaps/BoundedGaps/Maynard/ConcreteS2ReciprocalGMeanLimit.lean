import BoundedGaps.Maynard.MaynardS2ReciprocalGSingularTail
import BoundedGaps.Maynard.MaynardS2ReciprocalGCorrectionMean
import BoundedGaps.Maynard.ConcreteCoprimeEndpoint
import BoundedGaps.Maynard.ConcreteModulusLogLimit
import BoundedGaps.Maynard.ConcreteS2OuterMeanLimit

noncomputable section

/-! Concrete primorial normalization of the reciprocal-g squarefree mean. -/

namespace BoundedGaps.Maynard

open Filter

set_option maxHeartbeats 1600000 in
theorem tendsto_normalized_engelsmaReciprocalGSquarefreeMean_sub_tailLeadingTerm_zero
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      (maynardS2ReciprocalGSquarefreeMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) -
        maynardS2ReciprocalGInfiniteSingularTail
          (tripleLogCutoff (N - 1)) *
          (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
            Real.log (engelsmaMaynardRadius alpha N))) /
      (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds 0) := by
  let C0 : ℝ := 2 * (Real.exp 40 +
    4 * maynardS2ReciprocalGCorrectionQuarterConstant)
  let K : ℝ := Real.exp 8
  let A : ℝ := C0 + K
  have hA : 0 ≤ A := by
    unfold A C0 K maynardS2ReciprocalGCorrectionQuarterConstant
    positivity
  have hmod :=
    (tendsto_engelsmaMaynardModulus_sq_div_logRadius_zero halpha).const_mul A
  have hpred :=
    tendsto_primeLogPredecessorSum_tripleLog_div_logRadius_zero halpha
  have hL := tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hpredAbs : Tendsto (fun N : ℕ =>
      |primeLogPredecessorSum (tripleLogCutoff (N - 1))| /
        Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
    have htmp := (hpred.abs).congr'
      (show (fun N : ℕ =>
          |primeLogPredecessorSum (tripleLogCutoff (N - 1)) /
            Real.log (engelsmaMaynardRadius alpha N)|) =ᶠ[atTop]
        (fun N : ℕ =>
          |primeLogPredecessorSum (tripleLogCutoff (N - 1))| /
            Real.log (engelsmaMaynardRadius alpha N)) by
        filter_upwards [hL.eventually (eventually_gt_atTop 0)] with N hN
        rw [abs_div, abs_of_pos hN])
    simpa only [abs_zero] using htmp
  have henv : Tendsto (fun N : ℕ =>
      A * ((engelsmaMaynardModulus N : ℝ) ^ 2 /
        Real.log (engelsmaMaynardRadius alpha N)) +
      K * |primeLogPredecessorSum (tripleLogCutoff (N - 1))| /
        Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hmod.add (hpredAbs.const_mul K))
  obtain ⟨M0, hM0⟩ := exists_tripleLogCutoff_ge 2
  have hD : ∀ᶠ N : ℕ in atTop,
      2 ≤ tripleLogCutoff (N - 1) := by
    filter_upwards [eventually_ge_atTop (M0 + 1)] with N hN
    exact hM0 (N - 1) (by omega)
  have hWle := eventually_engelsmaMaynardModulus_le_radius halpha
  have hH := eventually_abs_engelsmaPrimorialCoprimeHarmonic_error halpha
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henv
  filter_upwards [hD, hWle,
    hL.eventually (eventually_gt_atTop 0), hH] with
      N hDN hWleN hLpos hHN
  let D := tripleLogCutoff (N - 1)
  let W : ℝ := engelsmaMaynardModulus N
  let L : ℝ := Real.log (engelsmaMaynardRadius alpha N)
  let S : ℝ := preSieveSingularSeries D
  let T : ℝ := maynardS2ReciprocalGInfiniteSingularTail D
  let B : ℝ := primeLogPredecessorSum D
  let H : ℝ := coprimeHarmonicSum (engelsmaMaynardModulus N)
    (engelsmaMaynardRadius alpha N)
  let M : ℝ := maynardS2ReciprocalGSquarefreeMean
    (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N)
  have hD2 : 2 ≤ D := by simpa [D] using hDN
  have hS : 0 < S := by
    simpa [S, D] using preSieveSingularSeries_pos D
  have hSinv : S⁻¹ ≤ W := by
    simpa [S, W, D, engelsmaMaynardModulus] using
      inv_preSieveSingularSeries_le_primorial D
  have hWone : 1 ≤ W := by
    unfold W engelsmaMaynardModulus
    exact_mod_cast primorial_pos (tripleLogCutoff (N - 1))
  have hWnonneg : 0 ≤ W := by linarith
  have hLpos : 0 < L := by simpa [L] using hLpos
  have hMerr : |M - T * H| ≤ C0 := by
    have h := abs_maynardS2ReciprocalGSquarefreeMean_sub_tail_mul_harmonic_le
      hD2 (engelsmaMaynardRadius alpha N)
    simpa [M, T, H, C0, D, engelsmaMaynardModulus] using h
  have hHerr : |H - S * (L + B)| ≤ W := by
    have h := hHN
    simpa [H, S, L, B, D, W, primorialCoprimeHarmonicMainTerm] using h
  have hHL : |H - S * L| ≤ W + S * |B| := by
    calc
      |H - S * L| = |(H - S * (L + B)) + S * B| := by
        congr 1
        ring
      _ ≤ |H - S * (L + B)| + |S * B| := abs_add_le _ _
      _ ≤ W + S * |B| := by
        rw [abs_mul, abs_of_pos hS]
        exact add_le_add hHerr le_rfl
  have hTexp : |T| ≤ Real.exp (16 / (D : ℝ)) := by
    have htail := abs_maynardS2ReciprocalGInfiniteSingularTail_sub_one_le hD2
    calc
      |T| = |(T - 1) + 1| := by congr 1; ring
      _ ≤ |T - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ Real.exp (16 / (D : ℝ)) - 1 + 1 := by
        rw [abs_one]
        exact add_le_add htail le_rfl
      _ = Real.exp (16 / (D : ℝ)) := by ring
  have hTle : |T| ≤ K := by
    have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD2
    have harg : 16 / (D : ℝ) ≤ 8 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < D)).2
      nlinarith
    unfold K
    exact hTexp.trans (Real.exp_le_exp.mpr harg)
  have hmain : |M - T * (S * L)| ≤
      C0 + |T| * (W + S * |B|) := by
    calc
      |M - T * (S * L)| =
          |(M - T * H) + T * (H - S * L)| := by
        congr 1
        ring
      _ ≤ |M - T * H| + |T * (H - S * L)| := abs_add_le _ _
      _ ≤ C0 + |T| * (W + S * |B|) := by
        rw [abs_mul]
        exact add_le_add hMerr
          (mul_le_mul_of_nonneg_left hHL (abs_nonneg _))
  have hmain' : |M - T * (S * L)| ≤
      C0 + K * (W + S * |B|) := by
    exact hmain.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hTle (by positivity)))
  have hWS : 0 ≤ S * L := (mul_pos hS hLpos).le
  have hWsq : W ≤ W ^ 2 := by nlinarith
  have hbound : |(M - T * (S * L)) / (S * L)| ≤
      A * (W ^ 2 / L) + K * (|B| / L) := by
    rw [abs_div, abs_of_pos (mul_pos hS hLpos)]
    calc
      |M - T * (S * L)| / (S * L) ≤
          (C0 + K * (W + S * |B|)) / (S * L) :=
        div_le_div_of_nonneg_right hmain' hWS
      _ = C0 * S⁻¹ / L + K * W * S⁻¹ / L + K * (|B| / L) := by
        field_simp [hS.ne', hLpos.ne']
        ring
      _ ≤ C0 * W ^ 2 / L + K * W ^ 2 / L + K * (|B| / L) := by
        have hC0 : 0 ≤ C0 := by
          unfold C0 maynardS2ReciprocalGCorrectionQuarterConstant
          positivity
        have hK : 0 ≤ K := by unfold K; positivity
        have hfirst : C0 * S⁻¹ / L ≤ C0 * W ^ 2 / L := by
          apply div_le_div_of_nonneg_right _ hLpos.le
          exact mul_le_mul_of_nonneg_left (hSinv.trans hWsq) hC0
        have hsecond : K * W * S⁻¹ / L ≤ K * W ^ 2 / L := by
          apply div_le_div_of_nonneg_right _ hLpos.le
          calc
            K * W * S⁻¹ ≤ K * W * W :=
              mul_le_mul_of_nonneg_left hSinv (mul_nonneg hK hWnonneg)
            _ = K * W ^ 2 := by ring
        exact add_le_add (add_le_add hfirst hsecond) le_rfl
      _ = A * (W ^ 2 / L) + K * (|B| / L) := by
        unfold A
        ring
  simpa [M, T, S, L, W, B, D, div_eq_mul_inv, mul_assoc] using hbound

theorem tendsto_engelsmaReciprocalGSquarefreeMean_div_leadingTerm_one
    {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      maynardS2ReciprocalGSquarefreeMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)))
      atTop (nhds 1) := by
  have hmain :=
    tendsto_normalized_engelsmaReciprocalGSquarefreeMean_sub_tailLeadingTerm_zero
      halpha
  have hD := tendsto_shifted_tripleLogCutoff
  have hDreal : Tendsto (fun N : ℕ =>
      (tripleLogCutoff (N - 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hD
  have harg : Tendsto (fun N : ℕ =>
      16 / (tripleLogCutoff (N - 1) : ℝ)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (16 : ℝ))
        atTop (nhds 16)).div_atTop hDreal)
  have hexp : Tendsto (fun N : ℕ =>
      Real.exp (16 / (tripleLogCutoff (N - 1) : ℝ)) - 1)
      atTop (nhds 0) := by
    simpa using (Real.continuous_exp.continuousAt.tendsto.comp harg).sub_const 1
  have htail : Tendsto (fun N : ℕ =>
      |maynardS2ReciprocalGInfiniteSingularTail
          (tripleLogCutoff (N - 1)) - 1|)
      atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ hexp
    obtain ⟨M0, hM0⟩ := exists_tripleLogCutoff_ge 2
    filter_upwards [eventually_ge_atTop (M0 + 1)] with N hN
    have hDN : 2 ≤ tripleLogCutoff (N - 1) :=
      hM0 (N - 1) (by omega)
    simpa using abs_maynardS2ReciprocalGInfiniteSingularTail_sub_one_le hDN
  have htailSigned : Tendsto (fun N : ℕ =>
      maynardS2ReciprocalGInfiniteSingularTail
          (tripleLogCutoff (N - 1)) - 1)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    change Tendsto (fun N : ℕ =>
      |maynardS2ReciprocalGInfiniteSingularTail
          (tripleLogCutoff (N - 1)) - 1|) atTop (nhds 0)
    exact htail
  have hratio : Tendsto (fun N : ℕ =>
      (maynardS2ReciprocalGSquarefreeMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) -
        maynardS2ReciprocalGInfiniteSingularTail
          (tripleLogCutoff (N - 1)) *
          (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
            Real.log (engelsmaMaynardRadius alpha N))) /
      (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N)) +
      (maynardS2ReciprocalGInfiniteSingularTail
          (tripleLogCutoff (N - 1)) - 1)) atTop (nhds 0) := by
    simpa using hmain.add htailSigned
  have hshift : Tendsto (fun N : ℕ =>
      (maynardS2ReciprocalGSquarefreeMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius alpha N) -
        maynardS2ReciprocalGInfiniteSingularTail
          (tripleLogCutoff (N - 1)) *
          (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
            Real.log (engelsmaMaynardRadius alpha N))) /
      (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N)) +
      (maynardS2ReciprocalGInfiniteSingularTail
          (tripleLogCutoff (N - 1)) - 1) + 1) atTop (nhds 1) := by
    simpa using hratio.add_const 1
  apply hshift.congr'
  filter_upwards [
    (tendsto_log_engelsmaMaynardRadius_atTop halpha).eventually
      (eventually_gt_atTop 0)] with N hLpos
  have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
  field_simp [hS.ne', (ne_of_gt hLpos)]
  ring

end BoundedGaps.Maynard
