import BoundedGaps.Maynard.ConcreteS2RestrictedCrossBound

noncomputable section

/-!
# Normalized restricted S2 cross correction

The finite correction bound is divided by the coordinate-one S2 scale. The
rough cross tail supplies the vanishing factor; the common reciprocal-`g`
mass is normalized by the existing scalar mean limit.
-/

namespace BoundedGaps.Maynard

open Filter Set
set_option maxRecDepth 12000

def normalizedEngelsmaS2RestrictedCrossCorrection
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  engelsmaMaynardS2RestrictedCrossCorrection alpha N m /
    ((preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N)) ^
      (Finset.univ.erase m).card *
      Real.log (engelsmaMaynardRadius alpha N) ^ 2)

theorem tendsto_normalizedEngelsmaS2RestrictedCrossCorrection_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2RestrictedCrossCorrection alpha N m)
      atTop (nhds 0) := by
  let D : ℕ → ℕ := fun N => tripleLogCutoff (N - 1)
  let R : ℕ → ℕ := fun N => engelsmaMaynardRadius alpha N
  let W : ℕ → ℕ := fun N => engelsmaMaynardModulus N
  let L : ℕ → ℝ := fun N => Real.log (R N)
  let S : ℕ → ℝ := fun N => preSieveSingularSeries (D N)
  let Q : ℕ → ℝ := fun N => S N * L N
  let M : ℕ → ℝ := fun N =>
    maynardS2ReciprocalGSquarefreeMean (W N) (R N)
  let k : ℕ := (Finset.univ.erase m).card
  let A : ℕ → ℝ := fun N =>
    8 / (D N : ℝ) + (8 * Real.exp 8 / (D N : ℝ)) *
      (1 + 8 * Real.exp 8 / (D N : ℝ)) ^ (k - 1)
  let E : ℕ → ℝ := fun N =>
    engelsmaS2RestrictedTransformEnvelope alpha N m
  let Tail : ℕ → ℝ := fun N =>
    (32 * Real.exp 32 / (D N : ℝ)) *
      ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
      (Real.exp 32) ^
        ((offDiagonalPairs BoundedGaps.engelsmaTuple).card - 1)
  let Ctail : ℝ := 32 * Real.exp 32 *
      ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
      (Real.exp 32) ^
        ((offDiagonalPairs BoundedGaps.engelsmaTuple).card - 1)
  let Cenv : ℝ := 16 * smallKCandidateBound * (1 + (k : ℝ))
  have hDtop : Tendsto (fun N => (D N : ℝ)) atTop atTop := by
    dsimp [D]
    exact tendsto_natCast_atTop_atTop.comp tendsto_shifted_tripleLogCutoff
  have hinvD : Tendsto (fun N => (1 : ℝ) / D N)
      atTop (nhds 0) := by
    simpa [one_div] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ))
        atTop (nhds 1)).div_atTop hDtop)
  have hterm : Tendsto (fun N => 8 * Real.exp 8 / D N)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinvD.const_mul (8 * Real.exp 8)
  have hpow : Tendsto (fun N =>
      (1 + 8 * Real.exp 8 / D N) ^ (k - 1)) atTop (nhds 1) := by
    simpa [add_comm] using (hterm.add_const 1).pow (k - 1)
  have hA : Tendsto A atTop (nhds 0) := by
    have hfirst : Tendsto (fun N => (8 : ℝ) / (D N : ℝ))
        atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using hinvD.const_mul 8
    have hsecond : Tendsto (fun N =>
        (8 * Real.exp 8 / D N) *
          (1 + 8 * Real.exp 8 / D N) ^ (k - 1))
        atTop (nhds 0) := by
      simpa using hterm.mul hpow
    simpa [A] using hfirst.add hsecond
  have hAsmall : ∀ᶠ N : ℕ in atTop, 0 ≤ A N ∧ A N ≤ 1 := by
    filter_upwards [hA.eventually
      (Metric.ball_mem_nhds (0 : ℝ) one_pos),
      hDtop.eventually (eventually_gt_atTop 0)] with N hN hDN
    have hnonneg : 0 ≤ A N := by
      dsimp [A]
      positivity
    have hle : A N ≤ 1 := by
      exact le_of_lt (by simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hN)
    exact ⟨hnonneg, hle⟩
  have hLtop : Tendsto L atTop atTop := by
    dsimp [L, R]
    exact tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hLratio : ∀ᶠ N : ℕ in atTop,
      0 ≤ (1 + L N) / L N ∧ (1 + L N) / L N ≤ 2 := by
    filter_upwards [hLtop.eventually (eventually_ge_atTop (1 : ℝ))] with
      N hN
    have hLpos : 0 < L N := lt_of_lt_of_le zero_lt_one hN
    constructor
    · exact div_nonneg (by linarith) hLpos.le
    · apply (div_le_iff₀ hLpos).2
      linarith
  have hS : ∀ᶠ N : ℕ in atTop, 0 < S N ∧ S N ≤ 1 := by
    filter_upwards [] with N
    exact ⟨preSieveSingularSeries_pos _, preSieveSingularSeries_le_one _⟩
  have hQ : ∀ᶠ N : ℕ in atTop, 0 < Q N := by
    filter_upwards [hS, hLtop.eventually (eventually_gt_atTop 0)] with
      N hSN hLN
    exact mul_pos hSN.1 hLN
  have hmean : Tendsto (fun N => M N / Q N) atTop (nhds 1) := by
    simpa [M, Q, S, L, D, R, W] using
      tendsto_engelsmaReciprocalGSquarefreeMean_div_leadingTerm_one halpha
  have hmeanPow : Tendsto (fun N => M N ^ k / Q N ^ k)
      atTop (nhds 1) := by
    simpa [div_pow] using hmean.pow k
  have hmassLe : ∀ᶠ N : ℕ in atTop,
      M N ^ k / Q N ^ k ≤ 2 := by
    filter_upwards [hmeanPow.eventually
      (Metric.ball_mem_nhds (1 : ℝ) one_pos)] with N hN
    have hdist : |M N ^ k / Q N ^ k - 1| < 1 := by
      simpa [Real.dist_eq] using hN
    linarith [le_abs_self (M N ^ k / Q N ^ k - 1)]
  have hcond := eventually_engelsmaMaynardCrossBound_conditions halpha
  have hRone := eventually_one_lt_engelsmaMaynardRadius halpha
  have hD2 : ∀ᶠ N : ℕ in atTop, 2 ≤ D N := by
    obtain ⟨M₀, hM₀⟩ := exists_tripleLogCutoff_ge 2
    filter_upwards [eventually_ge_atTop (M₀ + 1)] with N hN
    exact hM₀ (N - 1) (by omega)
  have hLpos : ∀ᶠ N : ℕ in atTop, 0 < L N :=
    hLtop.eventually (eventually_gt_atTop 0)
  have henv : ∀ᶠ N : ℕ in atTop,
      0 ≤ E N / L N ∧ E N / L N ≤ Cenv := by
    filter_upwards [hcond, hD2, hLratio, hAsmall, hS, hLpos] with
      N hCN hD2N hLR hAN hSN hLN
    have hEdiv : E N / L N =
        smallKCandidateBound * 8 * S N * ((1 + L N) / L N) *
          (1 + (k : ℝ) * A N) := by
      dsimp [E, L, S, A, D, R, W]
      unfold engelsmaS2RestrictedTransformEnvelope
      simp only [engelsmaMaynardModulus]
      rw [preSieveSingularSeries_eq_totient_div]
      field_simp [ne_of_gt hLN]
      ring
    have hfac0 : 0 ≤ 1 + (k : ℝ) * A N := by positivity
    have hfacLe : 1 + (k : ℝ) * A N ≤ 1 + (k : ℝ) := by
      simpa [add_comm] using add_le_add_left
        (mul_le_mul_of_nonneg_left hAN.2 (Nat.cast_nonneg k)) 1
    rw [hEdiv]
    constructor
    · simpa [mul_assoc] using
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg smallKCandidateBound_nonneg (by norm_num))
              hSN.1.le)
            hLR.1)
          hfac0)
    · calc
        smallKCandidateBound * 8 * S N * ((1 + L N) / L N) *
            (1 + (k : ℝ) * A N) ≤
          smallKCandidateBound * 8 * 1 * 2 * (1 + (k : ℝ)) := by
            calc
              smallKCandidateBound * 8 * S N * ((1 + L N) / L N) *
                  (1 + (k : ℝ) * A N) ≤
                smallKCandidateBound * 8 * S N * 2 *
                  (1 + (k : ℝ) * A N) := by
                    simpa [mul_assoc] using
                      (mul_le_mul_of_nonneg_right
                        (mul_le_mul_of_nonneg_left hLR.2
                          (mul_nonneg
                            (mul_nonneg smallKCandidateBound_nonneg
                              (by norm_num)) hSN.1.le))
                        hfac0)
              _ ≤ smallKCandidateBound * 8 * S N * 2 *
                  (1 + (k : ℝ)) := by
                    simpa [mul_assoc] using
                      (mul_le_mul_of_nonneg_left hfacLe
                        (mul_nonneg
                          (mul_nonneg
                            (mul_nonneg smallKCandidateBound_nonneg
                              (by norm_num)) hSN.1.le)
                          (by norm_num)))
              _ ≤ smallKCandidateBound * 8 * 1 * 2 *
                  (1 + (k : ℝ)) := by
                    calc
                      smallKCandidateBound * 8 * S N * 2 *
                          (1 + (k : ℝ)) =
                        (smallKCandidateBound * 8 * 2 *
                          (1 + (k : ℝ))) * S N := by ring
                      _ ≤ (smallKCandidateBound * 8 * 2 *
                          (1 + (k : ℝ))) * 1 :=
                        mul_le_mul_of_nonneg_left hSN.2
                          (mul_nonneg
                            (mul_nonneg
                              (mul_nonneg smallKCandidateBound_nonneg
                                (by norm_num)) (by norm_num))
                            (by positivity))
                      _ = smallKCandidateBound * 8 * 1 * 2 *
                          (1 + (k : ℝ)) := by ring
        _ = Cenv := by
          dsimp [Cenv]
          ring
  have htail : Tendsto Tail atTop (nhds 0) := by
    have h := hinvD.const_mul Ctail
    simpa [Tail, Ctail, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using h
  have hzero : Tendsto (fun N => (2 * Cenv ^ 2) * Tail N)
      atTop (nhds 0) := by
    simpa using htail.const_mul (2 * Cenv ^ 2)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun N => abs_nonneg _)) ?_ hzero
  filter_upwards [hcond, hRone, hD2, henv, hmassLe, hQ, hLpos] with
      N hCN hRoneN hD2N hEN hMN hQN hLN
  have hcorr := abs_engelsmaMaynardS2RestrictedCrossCorrection_le_explicit
    m hRoneN hD2N hCN.2.2
  have hden : 0 < Q N ^ k * L N ^ 2 := by positivity
  have hTail0 : 0 ≤ Tail N := by
    dsimp [Tail]
    positivity
  have hMnonneg : 0 ≤ M N := by
    dsimp [M]
    unfold maynardS2ReciprocalGSquarefreeMean
    exact Finset.sum_nonneg fun n hn =>
      maynardS2ReciprocalGSquarefreeAF_nonneg _ n
  have hM0 : 0 ≤ M N ^ k / Q N ^ k := by
    exact div_nonneg (pow_nonneg hMnonneg _) (pow_nonneg hQN.le _)
  have hE0 : 0 ≤ E N / L N := hEN.1
  have hsq : (E N / L N) ^ 2 ≤ Cenv ^ 2 :=
    pow_le_pow_left₀ hE0 hEN.2 2
  rw [normalizedEngelsmaS2RestrictedCrossCorrection,
    abs_div, abs_of_pos hden]
  calc
    |engelsmaMaynardS2RestrictedCrossCorrection alpha N m| /
          (Q N ^ k * L N ^ 2) ≤
        (E N ^ 2 * Tail N * M N ^ k) /
          (Q N ^ k * L N ^ 2) :=
      div_le_div_of_nonneg_right hcorr hden.le
    _ = (E N / L N) ^ 2 * Tail N *
          (M N ^ k / Q N ^ k) := by
      field_simp [ne_of_gt hLN, ne_of_gt hQN]
    _ ≤ Cenv ^ 2 * Tail N * (M N ^ k / Q N ^ k) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsq hTail0) hM0
    _ ≤ Cenv ^ 2 * Tail N * 2 := by
      exact mul_le_mul_of_nonneg_left hMN
        (mul_nonneg (sq_nonneg _) hTail0)
    _ = (2 * Cenv ^ 2) * Tail N := by ring

end BoundedGaps.Maynard
