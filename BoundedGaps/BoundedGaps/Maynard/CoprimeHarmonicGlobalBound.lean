import BoundedGaps.Maynard.CoprimeHarmonicErrorBound

noncomputable section

/-!
# Global density-sensitive coprime-harmonic envelope

The quotient-block estimate controls endpoints below the squarefree modulus;
the resulting `W` penalty is retained explicitly for later range splitting.
-/

namespace BoundedGaps.Maynard

open Real

theorem abs_coprimeHarmonicError_le_global_density_envelope
    {W Q : ℕ} (hW : 0 < W) (hQ : 0 < Q) :
    |coprimeHarmonicError W Q| ≤
      coprimeHarmonicDensity W *
        ((W : ℝ) + 1 + 2 * Real.log Q +
          |Real.eulerMascheroniConstant| +
          primeLogPredecessorDivisorMass W) := by
  have hQlog : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ)
  have hMass : 0 ≤ primeLogPredecessorDivisorMass W := by
    unfold primeLogPredecessorDivisorMass
    positivity
  have hDensity : 0 ≤ coprimeHarmonicDensity W := by
    unfold coprimeHarmonicDensity
    positivity
  have hHarmonic := coprimeHarmonicSum_le (Q := Q) hW
  have hHarmonic' : coprimeHarmonicSum W Q ≤
      coprimeHarmonicDensity W * ((W : ℝ) + 1 + Real.log Q) := by
    unfold coprimeHarmonicDensity at *
    have hWReal : (0 : ℝ) < W := by exact_mod_cast hW
    have hH := hHarmonic
    have hH' : ((harmonic Q : ℚ) : ℝ) ≤ 1 + Real.log Q := by
      exact harmonic_le_one_add_log Q
    calc
      coprimeHarmonicSum W Q ≤
          (Nat.totient W : ℝ) *
            (1 + ((harmonic Q : ℚ) : ℝ) / W) := hH
      _ ≤ (Nat.totient W : ℝ) *
          (1 + (1 + Real.log Q) / W) := by
        gcongr
      _ = ((Nat.totient W : ℝ) / W) *
          ((W : ℝ) + 1 + Real.log Q) := by
        field_simp
        ring
  unfold coprimeHarmonicError
  calc
    |coprimeHarmonicSum W Q - coprimeHarmonicMainTerm W (Q : ℝ)| ≤
        coprimeHarmonicSum W Q +
          |coprimeHarmonicMainTerm W (Q : ℝ)| := by
      have hAbs := abs_sub_le (coprimeHarmonicSum W Q) 0
        (coprimeHarmonicMainTerm W (Q : ℝ))
      have hHnonneg : 0 ≤ coprimeHarmonicSum W Q := by
        unfold coprimeHarmonicSum
        positivity
      simpa [abs_of_nonneg hHnonneg, abs_neg]
        using hAbs
    _ ≤ coprimeHarmonicDensity W *
          ((W : ℝ) + 1 + Real.log Q) +
        coprimeHarmonicDensity W *
          (Real.log Q + |Real.eulerMascheroniConstant| +
            primeLogPredecessorDivisorMass W) := by
      apply add_le_add hHarmonic'
      unfold coprimeHarmonicMainTerm
      rw [abs_mul, abs_of_nonneg hDensity]
      apply mul_le_mul_of_nonneg_left
      · calc
          |Real.log Q + Real.eulerMascheroniConstant +
              primeLogPredecessorDivisorMass W| ≤
              |Real.log Q + Real.eulerMascheroniConstant| +
                |primeLogPredecessorDivisorMass W| := abs_add_le _ _
          _ ≤ (|Real.log Q| + |Real.eulerMascheroniConstant|) +
              |primeLogPredecessorDivisorMass W| := by
            exact add_le_add_left
              (abs_add_le (Real.log Q) Real.eulerMascheroniConstant)
              |primeLogPredecessorDivisorMass W|
          _ = Real.log Q + |Real.eulerMascheroniConstant| +
              primeLogPredecessorDivisorMass W := by
            rw [abs_of_nonneg hQlog, abs_of_nonneg hMass]
          _ ≤ _ := le_rfl
      · exact hDensity
    _ = coprimeHarmonicDensity W *
          ((W : ℝ) + 1 + 2 * Real.log Q +
            |Real.eulerMascheroniConstant| +
            primeLogPredecessorDivisorMass W) := by ring

theorem abs_log_natFloor_sub_log_le_log_two_global
    {t : ℝ} (ht : 1 ≤ t) :
    |Real.log (⌊t⌋₊ : ℕ) - Real.log t| ≤ Real.log 2 := by
  let q : ℕ := ⌊t⌋₊
  have hqOne : 1 ≤ q := by
    exact (Nat.one_le_floor_iff t).2 ht
  have hqPos : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hqOne
  have htPos : 0 < t := zero_lt_one.trans_le ht
  have hqt : (q : ℝ) ≤ t := by exact Nat.floor_le htPos.le
  have htSucc : t < (q : ℝ) + 1 := by
    simpa [q, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one t
  have hsuccTwo : (q : ℝ) + 1 ≤ 2 * q := by
    exact_mod_cast (show q + 1 ≤ 2 * q by omega)
  have htTwo : t ≤ 2 * (q : ℝ) := htSucc.le.trans hsuccTwo
  have hlogLower : Real.log q ≤ Real.log t :=
    Real.strictMonoOn_log.monotoneOn hqPos htPos hqt
  have htwoPos : (0 : ℝ) < 2 * q := mul_pos (by norm_num) hqPos
  have hlogUpper : Real.log t ≤ Real.log q + Real.log 2 := by
    have hmono := Real.strictMonoOn_log.monotoneOn htPos htwoPos htTwo
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hqPos.ne'] at hmono
    linarith
  rw [abs_of_nonpos (sub_nonpos.mpr hlogLower)]
  linarith

theorem abs_coprimeHarmonicSum_natFloor_sub_mainTerm_le_global
    {W : ℕ} (hW : 0 < W) {t : ℝ} (ht : 1 ≤ t) :
    |coprimeHarmonicSum W ⌊t⌋₊ -
        coprimeHarmonicMainTerm W t| ≤
      coprimeHarmonicDensity W *
        ((W : ℝ) + 1 + 2 * Real.log t +
          |Real.eulerMascheroniConstant| +
          primeLogPredecessorDivisorMass W + Real.log 2) := by
  let q : ℕ := ⌊t⌋₊
  have hqOne : 1 ≤ q := by exact (Nat.one_le_floor_iff t).2 ht
  have hqPos : 0 < q := Nat.zero_lt_of_lt hqOne
  have hGlobal := abs_coprimeHarmonicError_le_global_density_envelope
    hW hqPos
  have hFloor := abs_log_natFloor_sub_log_le_log_two_global ht
  have hFloor' : |Real.log (q : ℝ) - Real.log t| ≤ Real.log 2 := by
    simpa [q] using hFloor
  have hlogdiff : Real.log t - Real.log (q : ℝ) ≤ Real.log 2 := by
    have h := (abs_le.mp hFloor')
    linarith
  have hDensity : 0 ≤ coprimeHarmonicDensity W := by
    unfold coprimeHarmonicDensity
    positivity
  have hlogq : Real.log (q : ℝ) ≤ Real.log t := by
    apply Real.strictMonoOn_log.monotoneOn
    · simp only [Set.mem_Ioi]
      exact_mod_cast hqPos
    · exact zero_lt_one.trans_le ht
    · exact Nat.floor_le (by linarith)
  change |coprimeHarmonicSum W q - coprimeHarmonicMainTerm W t| ≤ _
  calc
    |coprimeHarmonicSum W q - coprimeHarmonicMainTerm W t| ≤
        |coprimeHarmonicSum W q - coprimeHarmonicMainTerm W (q : ℝ)| +
          |coprimeHarmonicMainTerm W (q : ℝ) -
            coprimeHarmonicMainTerm W t| := by
      rw [show coprimeHarmonicSum W q - coprimeHarmonicMainTerm W t =
          (coprimeHarmonicSum W q - coprimeHarmonicMainTerm W (q : ℝ)) +
            (coprimeHarmonicMainTerm W (q : ℝ) -
              coprimeHarmonicMainTerm W t) by ring]
      exact abs_add_le _ _
    _ ≤ coprimeHarmonicDensity W *
          ((W : ℝ) + 1 + 2 * Real.log q +
            |Real.eulerMascheroniConstant| +
            primeLogPredecessorDivisorMass W) +
        coprimeHarmonicDensity W * Real.log 2 := by
      apply add_le_add hGlobal
      unfold coprimeHarmonicMainTerm
      have hdiff :
          coprimeHarmonicDensity W *
              (Real.log (q : ℝ) + Real.eulerMascheroniConstant +
                primeLogPredecessorDivisorMass W) -
            coprimeHarmonicDensity W *
              (Real.log t + Real.eulerMascheroniConstant +
                primeLogPredecessorDivisorMass W) =
          coprimeHarmonicDensity W * (Real.log (q : ℝ) - Real.log t) := by
        ring
      rw [hdiff, abs_mul, abs_of_nonneg hDensity]
      apply mul_le_mul_of_nonneg_left
      · rw [abs_of_nonpos (sub_nonpos.mpr hlogq)]
        linarith [hlogdiff]
      · exact hDensity
    _ ≤ coprimeHarmonicDensity W *
          ((W : ℝ) + 1 + 2 * Real.log t +
            |Real.eulerMascheroniConstant| +
            primeLogPredecessorDivisorMass W + Real.log 2) := by
      calc
        coprimeHarmonicDensity W *
              ((W : ℝ) + 1 + 2 * Real.log q +
                |Real.eulerMascheroniConstant| +
                primeLogPredecessorDivisorMass W) +
            coprimeHarmonicDensity W * Real.log 2 =
            coprimeHarmonicDensity W *
              (((W : ℝ) + 1 + 2 * Real.log q +
                |Real.eulerMascheroniConstant| +
                primeLogPredecessorDivisorMass W) + Real.log 2) := by ring
        _ ≤ coprimeHarmonicDensity W *
              ((W : ℝ) + 1 + 2 * Real.log t +
                |Real.eulerMascheroniConstant| +
                primeLogPredecessorDivisorMass W + Real.log 2) := by
          apply mul_le_mul_of_nonneg_left
          · linarith [hlogq]
          · exact hDensity

end BoundedGaps.Maynard
