import BoundedGaps.Maynard.CoprimeHarmonicMainTerm

noncomputable section

/-!
# Natural-versus-real quotient endpoints

The finite prime-adjunction recurrence uses natural division, while the smooth
main term uses a real quotient. This file isolates the floor loss and carries
it into an exact discrepancy recurrence.
-/

namespace BoundedGaps.Maynard

open Real

theorem abs_log_natDiv_sub_log_div_le_log_two
    {Q p : ℕ} (hp : 0 < p) (hpQ : p ≤ Q) :
    |Real.log (Q / p : ℕ) - Real.log ((Q : ℝ) / p)| ≤ Real.log 2 := by
  let q : ℕ := Q / p
  have hqOne : 1 ≤ q := by
    dsimp [q]
    exact (Nat.le_div_iff_mul_le hp).2 (by simpa [Nat.one_mul] using hpQ)
  have hqPos : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hqOne)
  have hQPos : (0 : ℝ) < Q := by
    exact_mod_cast (hp.trans_le hpQ)
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp
  have hratioPos : (0 : ℝ) < (Q : ℝ) / p := div_pos hQPos hpPos
  have hcastDiv : (q : ℝ) ≤ (Q : ℝ) / p := by
    exact Nat.cast_div_le
  have hQlt : Q < (q + 1) * p := by
    have hmod := Nat.mod_lt Q hp
    have hdecomp := Nat.div_add_mod Q p
    dsimp [q]
    calc
      Q = p * (Q / p) + Q % p := hdecomp.symm
      _ < p * (Q / p) + p := Nat.add_lt_add_left hmod _
      _ = (Q / p + 1) * p := by ring
  have hratioLt : (Q : ℝ) / p < (q + 1 : ℕ) := by
    rw [div_lt_iff₀ hpPos]
    exact_mod_cast hQlt
  have hlogLower : Real.log (q : ℕ) ≤ Real.log ((Q : ℝ) / p) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; exact hqPos)
      (by simp only [Set.mem_Ioi]; exact hratioPos) hcastDiv
  have hsuccLe : (q + 1 : ℕ) ≤ 2 * q := by omega
  have htwo : (Q : ℝ) / p ≤ 2 * (q : ℝ) := by
    have hupper : (Q : ℝ) / p < (q + 1 : ℕ) := hratioLt
    have hsuccCast : ((q + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by
      exact_mod_cast hsuccLe
    exact hupper.le.trans hsuccCast
  have hlogUpper : Real.log ((Q : ℝ) / p) ≤
      Real.log (q : ℕ) + Real.log 2 := by
    have hmono := Real.strictMonoOn_log.monotoneOn hratioPos
      (mul_pos (by norm_num) hqPos) htwo
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hqPos.ne'] at hmono
    linarith
  rw [abs_of_nonpos (sub_nonpos.mpr hlogLower)]
  linarith

noncomputable def coprimeHarmonicError (W Q : ℕ) : ℝ :=
  coprimeHarmonicSum W Q - coprimeHarmonicMainTerm W (Q : ℝ)

theorem coprimeHarmonicError_mul_prime_of_pos
    {W p Q : ℕ} (hW : 0 < W) (hp : p.Prime)
    (hpW : Nat.Coprime p W) (hQ : 0 < Q) :
    coprimeHarmonicError (W * p) Q =
      coprimeHarmonicError W Q -
        (1 : ℝ) / p * coprimeHarmonicError W (Q / p) +
        (1 : ℝ) / p *
          (coprimeHarmonicMainTerm W ((Q : ℝ) / p) -
            coprimeHarmonicMainTerm W ((Q / p : ℕ) : ℝ)) := by
  unfold coprimeHarmonicError
  rw [coprimeHarmonicSum_mul_prime hp hpW,
    coprimeHarmonicMainTerm_mul_prime hW hp hpW (by exact_mod_cast hQ)]
  ring

theorem coprimeHarmonicError_mul_prime
    {W p Q : ℕ} (hW : 0 < W) (hp : p.Prime)
    (hpW : Nat.Coprime p W) (hpQ : p ≤ Q) :
    coprimeHarmonicError (W * p) Q =
      coprimeHarmonicError W Q -
        (1 : ℝ) / p * coprimeHarmonicError W (Q / p) +
        (1 : ℝ) / p *
          (coprimeHarmonicMainTerm W ((Q : ℝ) / p) -
            coprimeHarmonicMainTerm W ((Q / p : ℕ) : ℝ)) := by
  have hQ : 0 < Q := hp.pos.trans_le hpQ
  exact coprimeHarmonicError_mul_prime_of_pos hW hp hpW hQ

theorem coprimeHarmonicError_mul_prime_of_lt
    {W p Q : ℕ} (hW : 0 < W) (hp : p.Prime)
    (hpW : Nat.Coprime p W) (hQ : 0 < Q) (hQp : Q < p) :
    coprimeHarmonicError (W * p) Q =
      coprimeHarmonicError W Q +
        (1 : ℝ) / p * coprimeHarmonicMainTerm W ((Q : ℝ) / p) := by
  rw [coprimeHarmonicError_mul_prime_of_pos hW hp hpW hQ,
    Nat.div_eq_of_lt hQp]
  unfold coprimeHarmonicError coprimeHarmonicSum
  simp
  ring

theorem abs_coprimeHarmonicError_mul_prime_of_lt_le
    {W p Q : ℕ} (hW : 0 < W) (hp : p.Prime)
    (hpW : Nat.Coprime p W) (hQ : 0 < Q) (hQp : Q < p) :
    |coprimeHarmonicError (W * p) Q| ≤
      |coprimeHarmonicError W Q| +
        (1 : ℝ) / p *
          |coprimeHarmonicMainTerm W ((Q : ℝ) / p)| := by
  rw [coprimeHarmonicError_mul_prime_of_lt hW hp hpW hQ hQp]
  calc
    |coprimeHarmonicError W Q +
        (1 : ℝ) / p * coprimeHarmonicMainTerm W ((Q : ℝ) / p)| ≤
      |coprimeHarmonicError W Q| +
        |(1 : ℝ) / p * coprimeHarmonicMainTerm W ((Q : ℝ) / p)| :=
      abs_add_le _ _
    _ = |coprimeHarmonicError W Q| +
        (1 : ℝ) / p *
          |coprimeHarmonicMainTerm W ((Q : ℝ) / p)| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / p)]

theorem abs_coprimeHarmonicMainTerm_realDiv_le
    {W p Q : ℕ} (hW : 0 < W) (hp : p.Prime)
    (hQ : 0 < Q) (hQp : Q < p) :
    |coprimeHarmonicMainTerm W ((Q : ℝ) / p)| ≤
      coprimeHarmonicDensity W *
        (Real.log p + |Real.eulerMascheroniConstant| +
          primeLogPredecessorDivisorMass W) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hQPos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hratioPos : (0 : ℝ) < (Q : ℝ) / p := div_pos hQPos hpPos
  have hlogNonpos : Real.log ((Q : ℝ) / p) ≤ 0 := by
    apply Real.log_nonpos hratioPos.le
    rw [div_le_iff₀ hpPos]
    norm_num
    exact_mod_cast hQp.le
  have hlogAbs : |Real.log ((Q : ℝ) / p)| ≤ Real.log p := by
    rw [abs_of_nonpos hlogNonpos]
    have hlogQNonneg : 0 ≤ Real.log Q :=
      Real.log_nonneg (by exact_mod_cast hQ)
    rw [Real.log_div hQPos.ne' hpPos.ne']
    linarith
  have hmass : 0 ≤ primeLogPredecessorDivisorMass W := by
    unfold primeLogPredecessorDivisorMass
    positivity
  have hdensity : 0 ≤ coprimeHarmonicDensity W := by
    unfold coprimeHarmonicDensity
    positivity
  unfold coprimeHarmonicMainTerm
  rw [abs_mul, abs_of_nonneg hdensity]
  apply mul_le_mul_of_nonneg_left
  · calc
      |Real.log ((Q : ℝ) / p) + Real.eulerMascheroniConstant +
          primeLogPredecessorDivisorMass W| ≤
          |Real.log ((Q : ℝ) / p) + Real.eulerMascheroniConstant| +
          |primeLogPredecessorDivisorMass W| := abs_add_le _ _
      _ ≤ (|Real.log ((Q : ℝ) / p)| +
          |Real.eulerMascheroniConstant|) +
          |primeLogPredecessorDivisorMass W| := by
        exact add_le_add_left (abs_add_le _ _) _
      _ = |Real.log ((Q : ℝ) / p)| +
          |Real.eulerMascheroniConstant| +
          primeLogPredecessorDivisorMass W := by
        rw [abs_of_nonneg hmass]
      _ ≤ Real.log p + |Real.eulerMascheroniConstant| +
          primeLogPredecessorDivisorMass W := by
        exact add_le_add_left
          (add_le_add_left hlogAbs |Real.eulerMascheroniConstant|)
          (primeLogPredecessorDivisorMass W)
  · exact hdensity

theorem abs_coprimeHarmonicError_mul_prime_of_lt_mass_le
    {W p Q : ℕ} (hW : 0 < W) (hp : p.Prime)
    (hpW : Nat.Coprime p W) (hQ : 0 < Q) (hQp : Q < p) :
    |coprimeHarmonicError (W * p) Q| ≤
      |coprimeHarmonicError W Q| +
        coprimeHarmonicDensity W / p *
          (Real.log p + |Real.eulerMascheroniConstant| +
            primeLogPredecessorDivisorMass W) := by
  rw [coprimeHarmonicError_mul_prime_of_lt hW hp hpW hQ hQp]
  have hmain := abs_coprimeHarmonicMainTerm_realDiv_le hW hp hQ hQp
  have hinv : (0 : ℝ) ≤ 1 / p := by positivity
  calc
    |coprimeHarmonicError W Q +
        (1 : ℝ) / p * coprimeHarmonicMainTerm W ((Q : ℝ) / p)| ≤
      |coprimeHarmonicError W Q| +
        (1 : ℝ) / p *
          |coprimeHarmonicMainTerm W ((Q : ℝ) / p)| := by
      calc
        _ ≤ |coprimeHarmonicError W Q| +
            |(1 : ℝ) / p * coprimeHarmonicMainTerm W ((Q : ℝ) / p)| :=
          abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_of_nonneg hinv]
    _ ≤ |coprimeHarmonicError W Q| +
        (1 : ℝ) / p *
          (coprimeHarmonicDensity W *
            (Real.log p + |Real.eulerMascheroniConstant| +
              primeLogPredecessorDivisorMass W)) := by
      gcongr
    _ = |coprimeHarmonicError W Q| +
        coprimeHarmonicDensity W / p *
          (Real.log p + |Real.eulerMascheroniConstant| +
            primeLogPredecessorDivisorMass W) := by ring

theorem abs_coprimeHarmonicMainTerm_natDiv_sub_realDiv_le
    {W p Q : ℕ} (hW : 0 < W) (hp : p.Prime)
    (hpQ : p ≤ Q) :
    |coprimeHarmonicMainTerm W ((Q / p : ℕ) : ℝ) -
        coprimeHarmonicMainTerm W ((Q : ℝ) / p)| ≤
      coprimeHarmonicDensity W * Real.log 2 := by
  have hlog := abs_log_natDiv_sub_log_div_le_log_two hp.pos hpQ
  have hDensity : 0 ≤ coprimeHarmonicDensity W := by
    unfold coprimeHarmonicDensity
    positivity
  unfold coprimeHarmonicMainTerm
  rw [← mul_sub, abs_mul]
  rw [abs_of_nonneg hDensity]
  apply mul_le_mul_of_nonneg_left
  · have hdiff :
        Real.log (Q / p : ℕ) - Real.log ((Q : ℝ) / p) =
          (Real.log ((Q / p : ℕ) : ℝ) + Real.eulerMascheroniConstant +
            primeLogPredecessorDivisorMass W) -
          (Real.log ((Q : ℝ) / p) + Real.eulerMascheroniConstant +
            primeLogPredecessorDivisorMass W) := by ring
    rw [← hdiff]
    exact hlog
  · exact hDensity

theorem abs_coprimeHarmonicError_mul_prime_le
    {W p Q : ℕ} (hW : 0 < W) (hp : p.Prime)
    (hpW : Nat.Coprime p W) (hpQ : p ≤ Q) :
    |coprimeHarmonicError (W * p) Q| ≤
      |coprimeHarmonicError W Q| +
        (1 : ℝ) / p * |coprimeHarmonicError W (Q / p)| +
        coprimeHarmonicDensity W * Real.log 2 / p := by
  rw [coprimeHarmonicError_mul_prime hW hp hpW hpQ]
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hInv : 0 ≤ (1 : ℝ) / p := by positivity
  have hEndpoint :=
    abs_coprimeHarmonicMainTerm_natDiv_sub_realDiv_le hW hp hpQ
  have hEndpoint' :
      |coprimeHarmonicMainTerm W ((Q : ℝ) / p) -
          coprimeHarmonicMainTerm W ((Q / p : ℕ) : ℝ)| ≤
        coprimeHarmonicDensity W * Real.log 2 := by
    simpa [abs_sub_comm] using hEndpoint
  have hfirst :
      |coprimeHarmonicError W Q - (1 : ℝ) / p * coprimeHarmonicError W (Q / p)| ≤
        |coprimeHarmonicError W Q| +
          |(1 : ℝ) / p * coprimeHarmonicError W (Q / p)| := by
    have hAbs :
        |(1 : ℝ) / p * coprimeHarmonicError W (Q / p)| =
          (1 : ℝ) / p * |coprimeHarmonicError W (Q / p)| := by
      rw [abs_mul, abs_of_nonneg hInv]
    have hNegAbs :
        |-(1 : ℝ) / p * coprimeHarmonicError W (Q / p)| =
          (1 : ℝ) / p * |coprimeHarmonicError W (Q / p)| := by
      have hneg : (-(1 : ℝ) / p) * coprimeHarmonicError W (Q / p) =
          -((1 : ℝ) / p * coprimeHarmonicError W (Q / p)) := by ring
      rw [hneg, abs_neg, hAbs]
    calc
      |coprimeHarmonicError W Q - (1 : ℝ) / p *
          coprimeHarmonicError W (Q / p)| =
          |coprimeHarmonicError W Q +
            (-(1 : ℝ) / p * coprimeHarmonicError W (Q / p))| := by
          congr 1
          ring
      _ ≤ |coprimeHarmonicError W Q| +
          |-(1 : ℝ) / p * coprimeHarmonicError W (Q / p)| := abs_add_le _ _
      _ = |coprimeHarmonicError W Q| +
          |(1 : ℝ) / p * coprimeHarmonicError W (Q / p)| := by
          rw [hNegAbs, hAbs]
  calc
    |coprimeHarmonicError W Q - (1 : ℝ) / p * coprimeHarmonicError W (Q / p) +
        (1 : ℝ) / p *
          (coprimeHarmonicMainTerm W ((Q : ℝ) / p) -
            coprimeHarmonicMainTerm W ((Q / p : ℕ) : ℝ))| ≤
        |coprimeHarmonicError W Q| +
          |(1 : ℝ) / p * coprimeHarmonicError W (Q / p)| +
          |(1 : ℝ) / p *
            (coprimeHarmonicMainTerm W ((Q : ℝ) / p) -
              coprimeHarmonicMainTerm W ((Q / p : ℕ) : ℝ))| := by
      calc
        _ ≤ |coprimeHarmonicError W Q -
              (1 : ℝ) / p * coprimeHarmonicError W (Q / p)| +
              |(1 : ℝ) / p *
                (coprimeHarmonicMainTerm W ((Q : ℝ) / p) -
                  coprimeHarmonicMainTerm W ((Q / p : ℕ) : ℝ))| :=
          abs_add_le _ _
        _ ≤ (|coprimeHarmonicError W Q| +
              |(1 : ℝ) / p * coprimeHarmonicError W (Q / p)|) +
              |(1 : ℝ) / p *
                (coprimeHarmonicMainTerm W ((Q : ℝ) / p) -
                  coprimeHarmonicMainTerm W ((Q / p : ℕ) : ℝ))| :=
          add_le_add_left hfirst _
    _ = |coprimeHarmonicError W Q| +
          (1 : ℝ) / p * |coprimeHarmonicError W (Q / p)| +
          (1 : ℝ) / p *
            |coprimeHarmonicMainTerm W ((Q : ℝ) / p) -
              coprimeHarmonicMainTerm W ((Q / p : ℕ) : ℝ)| := by
      rw [abs_mul, abs_of_nonneg hInv, abs_mul, abs_of_nonneg hInv]
    _ ≤ |coprimeHarmonicError W Q| +
          (1 : ℝ) / p * |coprimeHarmonicError W (Q / p)| +
          (1 : ℝ) / p * (coprimeHarmonicDensity W * Real.log 2) := by
      gcongr
    _ = |coprimeHarmonicError W Q| +
          (1 : ℝ) / p * |coprimeHarmonicError W (Q / p)| +
          coprimeHarmonicDensity W * Real.log 2 / p := by ring

end BoundedGaps.Maynard
