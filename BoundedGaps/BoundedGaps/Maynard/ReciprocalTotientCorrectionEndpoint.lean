import BoundedGaps.Maynard.ReciprocalTotientCorrectionLogMoment
import Mathlib.NumberTheory.Harmonic.Bounds

noncomputable section

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction Real
open scoped BigOperators ArithmeticFunction.Moebius

/-! Uniform comparison of the corrected mean with its coprime harmonic endpoint. -/

private theorem reciprocalTotientCorrection_local_sum_eq_one
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    (∑' i : ℕ, reciprocalTotientCorrectionAF W (p ^ i)) = 1 := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun i hi => by
    simp only [Finset.mem_range, not_lt] at hi
    rw [reciprocalTotientCorrectionAF_apply_prime_pow_ge_three W hp hi]
)]
  rw [Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [pow_zero, pow_one]
  rw [reciprocalTotientCorrectionAF_apply_prime W hp,
    reciprocalTotientCorrectionAF_apply_prime_sq W hp]
  have hOne : reciprocalTotientCorrectionAF W 1 = 1 :=
    (reciprocalTotientCorrectionAF_multiplicative W).map_one
  rw [hOne]
  by_cases hpW : p ∣ W
  · simp [hpW]
  · rw [if_neg hpW, if_neg hpW]
    norm_num
    field_simp
    ring

theorem tsum_reciprocalTotientCorrectionAF_eq_one (W : ℕ) :
    (∑' n : ℕ, reciprocalTotientCorrectionAF W n) = 1 := by
  have hsum : Summable (fun n : ℕ =>
      ‖reciprocalTotientCorrectionAF W n‖) := by
    simpa [Real.norm_eq_abs] using summable_abs_reciprocalTotientCorrectionAF W
  have hEuler :=
    (reciprocalTotientCorrectionAF_multiplicative W).eulerProduct_tprod hsum
  rw [← hEuler]
  have hprod :
      (∏' p : Nat.Primes,
        ∑' i : ℕ, reciprocalTotientCorrectionAF W ((p : ℕ) ^ i)) =
        ∏' p : Nat.Primes, (1 : ℝ) := by
    apply tprod_congr
    intro p
    exact reciprocalTotientCorrection_local_sum_eq_one W p.property
  rw [hprod]
  simp

theorem coprimeHarmonicSum_sub_div_le_one_add_log
    {W Q d : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) :
    coprimeHarmonicSum W Q - coprimeHarmonicSum W (Q / d) ≤
      1 + Real.log d := by
  unfold coprimeHarmonicSum
  let S : Finset ℕ := (Finset.Icc 1 Q).filter (Nat.Coprime · W)
  let T : Finset ℕ := (Finset.Icc 1 (Q / d)).filter (Nat.Coprime · W)
  have hQT : Q / d ≤ Q := Nat.div_le_self Q d
  have hsub : T ⊆ S := by
    intro n hn
    simp only [T, S, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans hQT⟩, hn.2⟩
  have hdiff := Finset.sum_sdiff (s₁ := T) (s₂ := S)
    (f := fun n : ℕ => (1 : ℝ) / n) hsub
  have hsumDiff :
      (∑ n ∈ S, (1 : ℝ) / n) - ∑ n ∈ T, (1 : ℝ) / n =
        ∑ n ∈ S \ T, (1 : ℝ) / n := by
    linarith
  have hsdiffSub : S \ T ⊆ Finset.Icc 1 Q \ Finset.Icc 1 (Q / d) := by
    intro n hn
    simp only [S, T, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1.1, fun hnB => hn.2 ⟨hnB, hn.1.2⟩⟩
  have htail :
      (∑ n ∈ S \ T, (1 : ℝ) / n) ≤
        (∑ n ∈ Finset.Icc 1 Q, (1 : ℝ) / n) -
          ∑ n ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / n := by
    have hIcc : Finset.Icc 1 (Q / d) ⊆ Finset.Icc 1 Q := by
      intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      exact ⟨hn.1, hn.2.trans hQT⟩
    have hIccDiff := Finset.sum_sdiff (s₁ := Finset.Icc 1 (Q / d))
      (s₂ := Finset.Icc 1 Q) (f := fun n : ℕ => (1 : ℝ) / n) hIcc
    have hsumIcc :
        (∑ n ∈ Finset.Icc 1 Q, (1 : ℝ) / n) -
            ∑ n ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / n =
          ∑ n ∈ Finset.Icc 1 Q \ Finset.Icc 1 (Q / d), (1 : ℝ) / n := by
      linarith
    rw [hsumIcc]
    apply Finset.sum_le_sum_of_subset_of_nonneg hsdiffSub
    intro n hn hnNot
    positivity
  have hharmonicDiff :
      (∑ n ∈ Finset.Icc 1 Q, (1 : ℝ) / n) -
          ∑ n ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / n =
        (harmonic Q : ℝ) - harmonic (Q / d) := by
    rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  have hQpos : 0 < Q := lt_of_lt_of_le hd hdQ
  have hMpos : 0 < Q / d + 1 := Nat.succ_pos _
  have hlogQ : (harmonic Q : ℝ) ≤ 1 + Real.log Q := by
    exact harmonic_le_one_add_log Q
  have hlogM : Real.log ((Q / d : ℕ) + 1) ≤ harmonic (Q / d) := by
    simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic (Q / d)
  have hratio : Real.log Q - Real.log ((Q / d : ℕ) + 1) ≤ Real.log d := by
    have hlt : Q < (Q / d) * d + d := Nat.lt_div_mul_add hd
    have hleNat : Q ≤ ((Q / d) + 1) * d := by
      simpa [Nat.add_mul] using hlt.le
    have hle : (Q : ℝ) / ((Q / d : ℕ) + 1) ≤ d := by
      rw [div_le_iff₀ (by exact_mod_cast hMpos)]
      have hleNat' : Q ≤ d * ((Q / d) + 1) := by
        simpa [mul_comm] using hleNat
      exact_mod_cast hleNat'
    have hlogle := Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < (Q : ℝ) / ((Q / d : ℕ) + 1) by
        exact div_pos (by exact_mod_cast hQpos) (by exact_mod_cast hMpos))
      (show (0 : ℝ) < d by exact_mod_cast hd) hle
    rw [Real.log_div (by exact_mod_cast hQpos.ne')
      (by exact_mod_cast hMpos.ne')] at hlogle
    exact hlogle
  calc
    coprimeHarmonicSum W Q - coprimeHarmonicSum W (Q / d) ≤
        (harmonic Q : ℝ) - harmonic (Q / d) := by
      calc
        _ = ∑ n ∈ S \ T, (1 : ℝ) / n := hsumDiff
        _ ≤ (∑ n ∈ Finset.Icc 1 Q, (1 : ℝ) / n) -
            ∑ n ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / n := htail
        _ = (harmonic Q : ℝ) - harmonic (Q / d) := hharmonicDiff
    _ ≤ 1 + Real.log Q - Real.log ((Q / d : ℕ) + 1) := by linarith
    _ ≤ 1 + Real.log d := by linarith

theorem coprimeHarmonicSum_nonneg (W Q : ℕ) :
    0 ≤ coprimeHarmonicSum W Q := by
  unfold coprimeHarmonicSum
  apply Finset.sum_nonneg
  intro n hn
  positivity

theorem coprimeHarmonicSum_le_harmonic (W Q : ℕ) :
    coprimeHarmonicSum W Q ≤ (harmonic Q : ℝ) := by
  unfold coprimeHarmonicSum
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _)
  intro n hn hnNot
  positivity

theorem coprimeHarmonicSum_mono
    {W A B : ℕ} (hAB : A ≤ B) :
    coprimeHarmonicSum W A ≤ coprimeHarmonicSum W B := by
  unfold coprimeHarmonicSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨hn.1.1, hn.1.2.trans hAB⟩, hn.2⟩
  · intro n hn hnNot
    positivity

private theorem finite_abs_correction_one_add_log_le (W Q : ℕ) :
    (∑ d ∈ Finset.Ioc 0 Q,
      |reciprocalTotientCorrectionAF W d| * (1 + Real.log d)) ≤
      Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant := by
  have hAbs := summable_abs_reciprocalTotientCorrectionAF W
  have hLog := summable_abs_reciprocalTotientCorrection_log W
  have hAbsFinite :
      (∑ d ∈ Finset.Ioc 0 Q, |reciprocalTotientCorrectionAF W d|) ≤
        Real.exp 16 := by
    exact (hAbs.sum_le_tsum (Finset.Ioc 0 Q) (fun n hn => abs_nonneg _)).trans
      (tsum_abs_reciprocalTotientCorrectionAF_le W)
  have hLogFinite :
      (∑ d ∈ Finset.Ioc 0 Q,
        |reciprocalTotientCorrectionAF W d| * Real.log d) ≤
        4 * reciprocalTotientCorrectionQuarterConstant := by
    exact (hLog.sum_le_tsum (Finset.Ioc 0 Q)
      (fun n hn => mul_nonneg (abs_nonneg _) (Real.log_natCast_nonneg n))).trans
      (tsum_abs_reciprocalTotientCorrection_log_le W)
  calc
    (∑ d ∈ Finset.Ioc 0 Q,
        |reciprocalTotientCorrectionAF W d| * (1 + Real.log d)) =
        (∑ d ∈ Finset.Ioc 0 Q,
          |reciprocalTotientCorrectionAF W d|) +
          ∑ d ∈ Finset.Ioc 0 Q,
            |reciprocalTotientCorrectionAF W d| * Real.log d := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant :=
      add_le_add hAbsFinite hLogFinite

set_option maxHeartbeats 2000000 in
private theorem correction_tail_one_add_log_le (W Q : ℕ) :
    (1 + Real.log Q) *
        |(∑ d ∈ Finset.Ioc 0 Q, reciprocalTotientCorrectionAF W d) - 1| ≤
      Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant := by
  let S : Set ℕ := {d | d ∈ Finset.Ioc 0 Q}
  let Sc : Set ℕ := Sᶜ
  have hsumC : Summable (fun n : ℕ => reciprocalTotientCorrectionAF W n) := by
    have hsumNorm : Summable (fun n : ℕ =>
        ‖reciprocalTotientCorrectionAF W n‖) := by
      simpa [Real.norm_eq_abs] using summable_abs_reciprocalTotientCorrectionAF W
    exact hsumNorm.of_norm
  have hsumIoc :
      (∑ d ∈ Finset.Ioc 0 Q, reciprocalTotientCorrectionAF W d) =
        ∑' d : S, reciprocalTotientCorrectionAF W d := by
    rw [_root_.tsum_subtype]
    rw [tsum_eq_sum (s := Finset.Ioc 0 Q) (fun n hn => by
      rw [Set.indicator_of_notMem]
      intro h
      exact hn (by simpa [S] using h))]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Set.indicator_of_mem]
    exact (by simpa [S] using (Finset.mem_Ioc.mp hd))
  have hsplit :
      (∑' d : S, reciprocalTotientCorrectionAF W d) +
          ∑' d : Sc, reciprocalTotientCorrectionAF W d =
        ∑' n : ℕ, reciprocalTotientCorrectionAF W n := by
    simpa [Sc] using hsumC.tsum_subtype_add_tsum_subtype_compl S
  have htailEq :
      (∑ d ∈ Finset.Ioc 0 Q, reciprocalTotientCorrectionAF W d) - 1 =
        -(∑' d : Sc, reciprocalTotientCorrectionAF W d) := by
    rw [hsumIoc]
    linarith [hsplit, tsum_reciprocalTotientCorrectionAF_eq_one W]
  have hAbsComp := (summable_abs_reciprocalTotientCorrectionAF W).subtype Sc
  have hNormComp : Summable (fun d : Sc =>
      ‖reciprocalTotientCorrectionAF W (d : ℕ)‖) :=
    hAbsComp.congr (fun d => by simp [Real.norm_eq_abs])
  have hcompNorm := norm_tsum_le_tsum_norm
    (f := fun d : Sc => reciprocalTotientCorrectionAF W (d : ℕ)) hNormComp
  have hFull : Summable (fun n : ℕ =>
      |reciprocalTotientCorrectionAF W n| * (1 + Real.log n)) := by
    have hA := summable_abs_reciprocalTotientCorrectionAF W
    have hL := summable_abs_reciprocalTotientCorrection_log W
    convert hA.add hL using 1
    ext n
    ring
  have hComp := hFull.subtype Sc
  have hCompBound :
      (∑' d : Sc, |reciprocalTotientCorrectionAF W d| *
        (1 + Real.log d)) ≤
        Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant := by
    have hInj := Summable.tsum_le_tsum_of_inj
      (f := fun d : Sc =>
        |reciprocalTotientCorrectionAF W (d : ℕ)| *
          (1 + Real.log (d : ℕ)))
      (g := fun n : ℕ =>
        |reciprocalTotientCorrectionAF W n| * (1 + Real.log n))
      (fun d : Sc => (d : ℕ)) Subtype.coe_injective
      (fun n _ => mul_nonneg (abs_nonneg _) (by positivity))
      (fun d => le_rfl) hComp hFull
    calc
      (∑' d : Sc, |reciprocalTotientCorrectionAF W d| *
          (1 + Real.log d)) ≤
          ∑' n : ℕ, |reciprocalTotientCorrectionAF W n| *
            (1 + Real.log n) := hInj
      _ = (∑' n : ℕ, |reciprocalTotientCorrectionAF W n|) +
          ∑' n : ℕ, |reciprocalTotientCorrectionAF W n| * Real.log n := by
        rw [← (summable_abs_reciprocalTotientCorrectionAF W).tsum_add
          (summable_abs_reciprocalTotientCorrection_log W)]
        congr 1
        funext n
        ring
      _ ≤ Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant :=
        add_le_add (tsum_abs_reciprocalTotientCorrectionAF_le W)
          (tsum_abs_reciprocalTotientCorrection_log_le W)
  have hLeft : Summable (fun d : Sc =>
      (1 + Real.log Q) * |reciprocalTotientCorrectionAF W d|) :=
    hAbsComp.mul_left _
  have hTailTerm :
      (1 + Real.log Q) *
          |∑' d : Sc, reciprocalTotientCorrectionAF W d| ≤
        ∑' d : Sc, |reciprocalTotientCorrectionAF W d| *
          (1 + Real.log d) := by
    calc
      (1 + Real.log Q) *
          |∑' d : Sc, reciprocalTotientCorrectionAF W d| ≤
          (1 + Real.log Q) *
            ∑' d : Sc, |reciprocalTotientCorrectionAF W d| :=
        mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hcompNorm)
          (by positivity)
      _ = ∑' d : Sc, (1 + Real.log Q) *
          |reciprocalTotientCorrectionAF W d| :=
        (hAbsComp.tsum_mul_left _).symm
      _ ≤ ∑' d : Sc, |reciprocalTotientCorrectionAF W d| *
          (1 + Real.log d) := by
        exact hLeft.tsum_le_tsum (fun d => by
          by_cases hd0 : (d : ℕ) = 0
          · have hc0 : reciprocalTotientCorrectionAF W (d : ℕ) = 0 := by
              rw [hd0]
              exact (reciprocalTotientCorrectionAF W).map_zero
            simp [hc0]
          · have hdQ : Q ≤ (d : ℕ) := by
              have hnot := d.property
              simp only [Sc, S, Set.mem_compl_iff, Set.mem_setOf_eq,
                Finset.mem_Ioc, not_and] at hnot
              omega
            have hlog : Real.log Q ≤ Real.log (d : ℕ) := by
              by_cases hQ0 : Q = 0
              · simp [hQ0, Real.log_natCast_nonneg]
              · apply Real.strictMonoOn_log.monotoneOn
                  (show (0 : ℝ) < Q by exact_mod_cast Nat.pos_of_ne_zero hQ0)
                  (show (0 : ℝ) < (d : ℕ) by
                    exact_mod_cast Nat.pos_of_ne_zero hd0)
                  (by exact_mod_cast hdQ)
            have hnonneg : 0 ≤ |reciprocalTotientCorrectionAF W (d : ℕ)| :=
              abs_nonneg _
            nlinarith) hComp
  rw [htailEq, abs_neg]
  exact hTailTerm.trans hCompBound

set_option maxHeartbeats 800000 in
theorem abs_squarefreeCoprimeInvTotientMean_sub_coprimeHarmonicSum_le
    (W Q : ℕ) :
    |squarefreeCoprimeInvTotientMean W Q - coprimeHarmonicSum W Q| ≤
      2 * (Real.exp 16 +
        4 * reciprocalTotientCorrectionQuarterConstant) := by
  rw [squarefreeCoprimeInvTotientMean_eq_correction_coprimeHarmonic]
  let C := Real.exp 16 + 4 * reciprocalTotientCorrectionQuarterConstant
  let S := Finset.Ioc 0 Q
  let c := reciprocalTotientCorrectionAF W
  let H := coprimeHarmonicSum W Q
  have hdecomp :
      (∑ d ∈ S, c d * coprimeHarmonicSum W (Q / d)) - H =
        (∑ d ∈ S, c d * (coprimeHarmonicSum W (Q / d) - H)) +
          H * ((∑ d ∈ S, c d) - 1) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [hdecomp]
  have hFinite :
      |∑ d ∈ S, c d * (coprimeHarmonicSum W (Q / d) - H)| ≤ C := by
    calc
      |∑ d ∈ S, c d * (coprimeHarmonicSum W (Q / d) - H)| ≤
          ∑ d ∈ S, |c d * (coprimeHarmonicSum W (Q / d) - H)| := by
        simpa [Real.norm_eq_abs] using
          norm_sum_le S (fun d => c d * (coprimeHarmonicSum W (Q / d) - H))
      _ ≤ ∑ d ∈ S, |c d| * (1 + Real.log d) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdData := Finset.mem_Ioc.mp hd
        dsimp [c, H]
        have hmono : coprimeHarmonicSum W (Q / d) ≤ H := by
          unfold H
          exact coprimeHarmonicSum_mono (Nat.div_le_self Q d)
        have hdiff := coprimeHarmonicSum_sub_div_le_one_add_log
          (W := W) hdData.1 hdData.2
        have habsDiff :
            |coprimeHarmonicSum W (Q / d) - H| =
              H - coprimeHarmonicSum W (Q / d) := by
          rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
          ring
        rw [abs_mul, habsDiff]
        exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
      _ ≤ C := by
        exact finite_abs_correction_one_add_log_le W Q
  have hTail :
      |H * ((∑ d ∈ S, c d) - 1)| ≤ C := by
    have hHnonneg : 0 ≤ H := by
      exact coprimeHarmonicSum_nonneg W Q
    have hH : H ≤ 1 + Real.log Q := by
      exact (coprimeHarmonicSum_le_harmonic W Q).trans
        (harmonic_le_one_add_log Q)
    rw [abs_mul, abs_of_nonneg hHnonneg]
    calc
      H * |(∑ d ∈ S, c d) - 1| ≤
          (1 + Real.log Q) * |(∑ d ∈ S, c d) - 1| :=
        mul_le_mul_of_nonneg_right hH (abs_nonneg _)
      _ ≤ C := by
        exact correction_tail_one_add_log_le W Q
  calc
    |(∑ d ∈ S, c d * (coprimeHarmonicSum W (Q / d) - H)) +
        H * ((∑ d ∈ S, c d) - 1)| ≤
        |∑ d ∈ S, c d * (coprimeHarmonicSum W (Q / d) - H)| +
          |H * ((∑ d ∈ S, c d) - 1)| := abs_add_le _ _
    _ ≤ C + C := add_le_add hFinite hTail
    _ = 2 * (Real.exp 16 +
        4 * reciprocalTotientCorrectionQuarterConstant) := by
      unfold C
      ring

end BoundedGaps.Maynard
