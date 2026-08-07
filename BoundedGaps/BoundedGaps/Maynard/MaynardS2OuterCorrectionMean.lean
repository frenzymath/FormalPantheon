import BoundedGaps.Maynard.MaynardS2OuterCorrectionConvolution
import BoundedGaps.Maynard.MaynardS2OuterCorrectionLogMoment
import BoundedGaps.Maynard.ReciprocalTotientCorrectionEndpoint

noncomputable section

/-! Uniform cumulative estimate for the S2 outer squarefree mean. -/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction Real
open scoped BigOperators

private theorem finite_abs_maynardS2OuterCorrection_one_add_log_le
    (W Q : ℕ) :
    (∑ d ∈ Finset.Ioc 0 Q,
      |maynardS2OuterCorrectionAF W d| * (1 + Real.log d)) ≤
      Real.exp 16 + 8 * maynardS2OuterCorrectionQuarterConstant := by
  have hAbs := summable_abs_maynardS2OuterCorrectionAF W
  have hLog := summable_abs_maynardS2OuterCorrection_log W
  have hAbsFinite :
      (∑ d ∈ Finset.Ioc 0 Q,
        |maynardS2OuterCorrectionAF W d|) ≤ Real.exp 16 := by
    exact (hAbs.sum_le_tsum (Finset.Ioc 0 Q)
      (fun n hn => abs_nonneg _)).trans
        (tsum_abs_maynardS2OuterCorrectionAF_le W)
  have hLogFinite :
      (∑ d ∈ Finset.Ioc 0 Q,
        |maynardS2OuterCorrectionAF W d| * Real.log d) ≤
        8 * maynardS2OuterCorrectionQuarterConstant := by
    exact (hLog.sum_le_tsum (Finset.Ioc 0 Q)
      (fun n hn => mul_nonneg (abs_nonneg _)
        (Real.log_natCast_nonneg n))).trans
          (tsum_abs_maynardS2OuterCorrection_log_le W)
  calc
    (∑ d ∈ Finset.Ioc 0 Q,
        |maynardS2OuterCorrectionAF W d| * (1 + Real.log d)) =
        (∑ d ∈ Finset.Ioc 0 Q,
          |maynardS2OuterCorrectionAF W d|) +
          ∑ d ∈ Finset.Ioc 0 Q,
            |maynardS2OuterCorrectionAF W d| * Real.log d := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ Real.exp 16 + 8 * maynardS2OuterCorrectionQuarterConstant :=
      add_le_add hAbsFinite hLogFinite

set_option maxHeartbeats 2000000 in
private theorem maynardS2OuterCorrection_tail_one_add_log_le
    {D : ℕ} (hD : 2 ≤ D) (Q : ℕ) :
    (1 + Real.log Q) *
        |(∑ d ∈ Finset.Ioc 0 Q,
            maynardS2OuterCorrectionAF (primorial D) d) -
          maynardS2OuterInfiniteSingularTail D| ≤
      Real.exp 16 + 8 * maynardS2OuterCorrectionQuarterConstant := by
  let W := primorial D
  let c := maynardS2OuterCorrectionAF W
  let T := maynardS2OuterInfiniteSingularTail D
  let S : Set ℕ := {d | d ∈ Finset.Ioc 0 Q}
  let Sc : Set ℕ := Sᶜ
  have hsumC : Summable (fun n : ℕ => c n) := by
    have hsumNorm : Summable (fun n : ℕ => ‖c n‖) := by
      simpa [c, Real.norm_eq_abs] using
        summable_abs_maynardS2OuterCorrectionAF W
    exact hsumNorm.of_norm
  have hsumIoc :
      (∑ d ∈ Finset.Ioc 0 Q, c d) = ∑' d : S, c d := by
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
      (∑' d : S, c d) + ∑' d : Sc, c d = ∑' n : ℕ, c n := by
    simpa [Sc] using hsumC.tsum_subtype_add_tsum_subtype_compl S
  have htotal : (∑' n : ℕ, c n) = T := by
    simpa [c, W, T] using
      tsum_maynardS2OuterCorrectionAF_eq_maynardS2OuterInfiniteSingularTail hD
  have htailEq :
      (∑ d ∈ Finset.Ioc 0 Q, c d) - T =
        -(∑' d : Sc, c d) := by
    rw [hsumIoc]
    linarith [hsplit, htotal]
  have hAbsComp := (summable_abs_maynardS2OuterCorrectionAF W).subtype Sc
  have hNormComp : Summable (fun d : Sc => ‖c (d : ℕ)‖) :=
    hAbsComp.congr (fun d => by simp [c, Real.norm_eq_abs])
  have hcompNorm := norm_tsum_le_tsum_norm
    (f := fun d : Sc => c (d : ℕ)) hNormComp
  have hFull : Summable (fun n : ℕ =>
      |c n| * (1 + Real.log n)) := by
    have hA := summable_abs_maynardS2OuterCorrectionAF W
    have hL := summable_abs_maynardS2OuterCorrection_log W
    convert hA.add hL using 1
    ext n
    simp only [c]
    ring
  have hComp := hFull.subtype Sc
  have hCompBound :
      (∑' d : Sc, |c d| * (1 + Real.log d)) ≤
        Real.exp 16 + 8 * maynardS2OuterCorrectionQuarterConstant := by
    have hInj := Summable.tsum_le_tsum_of_inj
      (f := fun d : Sc => |c (d : ℕ)| * (1 + Real.log (d : ℕ)))
      (g := fun n : ℕ => |c n| * (1 + Real.log n))
      (fun d : Sc => (d : ℕ)) Subtype.coe_injective
      (fun n _ => mul_nonneg (abs_nonneg _) (by positivity))
      (fun d => le_rfl) hComp hFull
    calc
      (∑' d : Sc, |c d| * (1 + Real.log d)) ≤
          ∑' n : ℕ, |c n| * (1 + Real.log n) := hInj
      _ = (∑' n : ℕ, |c n|) +
          ∑' n : ℕ, |c n| * Real.log n := by
        rw [← (summable_abs_maynardS2OuterCorrectionAF W).tsum_add
          (summable_abs_maynardS2OuterCorrection_log W)]
        congr 1
        funext n
        simp only [c]
        ring
      _ ≤ Real.exp 16 + 8 * maynardS2OuterCorrectionQuarterConstant :=
        add_le_add (tsum_abs_maynardS2OuterCorrectionAF_le W)
          (tsum_abs_maynardS2OuterCorrection_log_le W)
  have hLeft : Summable (fun d : Sc =>
      (1 + Real.log Q) * |c d|) := hAbsComp.mul_left _
  have hTailTerm :
      (1 + Real.log Q) * |∑' d : Sc, c d| ≤
        ∑' d : Sc, |c d| * (1 + Real.log d) := by
    calc
      (1 + Real.log Q) * |∑' d : Sc, c d| ≤
          (1 + Real.log Q) * ∑' d : Sc, |c d| :=
        mul_le_mul_of_nonneg_left
          (by simpa [c, Real.norm_eq_abs] using hcompNorm) (by positivity)
      _ = ∑' d : Sc, (1 + Real.log Q) * |c d| :=
        (hAbsComp.tsum_mul_left _).symm
      _ ≤ ∑' d : Sc, |c d| * (1 + Real.log d) := by
        exact hLeft.tsum_le_tsum (fun d => by
          by_cases hd0 : (d : ℕ) = 0
          · have hc0 : c (d : ℕ) = 0 := by
              rw [hd0]
              exact (maynardS2OuterCorrectionAF W).map_zero
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
            have hnonneg : 0 ≤ |c (d : ℕ)| := abs_nonneg _
            nlinarith) hComp
  rw [htailEq, abs_neg]
  exact hTailTerm.trans hCompBound

set_option maxHeartbeats 800000 in
theorem abs_maynardS2OuterSquarefreeMean_sub_singularTail_mul_harmonic_le
    {D : ℕ} (hD : 2 ≤ D) (Q : ℕ) :
    |maynardS2OuterSquarefreeMean (primorial D) Q -
        maynardS2OuterInfiniteSingularTail D *
          coprimeHarmonicSum (primorial D) Q| ≤
      2 * (Real.exp 16 +
        8 * maynardS2OuterCorrectionQuarterConstant) := by
  rw [maynardS2OuterSquarefreeMean_eq_correction_coprimeHarmonic]
  let W := primorial D
  let C := Real.exp 16 + 8 * maynardS2OuterCorrectionQuarterConstant
  let S := Finset.Ioc 0 Q
  let c := maynardS2OuterCorrectionAF W
  let H := coprimeHarmonicSum W Q
  let T := maynardS2OuterInfiniteSingularTail D
  have hdecomp :
      (∑ d ∈ S, c d * coprimeHarmonicSum W (Q / d)) - T * H =
        (∑ d ∈ S, c d * (coprimeHarmonicSum W (Q / d) - H)) +
          H * ((∑ d ∈ S, c d) - T) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  change |(∑ d ∈ S, c d * coprimeHarmonicSum W (Q / d)) - T * H| ≤ 2 * C
  rw [hdecomp]
  have hFinite :
      |∑ d ∈ S, c d * (coprimeHarmonicSum W (Q / d) - H)| ≤ C := by
    calc
      |∑ d ∈ S, c d * (coprimeHarmonicSum W (Q / d) - H)| ≤
          ∑ d ∈ S, |c d * (coprimeHarmonicSum W (Q / d) - H)| := by
        simpa [Real.norm_eq_abs] using
          norm_sum_le S (fun d =>
            c d * (coprimeHarmonicSum W (Q / d) - H))
      _ ≤ ∑ d ∈ S, |c d| * (1 + Real.log d) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdData := Finset.mem_Ioc.mp hd
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
        exact finite_abs_maynardS2OuterCorrection_one_add_log_le W Q
  have hTail : |H * ((∑ d ∈ S, c d) - T)| ≤ C := by
    have hHnonneg : 0 ≤ H := coprimeHarmonicSum_nonneg W Q
    have hH : H ≤ 1 + Real.log Q :=
      (coprimeHarmonicSum_le_harmonic W Q).trans
        (harmonic_le_one_add_log Q)
    rw [abs_mul, abs_of_nonneg hHnonneg]
    calc
      H * |(∑ d ∈ S, c d) - T| ≤
          (1 + Real.log Q) * |(∑ d ∈ S, c d) - T| :=
        mul_le_mul_of_nonneg_right hH (abs_nonneg _)
      _ ≤ C := by
        exact maynardS2OuterCorrection_tail_one_add_log_le hD Q
  calc
    |(∑ d ∈ S, c d * (coprimeHarmonicSum W (Q / d) - H)) +
        H * ((∑ d ∈ S, c d) - T)| ≤
        |∑ d ∈ S, c d * (coprimeHarmonicSum W (Q / d) - H)| +
          |H * ((∑ d ∈ S, c d) - T)| := abs_add_le _ _
    _ ≤ C + C := add_le_add hFinite hTail
    _ = 2 * C := by ring

end BoundedGaps.Maynard
