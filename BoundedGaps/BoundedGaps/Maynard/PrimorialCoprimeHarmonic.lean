import BoundedGaps.Maynard.PrimorialMobiusMoments
import BoundedGaps.Maynard.PrimePredecessorMertens

noncomputable section

/-! The scalar coprime harmonic main term for a primorial pre-sieve. -/

namespace BoundedGaps.Maynard

open Finset Nat Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable def primorialCoprimeHarmonicMainTerm (D Q : ℕ) : ℝ :=
  preSieveSingularSeries D *
    (Real.log Q + primeLogPredecessorSum D)

private theorem harmonic_natDiv_sub_log_div_bounds
    {Q d : ℕ} (hd : 0 < d) (hdQ : d ≤ Q) :
    0 ≤ realHarmonic (Q / d) - Real.log ((Q : ℝ) / d) ∧
      realHarmonic (Q / d) - Real.log ((Q : ℝ) / d) ≤ 1 := by
  have hQ : 0 < Q := hd.trans_le hdQ
  have hquotPos : 0 < Q / d := Nat.div_pos hdQ hd
  have hratioPos : (0 : ℝ) < (Q : ℝ) / d := by positivity
  have hcastDiv : ((Q / d : ℕ) : ℝ) ≤ (Q : ℝ) / d := Nat.cast_div_le
  have hQlt : Q < (Q / d + 1) * d := by
    have hmod := Nat.mod_lt Q hd
    have hdecomp := Nat.div_add_mod Q d
    calc
      Q = d * (Q / d) + Q % d := hdecomp.symm
      _ < d * (Q / d) + d := Nat.add_lt_add_left hmod _
      _ = (Q / d + 1) * d := by ring
  have hratioLt : (Q : ℝ) / d < ((Q / d + 1 : ℕ) : ℝ) := by
    rw [div_lt_iff₀ (by exact_mod_cast hd)]
    exact_mod_cast hQlt
  have hlogLower : Real.log (Q / d : ℕ) ≤
      Real.log ((Q : ℝ) / d) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; exact_mod_cast hquotPos)
      (by simp only [Set.mem_Ioi]; exact hratioPos) hcastDiv
  have hlogUpper : Real.log ((Q : ℝ) / d) ≤
      Real.log (Q / d + 1 : ℕ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; exact hratioPos)
      (by simp only [Set.mem_Ioi]; positivity) hratioLt.le
  have hharmLower : Real.log (Q / d + 1 : ℕ) ≤ realHarmonic (Q / d) := by
    simpa [realHarmonic] using log_add_one_le_harmonic (Q / d)
  have hharmUpper : realHarmonic (Q / d) ≤
      1 + Real.log (Q / d : ℕ) := by
    simpa [realHarmonic] using harmonic_le_one_add_log (Q / d)
  constructor <;> linarith

theorem primorial_log_divisor_sum_eq_main (D Q : ℕ)
    (hQ : 0 < Q) :
    (∑ d ∈ (primorial D).divisors,
      (ArithmeticFunction.moebius d : ℝ) / d *
        Real.log ((Q : ℝ) / d)) =
      primorialCoprimeHarmonicMainTerm D Q := by
  have hW : 0 < primorial D := primorial_pos D
  have hdensity : primorialMobiusDensity D = preSieveSingularSeries D := by
    rw [primorialMobiusDensity_eq_totient_div,
      preSieveSingularSeries_eq_totient_div]
  unfold primorialCoprimeHarmonicMainTerm
  calc
    (∑ d ∈ (primorial D).divisors,
        (ArithmeticFunction.moebius d : ℝ) / d *
          Real.log ((Q : ℝ) / d)) =
        ∑ d ∈ (primorial D).divisors,
          (ArithmeticFunction.moebius d : ℝ) / d *
            (Real.log Q - Real.log d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdPos := Nat.pos_of_mem_divisors hd
      rw [Real.log_div (by exact_mod_cast hQ.ne')
        (by exact_mod_cast hdPos.ne')]
    _ = Real.log Q * primorialMobiusDensity D -
        primorialMobiusLogMoment D := by
      unfold primorialMobiusDensity primorialMobiusLogMoment
      rw [Finset.mul_sum]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by
      rw [hdensity, primorialMobiusLogMoment_eq]
      change Real.log Q * preSieveSingularSeries D -
          (-preSieveSingularSeries D * primeLogPredecessorSum D) = _
      ring

theorem abs_coprimeHarmonicSum_sub_primorialMainTerm_le
    {D Q : ℕ} (hDQ : primorial D ≤ Q) :
    |coprimeHarmonicSum (primorial D) Q -
      primorialCoprimeHarmonicMainTerm D Q| ≤ primorial D := by
  have hW : 0 < primorial D := primorial_pos D
  have hQ : 0 < Q := hW.trans_le hDQ
  rw [coprimeHarmonicSum_eq_moebius_harmonic hW,
    ← primorial_log_divisor_sum_eq_main D Q hQ, ← Finset.sum_sub_distrib]
  calc
    |∑ d ∈ (primorial D).divisors,
        ((ArithmeticFunction.moebius d : ℝ) / d * realHarmonic (Q / d) -
          (ArithmeticFunction.moebius d : ℝ) / d *
            Real.log ((Q : ℝ) / d))| =
        |∑ d ∈ (primorial D).divisors,
          (ArithmeticFunction.moebius d : ℝ) / d *
            (realHarmonic (Q / d) - Real.log ((Q : ℝ) / d))| := by
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤
        ∑ d ∈ (primorial D).divisors,
          |(ArithmeticFunction.moebius d : ℝ) / d *
            (realHarmonic (Q / d) - Real.log ((Q : ℝ) / d))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ (primorial D).divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdPos := Nat.pos_of_mem_divisors hd
      have hdW := Nat.le_of_dvd hW (Nat.dvd_of_mem_divisors hd)
      have herr := harmonic_natDiv_sub_log_div_bounds hdPos (hdW.trans hDQ)
      have hmuInt := ArithmeticFunction.abs_moebius_le_one (n := d)
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast hmuInt
      have hdReal : (1 : ℝ) ≤ d := by exact_mod_cast hdPos
      have hweight : |(ArithmeticFunction.moebius d : ℝ) / d| ≤ 1 := by
        have hdAbs : |(d : ℝ)| = d := abs_of_pos (by exact_mod_cast hdPos)
        rw [abs_div, hdAbs]
        calc
          |(ArithmeticFunction.moebius d : ℝ)| / d ≤ 1 / (d : ℝ) := by
            gcongr
          _ ≤ 1 := by
            exact (div_le_one (by positivity)).mpr hdReal
      rw [abs_mul, abs_of_nonneg herr.1]
      nlinarith
    _ = ((primorial D).divisors.card : ℝ) := by simp
    _ ≤ primorial D := by exact_mod_cast Nat.card_divisors_le_self (primorial D)

end BoundedGaps.Maynard
