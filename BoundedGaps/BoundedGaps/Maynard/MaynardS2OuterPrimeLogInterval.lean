import BoundedGaps.Maynard.MaynardS2OuterGamma
import BoundedGaps.Maynard.PreSievedPrimeMertens
import Mathlib.Analysis.PSeries

noncomputable section

/-!
Uniform prime-log input for the outer S2 multiplicative weight.
Maynard2013v3, source lines 550--555, with the pre-sieved modulus made
explicit in the interval sum.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real

noncomputable def maynardS2OuterPrimeLogIntervalSum
    (D w z : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE z \ Nat.primesLE (w - 1),
    if p ∣ primorial D then 0 else
      maynardS2OuterGamma p * Real.log p / (p : ℝ)

private noncomputable def maynardS2OuterPrimeLogDefect (p : ℕ) : ℝ :=
  (maynardS2OuterGamma p / (p : ℝ) - 1 / (p : ℝ)) * Real.log p

private theorem maynardS2OuterGamma_prime_defect_le
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    |maynardS2OuterGamma p / (p : ℝ) - 1 / (p : ℝ)| ≤
      1 / ((p : ℝ) - 1) ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hden : 0 < (p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * p + 1 := by
    nlinarith [sq_nonneg ((p : ℝ) - 2)]
  have hnum : 0 ≤ (p : ℝ) ^ 2 - 3 * p + 1 := by
    have haux : 0 ≤ (p : ℝ) * ((p : ℝ) - 3) :=
      mul_nonneg hpR.le (sub_nonneg.mpr hp3R)
    nlinarith [haux]
  have hgammaDiv : maynardS2OuterGamma p / (p : ℝ) =
      ((p : ℝ) - 1) ^ 2 /
        ((p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * p + 1) := by
    rw [maynardS2OuterGamma_eq_fraction hden.ne']
    field_simp [hpR.ne']
  rw [hgammaDiv]
  rw [show ((p : ℝ) - 1) ^ 2 /
      ((p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * p + 1) - 1 / p =
      -((p : ℝ) ^ 2 - 3 * p + 1) /
        (p * ((p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * p + 1)) by
    rw [div_sub_div _ _ hden.ne' hpR.ne']
    congr 1 <;> ring]
  rw [abs_div, abs_neg, abs_of_nonneg hnum]
  rw [abs_of_pos (mul_pos hpR hden)]
  apply (div_le_div_iff₀ (mul_pos hpR hden)
      (sq_pos_of_pos (by linarith : (0 : ℝ) < p - 1))).2
  have hpoly :
      ((p : ℝ) ^ 2 - 3 * p + 1) * (p - 1) ^ 2 ≤
        p * ((p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * p + 1) := by
    have haux : 0 ≤ (p : ℝ) ^ 2 * ((p : ℝ) - 3) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hp3R)
    nlinarith [sq_nonneg ((p : ℝ) - 1), haux]
  simpa using hpoly

private theorem maynardS2OuterPrimeLogDefect_abs_le
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    |maynardS2OuterPrimeLogDefect p| ≤
      8 / (p : ℝ) ^ (3 / 2 : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : Real.log p ≤ (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
    Real.log_natCast_le_rpow_div p (by norm_num)
  have hlog' : Real.log p ≤ 2 * (p : ℝ) ^ (1 / 2 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlog
  have hlogNonneg : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hdef := maynardS2OuterGamma_prime_defect_le hp hp3
  have hweight : 1 / ((p : ℝ) - 1) ^ 2 ≤
      4 / (p : ℝ) ^ 2 := by
    have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    apply (div_le_div_iff₀ (sq_pos_of_pos (by linarith [hp3R] : (0 : ℝ) < p - 1))
      (sq_pos_of_pos hpR)).2
    nlinarith [sq_nonneg ((p : ℝ) - 2), hp3R]
  unfold maynardS2OuterPrimeLogDefect
  rw [abs_mul]
  rw [abs_of_nonneg hlogNonneg]
  calc
    |maynardS2OuterGamma p / (p : ℝ) - 1 / p| * Real.log p ≤
        (1 / ((p : ℝ) - 1) ^ 2) * Real.log p :=
      mul_le_mul_of_nonneg_right hdef hlogNonneg
    _ ≤ (4 / (p : ℝ) ^ 2) * (2 * (p : ℝ) ^ (1 / 2 : ℝ)) := by
      gcongr
    _ = 8 / (p : ℝ) ^ (3 / 2 : ℝ) := by
      have hpow : (p : ℝ) ^ (1 / 2 : ℝ) *
          (p : ℝ) ^ (3 / 2 : ℝ) = (p : ℝ) ^ 2 := by
        calc
          (p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) ^ (3 / 2 : ℝ) =
              (p : ℝ) ^ ((1 / 2 : ℝ) + 3 / 2) :=
            (Real.rpow_add hpR (1 / 2 : ℝ) (3 / 2 : ℝ)).symm
          _ = (p : ℝ) ^ 2 := by norm_num
      field_simp [hpR.ne']
      nlinarith [hpow]

private noncomputable def maynardS2OuterPrimeLogCorrectionConstant : ℝ :=
  ∑' n : ℕ, 8 / (n : ℝ) ^ (3 / 2 : ℝ)

private theorem maynardS2OuterPrimeLogCorrection_summable :
    Summable (fun n : ℕ => 8 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  simpa [div_eq_mul_inv] using
    ((Real.summable_one_div_nat_rpow
      (p := (3 / 2 : ℝ))).mpr (by norm_num)).mul_left 8

private theorem maynardS2OuterPrimeLogCorrectionConstant_nonneg :
    0 ≤ maynardS2OuterPrimeLogCorrectionConstant := by
  unfold maynardS2OuterPrimeLogCorrectionConstant
  exact tsum_nonneg fun n => by positivity

private theorem maynardS2OuterPrimeLogIntervalSum_eq_preSieved_add_defect
    (D w z : ℕ) :
    maynardS2OuterPrimeLogIntervalSum D w z =
      preSievedPrimeLogIntervalSum D w z +
        ∑ p ∈ Nat.primesLE z \ Nat.primesLE (w - 1),
          if p ∣ primorial D then 0 else
            maynardS2OuterPrimeLogDefect p := by
  classical
  unfold maynardS2OuterPrimeLogIntervalSum preSievedPrimeLogIntervalSum
    maynardS2OuterPrimeLogDefect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpd : p ∣ primorial D
  · simp [hpd]
  · simp [hpd]
    ring

theorem exists_uniform_maynardS2OuterPrimeLogInterval_bounds :
    ∃ K : ℝ, 0 < K ∧ ∀ {D w z : ℕ}, 2 ≤ D → 2 ≤ w → w ≤ z →
      -(K + Real.log D) ≤
          maynardS2OuterPrimeLogIntervalSum D w z -
            Real.log ((z : ℝ) / (w : ℝ)) ∧
      maynardS2OuterPrimeLogIntervalSum D w z -
          Real.log ((z : ℝ) / (w : ℝ)) ≤ K := by
  obtain ⟨K₀, hK₀, hbase⟩ :=
    exists_uniform_preSievedPrimeLogInterval_bounds
  let K := K₀ + maynardS2OuterPrimeLogCorrectionConstant
  have hC : 0 ≤ maynardS2OuterPrimeLogCorrectionConstant :=
    maynardS2OuterPrimeLogCorrectionConstant_nonneg
  refine ⟨K, by unfold K; linarith, ?_⟩
  intro D w z hD hw hwz
  let S := Nat.primesLE z \ Nat.primesLE (w - 1)
  have hbase' := hbase (D := D) hw hwz
  have hcorr :
      |∑ p ∈ S, if p ∣ primorial D then 0 else
          maynardS2OuterPrimeLogDefect p| ≤
        maynardS2OuterPrimeLogCorrectionConstant := by
    calc
      |∑ p ∈ S, if p ∣ primorial D then 0 else
            maynardS2OuterPrimeLogDefect p| ≤
          ∑ p ∈ S, |if p ∣ primorial D then 0 else
            maynardS2OuterPrimeLogDefect p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ S, 8 / (p : ℝ) ^ (3 / 2 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpPrime : p.Prime :=
          Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
        by_cases hpd : p ∣ primorial D
        · simp [hpd]
          positivity
        ·
          have hpLeD : ¬p ≤ D := by
            intro hpLe
            exact hpd (hpPrime.dvd_primorial_iff.mpr hpLe)
          have hp3 : 3 ≤ p := by
            have hpLower : D + 1 ≤ p := by omega
            omega
          simp only [if_neg hpd]
          exact maynardS2OuterPrimeLogDefect_abs_le hpPrime hp3
      _ ≤ maynardS2OuterPrimeLogCorrectionConstant := by
        exact maynardS2OuterPrimeLogCorrection_summable.sum_le_tsum S
          (fun p _ => by positivity)
  rw [maynardS2OuterPrimeLogIntervalSum_eq_preSieved_add_defect]
  have hcorr' := abs_le.mp hcorr
  constructor <;> unfold K at * <;> linarith [hbase'.1, hbase'.2]

end BoundedGaps.Maynard
