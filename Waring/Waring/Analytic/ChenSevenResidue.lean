import Waring.Analytic.ChenSevenPartition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Residue-class reduction in the small range of Chen's Lemma 7

This file isolates the sum-to-integral input cited from Vinogradov and proves
all finite residue-class algebra around it [CHEN1964-EN, p. 1552;
CHEN1964-ZH, p. 719].
-/

namespace Waring.Analytic

open scoped BigOperators Interval

/-- The perturbation sum over `1 <= x <= P` in one residue class modulo `q`. -/
noncomputable def residueFifthPerturbationSum
    (q : Nat) [NeZero q] (z : Real) (P : Nat) (y : ZMod q) : Complex :=
  ∑ i ∈ Finset.range P,
    if (((1 + i : Nat) : ZMod q) = y) then
      Complex.exp (Complex.I * fifthPerturbationPhase z 1 i)
    else 0

/-- The continuous perturbation integral in Chen's residue approximation. -/
noncomputable def fifthPerturbationIntegral (z : Real) (P : Nat) : Complex :=
  ∫ t in (0 : Real)..P,
    Complex.exp (Complex.I * ((2 * Real.pi * z * t ^ 5 : Real) : Complex))

/-- Exact finite decomposition of the source exponential sum by residue
classes modulo `q`. -/
theorem sum_range_exp_fifth_eq_sum_residueFifthPerturbationSum
    (q : Nat) [NeZero q] (a : Nat) (z : Real) (P : Nat) :
    (∑ i ∈ Finset.range P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))) =
      ∑ y : ZMod q,
        ZMod.stdAddChar ((a : ZMod q) * y ^ 5) *
          residueFifthPerturbationSum q z P y := by
  unfold residueFifthPerturbationSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5))) =
        Complex.exp (Complex.I * fifthPerturbationPhase z 1 i) *
          rationalFifthBlock (a : ZMod q) 1 i :=
      (exp_fifthPerturbationPhase_mul_rationalFifthBlock_natCast
        q a 1 i z).symm
    _ = ZMod.stdAddChar
          ((a : ZMod q) * (((1 + i : Nat) : ZMod q) ^ 5)) *
        Complex.exp (Complex.I * fifthPerturbationPhase z 1 i) := by
      unfold rationalFifthBlock
      ring
    _ = ∑ y : ZMod q,
        ZMod.stdAddChar ((a : ZMod q) * y ^ 5) *
          if (((1 + i : Nat) : ZMod q) = y) then
            Complex.exp (Complex.I * fifthPerturbationPhase z 1 i)
          else 0 := by
      simp

/-- The one-class sum-to-integral estimate that remains to be reconstructed
from the proof of Vinogradov's cited lemma. -/
def ChenSevenResidueApproximation : Prop :=
  ∀ (q : Nat) [NeZero q] (z : Real) (P : Nat), 0 < P →
    |z| ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4) →
      ∀ y : ZMod q,
        ‖residueFifthPerturbationSum q z P y -
          (q : Complex)⁻¹ * fifthPerturbationIntegral z P‖ ≤ 6

/-- Uniform one-class error at most six aggregates to Chen's error `6*q`. -/
theorem norm_sum_range_exp_fifth_sub_complete_mul_integral_le
    (happrox : ChenSevenResidueApproximation)
    (q : Nat) [NeZero q] (a : Nat) (z : Real) (P : Nat)
    (hP : 0 < P)
    (hz : |z| ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    ‖(∑ i ∈ Finset.range P,
          Complex.exp
            (2 * Real.pi * Complex.I *
              (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))) -
        (q : Complex)⁻¹ * completePowerSum 5 (a : ZMod q) *
          fifthPerturbationIntegral z P‖ ≤
      6 * q := by
  rw [sum_range_exp_fifth_eq_sum_residueFifthPerturbationSum]
  have hcomplete :
      completePowerSum 5 (a : ZMod q) =
        ∑ y : ZMod q, ZMod.stdAddChar ((a : ZMod q) * y ^ 5) := by
    rfl
  rw [hcomplete]
  have hdistribute :
      (q : Complex)⁻¹ *
            (∑ y : ZMod q, ZMod.stdAddChar ((a : ZMod q) * y ^ 5)) *
            fifthPerturbationIntegral z P =
        ∑ y : ZMod q,
          ZMod.stdAddChar ((a : ZMod q) * y ^ 5) *
            ((q : Complex)⁻¹ * fifthPerturbationIntegral z P) := by
    calc
      (q : Complex)⁻¹ *
            (∑ y : ZMod q, ZMod.stdAddChar ((a : ZMod q) * y ^ 5)) *
            fifthPerturbationIntegral z P =
          (∑ y : ZMod q, ZMod.stdAddChar ((a : ZMod q) * y ^ 5)) *
            ((q : Complex)⁻¹ * fifthPerturbationIntegral z P) := by ring
      _ = ∑ y : ZMod q,
          ZMod.stdAddChar ((a : ZMod q) * y ^ 5) *
            ((q : Complex)⁻¹ * fifthPerturbationIntegral z P) := by
        rw [Finset.sum_mul]
  rw [hdistribute, ← Finset.sum_sub_distrib]
  calc
    ‖∑ y : ZMod q,
        (ZMod.stdAddChar ((a : ZMod q) * y ^ 5) *
            residueFifthPerturbationSum q z P y -
          ZMod.stdAddChar ((a : ZMod q) * y ^ 5) *
            ((q : Complex)⁻¹ * fifthPerturbationIntegral z P))‖ ≤
        ∑ y : ZMod q,
          ‖ZMod.stdAddChar ((a : ZMod q) * y ^ 5) *
              residueFifthPerturbationSum q z P y -
            ZMod.stdAddChar ((a : ZMod q) * y ^ 5) *
              ((q : Complex)⁻¹ * fifthPerturbationIntegral z P)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _y : ZMod q, (6 : Real) := by
      apply Finset.sum_le_sum
      intro y _
      rw [← mul_sub, norm_mul, norm_stdAddChar, one_mul]
      exact happrox q z P hP hz y
    _ = 6 * q := by simp [mul_comm]

/-- The perturbation integral is bounded trivially by the interval length. -/
theorem norm_fifthPerturbationIntegral_le (z : Real) (P : Nat) :
    ‖fifthPerturbationIntegral z P‖ ≤ P := by
  unfold fifthPerturbationIntegral
  calc
    ‖∫ t in (0 : Real)..P,
        Complex.exp
          (Complex.I * ((2 * Real.pi * z * t ^ 5 : Real) : Complex))‖ ≤
        1 * |(P : Real) - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t _
      rw [Complex.norm_exp_I_mul_ofReal]
    _ = P := by simp

/-- Chen's pre-numerical small-range estimate, conditional only on the
single-class sum-to-integral approximation. -/
theorem norm_sum_range_exp_fifth_le_of_residueApproximation
    (happrox : ChenSevenResidueApproximation)
    (q : Nat) [NeZero q] (a : Nat) (z : Real) (P : Nat)
    (hP : 0 < P) (ha : IsUnit (a : ZMod q))
    (hz : |z| ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    ‖∑ i ∈ Finset.range P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))‖ ≤
      40 * P * (q : Real) ^ (-1 / 5 : Real) + 6 * q := by
  have hqPos : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hComplete := chen_two_completePowerSum_bound (a : ZMod q) ha
  have hIntegral := norm_fifthPerturbationIntegral_le z P
  have hMain :
      ‖(q : Complex)⁻¹ * completePowerSum 5 (a : ZMod q) *
          fifthPerturbationIntegral z P‖ ≤
        40 * P * (q : Real) ^ (-1 / 5 : Real) := by
    calc
      ‖(q : Complex)⁻¹ * completePowerSum 5 (a : ZMod q) *
          fifthPerturbationIntegral z P‖ =
          (q : Real)⁻¹ * ‖completePowerSum 5 (a : ZMod q)‖ *
            ‖fifthPerturbationIntegral z P‖ := by
        rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
      _ ≤ (q : Real)⁻¹ * (40 * (q : Real) ^ (4 / 5 : Real)) *
          ‖fifthPerturbationIntegral z P‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hComplete (by positivity))
          (norm_nonneg _)
      _ ≤ (q : Real)⁻¹ * (40 * (q : Real) ^ (4 / 5 : Real)) * P :=
        mul_le_mul_of_nonneg_left hIntegral (by positivity)
      _ = 40 * P * (q : Real) ^ (-1 / 5 : Real) := by
        rw [← Real.rpow_neg_one]
        calc
          (q : Real) ^ (-1 : Real) *
                (40 * (q : Real) ^ (4 / 5 : Real)) * P =
              40 * P *
                ((q : Real) ^ (-1 : Real) *
                  (q : Real) ^ (4 / 5 : Real)) := by ring
          _ = 40 * P *
              (q : Real) ^ ((-1 : Real) + 4 / 5) := by
            rw [← Real.rpow_add hqPos]
          _ = 40 * P * (q : Real) ^ (-1 / 5 : Real) := by norm_num
  have hError :=
    norm_sum_range_exp_fifth_sub_complete_mul_integral_le
      happrox q a z P hP hz
  calc
    ‖∑ i ∈ Finset.range P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))‖ ≤
        ‖(q : Complex)⁻¹ * completePowerSum 5 (a : ZMod q) *
            fifthPerturbationIntegral z P‖ +
          ‖(∑ i ∈ Finset.range P,
              Complex.exp
                (2 * Real.pi * Complex.I *
                  (((a : Real) / q + z) *
                    (((1 + i : Nat) : Real) ^ 5)))) -
            (q : Complex)⁻¹ * completePowerSum 5 (a : ZMod q) *
              fifthPerturbationIntegral z P‖ :=
      norm_le_norm_add_norm_sub' _ _
    _ ≤ 40 * P * (q : Real) ^ (-1 / 5 : Real) + 6 * q :=
      add_le_add hMain hError

/-- Chen's small-denominator conclusion, assuming the one-class
residue approximation. -/
theorem chenSeven_smallDenominator_bound_of_residueApproximation
    (happrox : ChenSevenResidueApproximation)
    (q : Nat) [NeZero q] (a : Nat) (z : Real) (P : Nat)
    (hPThreshold : (10 : Real) ^ 150 ≤ P)
    (hqLower : (P : Real) ^ (1 / 2 : Real) ≤ q)
    (hqUpper : (q : Real) ≤ (P : Real) ^ (19 / 20 : Real))
    (ha : IsUnit (a : ZMod q))
    (hz : |z| ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    ‖∑ i ∈ Finset.range P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))‖ ≤
      (P : Real) ^ (24 / 25 : Real) := by
  have hPReal : (0 : Real) < P :=
    (by positivity : (0 : Real) < 10 ^ 150).trans_le hPThreshold
  have hP : 0 < P := by exact_mod_cast hPReal
  exact
    (norm_sum_range_exp_fifth_le_of_residueApproximation
      happrox q a z P hP ha hz).trans
        (chenSeven_smallDenominator_numerical
          hPThreshold hqLower hqUpper)

-- The nonzero modulus remains in the residue-family definition so its public
-- signature is uniform with every theorem that consumes the sum.
attribute [nolint unusedArguments] residueFifthPerturbationSum

end Waring.Analytic
