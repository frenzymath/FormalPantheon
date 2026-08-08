import Waring.Analytic.ChenTenSingularIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Shift averages of Chen's singular integral

This file develops the positive shift exponential sum and relates its square
to shifted representation counts. It then translates and combines interval
integrals so the finite shift average can be compared with the whole-line
singular integral.
-/

set_option autoImplicit false

namespace Waring.Analytic

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

/-- The positive shift Weyl sum for shifts `1, ..., M`. -/
def chenTenPositiveShiftSum (M : Nat) (alpha : Real) : Complex :=
  ∑ j : Fin M,
    Complex.exp
      (2 * Real.pi * Complex.I * (alpha * (j.val.succ : Real)))

/-- Subtracting a natural shift from the target factors the target phase. -/
theorem chenTenTargetPhase_nat_sub_shift
    (N d : Nat) (hd : d ≤ N) (alpha : Real) :
    chenTenTargetPhase (N - d) alpha =
      chenTenTargetPhase N alpha *
        Complex.exp
          (2 * Real.pi * Complex.I * (alpha * (d : Real))) := by
  unfold chenTenTargetPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  rw [Nat.cast_sub hd]
  ring

/-- Squaring the positive shift sum expands into the double sum of combined shifts. -/
theorem chenTenPositiveShiftSum_sq_eq_pair_sum
    (M : Nat) (alpha : Real) :
    chenTenPositiveShiftSum M alpha ^ 2 =
      ∑ j : Fin M, ∑ k : Fin M,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (alpha * ((j.val.succ + k.val.succ : Nat) : Real))) := by
  unfold chenTenPositiveShiftSum
  rw [pow_two, Fintype.sum_mul_sum]
  apply Fintype.sum_congr
  intro j
  apply Fintype.sum_congr
  intro k
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The norm of the positive shift sum is bounded by its number of terms. -/
theorem norm_chenTenPositiveShiftSum_le (M : Nat) (alpha : Real) :
    ‖chenTenPositiveShiftSum M alpha‖ ≤ (M : Real) := by
  unfold chenTenPositiveShiftSum
  calc
    ‖∑ j : Fin M,
        Complex.exp
          (2 * Real.pi * Complex.I * (alpha * (j.val.succ : Real)))‖ ≤
        ∑ _j : Fin M, ‖Complex.exp
          (2 * Real.pi * Complex.I * (alpha * (_j.val.succ : Real)))‖ :=
      norm_sum_le _ _
    _ = (M : Real) := by
      simp only [Complex.norm_exp]
      simp

/-- The squared positive shift sum has norm at most `M ^ 2`. -/
theorem norm_chenTenPositiveShiftSum_sq_le (M : Nat) (alpha : Real) :
    ‖chenTenPositiveShiftSum M alpha ^ 2‖ ≤ (M : Real) ^ 2 := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_chenTenPositiveShiftSum_le M alpha) 2

/-- Two positive indices bounded by `M` have sum at most `N` when `2 * M ≤ N`. -/
theorem fin_succ_add_succ_le_of_two_mul_le
    {M N : Nat} (hMN : 2 * M ≤ N) (j k : Fin M) :
    j.val.succ + k.val.succ ≤ N := by
  have hj : j.val.succ ≤ M := by omega
  have hk : k.val.succ ≤ M := by omega
  omega

/-- The double sum of shifted representation counts equals the weighted integral
on any unit interval. -/
theorem sum_shifted_positiveFifthPowerRepresentationCount_eq_unitIntegral
    (P N M : Nat) (c : Real) (hMN : 2 * M ≤ N) :
    (∑ j : Fin M, ∑ k : Fin M,
      (positiveFifthPowerRepresentationCount 15 P
        (N - j.val.succ - k.val.succ) : Complex)) =
      ∫ alpha in c..c + 1,
        fifthPowerExponentialSum P alpha ^ 15 *
          chenTenTargetPhase N alpha *
      chenTenPositiveShiftSum M alpha ^ 2 := by
  have hcontF : Continuous (fifthPowerExponentialSum P) := by
    unfold fifthPowerExponentialSum realFifthPowerExponential realFifthPowerPhase
    fun_prop
  have hcontPhase (Q : Nat) : Continuous (chenTenTargetPhase Q) := by
    unfold chenTenTargetPhase
    fun_prop
  have hcount (j k : Fin M) :
      (positiveFifthPowerRepresentationCount 15 P
        (N - j.val.succ - k.val.succ) : Complex) =
        ∫ alpha in c..c + 1,
          fifthPowerExponentialSum P alpha ^ 15 *
            chenTenTargetPhase (N - j.val.succ - k.val.succ) alpha := by
    symm
    exact integral_fifthPowerExponentialSum_pow_eq_count
      15 P (N - j.val.succ - k.val.succ) c
  simp_rw [hcount]
  symm
  have hphase (alpha : Real) (j k : Fin M) :
      chenTenTargetPhase (N - j.val.succ - k.val.succ) alpha =
        chenTenTargetPhase N alpha *
          Complex.exp
            (2 * Real.pi * Complex.I *
              (alpha * ((j.val.succ + k.val.succ : Nat) : Real))) := by
    rw [Nat.sub_sub]
    exact chenTenTargetPhase_nat_sub_shift N
      (j.val.succ + k.val.succ)
      (fin_succ_add_succ_le_of_two_mul_le hMN j k) alpha
  have hintegrand (alpha : Real) :
      fifthPowerExponentialSum P alpha ^ 15 *
          chenTenTargetPhase N alpha *
            chenTenPositiveShiftSum M alpha ^ 2 =
        ∑ j : Fin M, ∑ k : Fin M,
          fifthPowerExponentialSum P alpha ^ 15 *
            chenTenTargetPhase (N - j.val.succ - k.val.succ) alpha := by
    rw [chenTenPositiveShiftSum_sq_eq_pair_sum]
    simp_rw [hphase]
    simp only [Finset.mul_sum]
    simp only [mul_assoc]
  apply (intervalIntegral.integral_congr (fun alpha _ => hintegrand alpha)).trans
  rw [intervalIntegral.integral_finsetSum (h := by
    intro j _
    have hsum : IntervalIntegrable
        (∑ k : Fin M, fun x : Real =>
          fifthPowerExponentialSum P x ^ 15 *
            chenTenTargetPhase (N - j.val.succ - k.val.succ) x)
        volume c (c + 1) := by
      apply IntervalIntegrable.sum (μ := volume) (a := c) (b := c + 1)
        Finset.univ
      intro k _
      exact Continuous.intervalIntegrable (μ := volume) (a := c) (b := c + 1)
        ((hcontF.pow 15).mul
          (hcontPhase (N - j.val.succ - k.val.succ)))
    have hfun :
        (fun x : Real => ∑ k : Fin M,
          fifthPowerExponentialSum P x ^ 15 *
            chenTenTargetPhase (N - j.val.succ - k.val.succ) x) =
          (∑ k : Fin M, fun x : Real =>
            fifthPowerExponentialSum P x ^ 15 *
              chenTenTargetPhase (N - j.val.succ - k.val.succ) x) := by
      funext x
      simp
    rw [hfun]
    exact hsum)]
  · apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_finsetSum (h := by
      intro k _
      exact Continuous.intervalIntegrable (μ := volume) (a := c) (b := c + 1)
        ((hcontF.pow 15).mul
          (hcontPhase (N - j.val.succ - k.val.succ))) )]

/-- The shifted representation-count identity specialized to Chen's translated unit interval. -/
theorem sum_shifted_positiveFifthPowerRepresentationCount_eq_chenInterval
    (P N M : Nat) (tau : Real) (hMN : 2 * M ≤ N) :
    (∑ j : Fin M, ∑ k : Fin M,
      (positiveFifthPowerRepresentationCount 15 P
        (N - j.val.succ - k.val.succ) : Complex)) =
      ∫ alpha in -tau⁻¹..1 - tau⁻¹,
        fifthPowerExponentialSum P alpha ^ 15 *
          chenTenTargetPhase N alpha *
            chenTenPositiveShiftSum M alpha ^ 2 := by
  convert sum_shifted_positiveFifthPowerRepresentationCount_eq_unitIntegral
    P N M (-tau⁻¹) hMN using 1
  ring_nf

/-- The double sum of shifted singular integrals is one whole-line weighted kernel integral. -/
theorem sum_shifted_chenTenSingularIntegral_eq_wholeLineIntegral
    (P N M : Nat) (hMN : 2 * M ≤ N) :
    (∑ j : Fin M, ∑ k : Fin M,
      chenTenSingularIntegral P (N - j.val.succ - k.val.succ)) =
      ∫ z : Real,
        chenTenSingularIntegralKernel P N z *
          chenTenPositiveShiftSum M z ^ 2 := by
  have hphase (z : Real) (j k : Fin M) :
      chenTenTargetPhase (N - j.val.succ - k.val.succ) z =
        chenTenTargetPhase N z *
          Complex.exp
            (2 * Real.pi * Complex.I *
              (z * ((j.val.succ + k.val.succ : Nat) : Real))) := by
    rw [Nat.sub_sub]
    exact chenTenTargetPhase_nat_sub_shift N
      (j.val.succ + k.val.succ)
      (fin_succ_add_succ_le_of_two_mul_le hMN j k) z
  have hkernel (z : Real) (j k : Fin M) :
      chenTenSingularIntegralKernel P
          (N - j.val.succ - k.val.succ) z =
        chenTenSingularIntegralKernel P N z *
          Complex.exp
            (2 * Real.pi * Complex.I *
              (z * ((j.val.succ + k.val.succ : Nat) : Real))) := by
    unfold chenTenSingularIntegralKernel
    rw [hphase]
    ring
  have hintegrand (z : Real) :
      chenTenSingularIntegralKernel P N z *
          chenTenPositiveShiftSum M z ^ 2 =
        ∑ j : Fin M, ∑ k : Fin M,
          chenTenSingularIntegralKernel P
            (N - j.val.succ - k.val.succ) z := by
    rw [chenTenPositiveShiftSum_sq_eq_pair_sum]
    simp_rw [hkernel]
    simp only [Finset.mul_sum, mul_assoc]
  unfold chenTenSingularIntegral
  calc
    (∑ j : Fin M, ∑ k : Fin M,
        ∫ z : Real,
          chenTenSingularIntegralKernel P
            (N - j.val.succ - k.val.succ) z) =
        ∫ z : Real, ∑ j : Fin M, ∑ k : Fin M,
          chenTenSingularIntegralKernel P
            (N - j.val.succ - k.val.succ) z := by
      symm
      rw [integral_finsetSum (s := (Finset.univ : Finset (Fin M)))
        (f := fun j => fun z : Real => ∑ k : Fin M,
          chenTenSingularIntegralKernel P
            (N - j.val.succ - k.val.succ) z) (μ := volume) (by
        intro j _
        have hsum := integrable_finsetSum'
          (μ := volume) (Finset.univ : Finset (Fin M)) (f := fun k =>
            fun z : Real =>
              chenTenSingularIntegralKernel P
                (N - j.val.succ - k.val.succ) z) (by
          intro k _
          exact integrable_chenTenSingularIntegralKernel P
            (N - j.val.succ - k.val.succ))
        have hfun :
            (fun z : Real => ∑ k : Fin M,
              chenTenSingularIntegralKernel P
                (N - j.val.succ - k.val.succ) z) =
              (∑ k : Fin M, fun z : Real =>
                chenTenSingularIntegralKernel P
                  (N - j.val.succ - k.val.succ) z) := by
          funext z
          simp
        rw [hfun]
        exact hsum)]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum (s := (Finset.univ : Finset (Fin M)))
        (f := fun k => fun z : Real =>
          chenTenSingularIntegralKernel P
            (N - j.val.succ - k.val.succ) z) (μ := volume) (by
        intro k _
        exact integrable_chenTenSingularIntegralKernel P
          (N - j.val.succ - k.val.succ))]
    _ = ∫ z : Real,
        chenTenSingularIntegralKernel P N z *
          chenTenPositiveShiftSum M z ^ 2 := by
      apply integral_congr_ae
      filter_upwards with z
      exact (hintegrand z).symm

/-- On a centered interval, the shifted kernel sum equals the kernel weighted by
the shift square. -/
theorem sum_shifted_chenTenKernel_eq_centeredIntervalIntegral
    (P N M : Nat) (hMN : 2 * M ≤ N) (r : Real) :
    (∑ j : Fin M, ∑ k : Fin M,
      (∫ z in -r..r,
        chenTenSingularIntegralKernel P
          (N - j.val.succ - k.val.succ) z)) =
      ∫ z in -r..r,
        chenTenSingularIntegralKernel P N z *
          chenTenPositiveShiftSum M z ^ 2 := by
  have hphase (z : Real) (j k : Fin M) :
      chenTenTargetPhase (N - j.val.succ - k.val.succ) z =
        chenTenTargetPhase N z *
          Complex.exp
            (2 * Real.pi * Complex.I *
              (z * ((j.val.succ + k.val.succ : Nat) : Real))) := by
    rw [Nat.sub_sub]
    exact chenTenTargetPhase_nat_sub_shift N
      (j.val.succ + k.val.succ)
      (fin_succ_add_succ_le_of_two_mul_le hMN j k) z
  have hkernel (z : Real) (j k : Fin M) :
      chenTenSingularIntegralKernel P
          (N - j.val.succ - k.val.succ) z =
        chenTenSingularIntegralKernel P N z *
          Complex.exp
            (2 * Real.pi * Complex.I *
              (z * ((j.val.succ + k.val.succ : Nat) : Real))) := by
    unfold chenTenSingularIntegralKernel
    rw [hphase]
    ring
  have hintegrand (z : Real) :
      chenTenSingularIntegralKernel P N z *
          chenTenPositiveShiftSum M z ^ 2 =
        ∑ j : Fin M, ∑ k : Fin M,
          chenTenSingularIntegralKernel P
            (N - j.val.succ - k.val.succ) z := by
    rw [chenTenPositiveShiftSum_sq_eq_pair_sum]
    simp_rw [hkernel]
    simp only [Finset.mul_sum, mul_assoc]
  have hinner (j : Fin M) :
      ∀ k ∈ (Finset.univ : Finset (Fin M)),
        IntervalIntegrable
          (fun z : Real =>
            chenTenSingularIntegralKernel P
              (N - j.val.succ - k.val.succ) z)
          volume (-r) r := by
    intro k _
    exact Continuous.intervalIntegrable
      (μ := volume) (a := -r) (b := r)
      (continuous_chenTenSingularIntegralKernel P
        (N - j.val.succ - k.val.succ))
  have houter :
      ∀ j ∈ (Finset.univ : Finset (Fin M)),
        IntervalIntegrable
          (fun z : Real => ∑ k : Fin M,
            chenTenSingularIntegralKernel P
              (N - j.val.succ - k.val.succ) z)
          volume (-r) r := by
    intro j _
    have hsum : IntervalIntegrable
        (∑ k : Fin M, fun z : Real =>
          chenTenSingularIntegralKernel P
            (N - j.val.succ - k.val.succ) z)
        volume (-r) r := by
      apply IntervalIntegrable.sum (μ := volume) (a := -r) (b := r)
        Finset.univ
      exact hinner j
    have hfun :
        (fun z : Real => ∑ k : Fin M,
          chenTenSingularIntegralKernel P
            (N - j.val.succ - k.val.succ) z) =
          (∑ k : Fin M, fun z : Real =>
            chenTenSingularIntegralKernel P
              (N - j.val.succ - k.val.succ) z) := by
      funext z
      simp
    rw [hfun]
    exact hsum
  calc
    (∑ j : Fin M, ∑ k : Fin M,
        (∫ z in -r..r,
          chenTenSingularIntegralKernel P
            (N - j.val.succ - k.val.succ) z)) =
        ∫ z in -r..r, ∑ j : Fin M, ∑ k : Fin M,
          chenTenSingularIntegralKernel P
            (N - j.val.succ - k.val.succ) z := by
      symm
      rw [intervalIntegral.integral_finsetSum (h := houter)]
      apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_finsetSum (h := hinner j)]
    _ = ∫ z in -r..r,
        chenTenSingularIntegralKernel P N z *
          chenTenPositiveShiftSum M z ^ 2 := by
      apply intervalIntegral.integral_congr
      intro z hz
      exact (hintegrand z).symm

/-- Truncating the averaged singular integrals to a centered interval is
controlled by the tail bound. -/
theorem norm_sum_shifted_chenTenSingularIntegral_sub_centeredIntegral_le
    (P N M : Nat) (hMN : 2 * M ≤ N) {r : Real} (hr : 0 < r) :
    ‖(∑ j : Fin M, ∑ k : Fin M,
        chenTenSingularIntegral P (N - j.val.succ - k.val.succ)) -
      (∫ z in -r..r,
        chenTenSingularIntegralKernel P N z *
          chenTenPositiveShiftSum M z ^ 2)‖ ≤
      (M : Real) ^ 2 * ((2 : Real) ^ 15 * r ^ (-2 : Real)) := by
  rw [← sum_shifted_chenTenKernel_eq_centeredIntervalIntegral
    P N M hMN r]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ j : Fin M, ∑ k : Fin M,
        (chenTenSingularIntegral P (N - j.val.succ - k.val.succ) -
          ∫ z in -r..r,
            chenTenSingularIntegralKernel P
              (N - j.val.succ - k.val.succ) z)‖ ≤
        ∑ j : Fin M, ‖∑ k : Fin M,
          (chenTenSingularIntegral P (N - j.val.succ - k.val.succ) -
            ∫ z in -r..r,
              chenTenSingularIntegralKernel P
                (N - j.val.succ - k.val.succ) z)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin M, ∑ k : Fin M,
        ‖chenTenSingularIntegral P (N - j.val.succ - k.val.succ) -
          ∫ z in -r..r,
            chenTenSingularIntegralKernel P
              (N - j.val.succ - k.val.succ) z‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact norm_sum_le _ _
    _ ≤ ∑ _j : Fin M, ∑ _k : Fin M,
        (2 : Real) ^ 15 * r ^ (-2 : Real) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact norm_chenTenSingularIntegral_sub_intervalIntegral_le
        P (N - j.val.succ - k.val.succ) hr
    _ = (M : Real) ^ 2 * ((2 : Real) ^ 15 * r ^ (-2 : Real)) := by
      simp
      ring

end

end Waring.Analytic
