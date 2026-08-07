import BoundedGaps.Maynard.ConcreteYDiagonalS1Limit
import BoundedGaps.Maynard.ConcreteS2

noncomputable section
namespace BoundedGaps.Maynard

open scoped BigOperators
local instance s2KernelDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def engelsmaShiftedPrimeIntervalCount (N : ℕ)
    (h : BoundedGaps.engelsmaTuple) : ℝ :=
  (primeCountTotal (2 * N + h.1 - 1) : ℝ) -
    (primeCountTotal (N + h.1 - 1) : ℝ)

noncomputable def engelsmaMaynardS2ShiftKernel
    (alpha : ℝ) (N : ℕ) (h : BoundedGaps.engelsmaTuple) : ℝ :=
  let D := maynardSupportFamily BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N
  let lambda := maynardCoefficientFamily BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
    engelsmaSmallKCandidate N
  ∑ d : D, ∑ e : D.filter
      (fun e : BoundedGaps.engelsmaTuple → ℕ =>
        IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d.1 e),
    if d.1 h = 1 ∧ e.1 h = 1 then
      (lambda d.1 * lambda e.1) /
        (Nat.totient (divisorPairModulus BoundedGaps.engelsmaTuple
          (engelsmaMaynardModulus N) d.1 e.1) : ℝ)
    else 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem engelsmaMaynardS2Main_eq_shiftKernel_sum
    (alpha : ℝ) (N : ℕ) :
    engelsmaMaynardS2Main alpha N =
      ∑ h ∈ BoundedGaps.engelsmaTuple.attach,
        engelsmaShiftedPrimeIntervalCount N h *
          engelsmaMaynardS2ShiftKernel alpha N h := by
  classical
  let D := maynardSupportFamily BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N
  let lambda := maynardCoefficientFamily BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
    engelsmaSmallKCandidate N
  change
    (∑ d : D, ∑ e : D.filter
        (fun e : BoundedGaps.engelsmaTuple → ℕ =>
          IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d.1 e),
      ∑ h ∈ BoundedGaps.engelsmaTuple.attach,
        if d.1 h = 1 ∧ e.1 h = 1 then
          (engelsmaShiftedPrimeIntervalCount N h /
              (Nat.totient (divisorPairModulus BoundedGaps.engelsmaTuple
                (engelsmaMaynardModulus N) d.1 e.1) : ℝ)) *
            (lambda d.1 * lambda e.1)
        else 0) =
      ∑ h ∈ BoundedGaps.engelsmaTuple.attach,
        engelsmaShiftedPrimeIntervalCount N h *
          ∑ d : D, ∑ e : D.filter
            (fun e : BoundedGaps.engelsmaTuple → ℕ =>
              IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d.1 e),
            if d.1 h = 1 ∧ e.1 h = 1 then
              (lambda d.1 * lambda e.1) /
                (Nat.totient (divisorPairModulus BoundedGaps.engelsmaTuple
                  (engelsmaMaynardModulus N) d.1 e.1) : ℝ)
            else 0
  calc
    _ = ∑ d : D, ∑ h ∈ BoundedGaps.engelsmaTuple.attach,
        ∑ e : D.filter
          (fun e : BoundedGaps.engelsmaTuple → ℕ =>
            IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d.1 e),
          if d.1 h = 1 ∧ e.1 h = 1 then
            (engelsmaShiftedPrimeIntervalCount N h /
                (Nat.totient (divisorPairModulus BoundedGaps.engelsmaTuple
                  (engelsmaMaynardModulus N) d.1 e.1) : ℝ)) *
              (lambda d.1 * lambda e.1)
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_comm
    _ = ∑ h ∈ BoundedGaps.engelsmaTuple.attach,
        ∑ d : D, ∑ e : D.filter
          (fun e : BoundedGaps.engelsmaTuple → ℕ =>
            IsCrossCoordinateCoprime BoundedGaps.engelsmaTuple d.1 e),
          if d.1 h = 1 ∧ e.1 h = 1 then
            (engelsmaShiftedPrimeIntervalCount N h /
                (Nat.totient (divisorPairModulus BoundedGaps.engelsmaTuple
                  (engelsmaMaynardModulus N) d.1 e.1) : ℝ)) *
              (lambda d.1 * lambda e.1)
          else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hde : d.1 h = 1 ∧ e.1 h = 1
      · rw [if_pos hde, if_pos hde]
        ring
      · rw [if_neg hde, if_neg hde, mul_zero]

end BoundedGaps.Maynard
