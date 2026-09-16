import Waring.Analytic.PhasePerturbation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The representation integral in Chen's Lemma 10

This file proves the exact finite Fourier identity at the start of Chen's
circle-method argument [CHEN1964-EN, pp. 1560-1561, equations (25)-(26);
CHEN1964-ZH, p. 727].
-/

namespace Waring.Analytic

open MeasureTheory
open scoped BigOperators Interval

/-- The sum of the fifth powers of a bounded positive tuple. An entry of
`Fin P` represents its positive successor in `1, ..., P`. -/
def positiveFifthPowerTupleSum {s P : Nat} (x : Fin s -> Fin P) : Nat :=
  ∑ i, (x i).val.succ ^ 5

/-- The number of representations of `N` by `s` positive fifth powers,
each at most `P`. -/
def positiveFifthPowerRepresentationCount (s P N : Nat) : Nat :=
  ((Finset.univ : Finset (Fin s -> Fin P)).filter fun x =>
    positiveFifthPowerTupleSum x = N).card

/-- The bounded positive representation count is nonzero exactly when a
representing tuple exists. -/
theorem positiveFifthPowerRepresentationCount_pos_iff
    (s P N : Nat) :
    0 < positiveFifthPowerRepresentationCount s P N ↔
      ∃ x : Fin s -> Fin P, positiveFifthPowerTupleSum x = N := by
  unfold positiveFifthPowerRepresentationCount
  rw [Finset.card_pos]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (Finset.mem_filter.mp hx).2⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩

/-- Chen's finite fifth-power exponential sum on the positive interval
`1, ..., P`. -/
noncomputable def fifthPowerExponentialSum (P : Nat) (alpha : Real) : Complex :=
  ∑ x : Fin P, realFifthPowerExponential alpha x

/-- Orthogonality of an integral-frequency exponential on an arbitrary
interval of length one. -/
theorem intervalIntegral_exp_int_frequency (c : Real) (m : Int) :
    (∫ alpha in c..c + 1,
        Complex.exp
          (2 * Real.pi * Complex.I * (((m : Int) : Real) * alpha))) =
      if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    simp
  rw [if_neg hm]
  let z : Complex := (m : Complex) * (2 * Real.pi * Complex.I)
  have hz : z ≠ 0 := by
    dsimp [z]
    have hpi : (Real.pi : Complex) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (Int.cast_ne_zero.mpr hm)
      (mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero)
  have hintegrand :
      (fun alpha : Real =>
        Complex.exp
          (2 * Real.pi * Complex.I * (((m : Int) : Real) * alpha))) =
        fun alpha : Real => Complex.exp (z * alpha) := by
    funext alpha
    congr 1
    dsimp [z]
    ring
  rw [hintegrand, integral_exp_mul_complex hz]
  have hperiod : Complex.exp z = 1 := by
    dsimp [z]
    simpa only [mul_assoc] using Complex.exp_int_mul_two_pi_mul_I m
  push_cast
  rw [show z * ((c : Complex) + 1) = z * c + z by ring,
    Complex.exp_add, hperiod]
  simp

/-- Expanding a power of the finite fifth-power sum gives one phase for each
bounded positive tuple. -/
theorem fifthPowerExponentialSum_pow
    (s P : Nat) (alpha : Real) :
    fifthPowerExponentialSum P alpha ^ s =
      ∑ x : Fin s -> Fin P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (alpha * (positiveFifthPowerTupleSum x : Real))) := by
  rw [fifthPowerExponentialSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [realFifthPowerExponential]
  rw [← Complex.exp_sum Finset.univ]
  congr 1
  unfold positiveFifthPowerTupleSum
  simp_rw [realFifthPowerPhase]
  push_cast
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A tuple phase times the target phase is the integral-frequency character
of the difference between its fifth-power sum and `N`. -/
theorem fifthPowerTuple_phase_mul_target
    {s P : Nat} (x : Fin s -> Fin P) (N : Nat) (alpha : Real) :
    Complex.exp
          (2 * Real.pi * Complex.I *
            (alpha * (positiveFifthPowerTupleSum x : Real))) *
        Complex.exp
          (-2 * Real.pi * Complex.I * (alpha * (N : Real))) =
      Complex.exp
        (2 * Real.pi * Complex.I *
          ((((positiveFifthPowerTupleSum x : Int) - N : Int) : Real) *
            alpha)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The unit-interval integral of Chen's generating function is exactly the
bounded positive representation count. -/
theorem integral_fifthPowerExponentialSum_pow_eq_count
    (s P N : Nat) (c : Real) :
    (∫ alpha in c..c + 1,
        fifthPowerExponentialSum P alpha ^ s *
          Complex.exp
            (-2 * Real.pi * Complex.I * (alpha * (N : Real)))) =
      (positiveFifthPowerRepresentationCount s P N : Complex) := by
  simp_rw [fifthPowerExponentialSum_pow]
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [fifthPowerTuple_phase_mul_target]
    simp_rw [intervalIntegral_exp_int_frequency]
    simp [positiveFifthPowerRepresentationCount, sub_eq_zero]
  · intro x _
    apply Continuous.intervalIntegrable
    fun_prop

/-- Chen's 15-variable representation identity, on the translated unit
interval used in equation (26). -/
theorem integral_fifthPowerExponentialSum_pow_fifteen_eq_count
    (P N : Nat) (tau : Real) :
    (∫ alpha in -tau⁻¹..1 - tau⁻¹,
        fifthPowerExponentialSum P alpha ^ 15 *
          Complex.exp
            (-2 * Real.pi * Complex.I * (alpha * (N : Real)))) =
      (positiveFifthPowerRepresentationCount 15 P N : Complex) := by
  convert integral_fifthPowerExponentialSum_pow_eq_count
    15 P N (-tau⁻¹) using 1
  ring_nf

end Waring.Analytic
