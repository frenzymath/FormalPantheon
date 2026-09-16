import Waring.Analytic.ChenSevenResidueIndex
import Waring.Analytic.ChenSevenResiduePhase
import Waring.Analytic.ChenSevenResidueTrivial

/-!
# The residue-class approximation in Chen's Lemma 7

This file specializes the monotone right-endpoint quadrature estimate to the
fifth-power phase on each residue class and proves the uniform error `6`.
-/

namespace Waring.Analytic

open MeasureTheory Set
open scoped BigOperators ComplexConjugate Interval

/-- In the branch `q ≤ P`, a nonnegative perturbation parameter gives the
one-class error at most six. -/
theorem norm_residueFifthPerturbationSum_sub_mainTerm_le_six_of_nonneg
    (q : Nat) [NeZero q] (z : Real) (P : Nat) (y : ZMod q)
    (hP : 0 < P) (hqP : q ≤ P) (hz0 : 0 ≤ z)
    (hz : z ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    ‖residueFifthPerturbationSum q z P y -
        (q : Complex)⁻¹ * fifthPerturbationIntegral z P‖ ≤ 6 := by
  let r := positiveResidueRepresentative q y
  let n := (P - r) / q
  let theta : Real → Real := residueAffinePhase q z r
  let f : Real → Complex := fun x =>
    Complex.exp (Complex.I * (theta x : Complex))
  let rightSamples : Complex :=
    ∑ i ∈ Finset.range n,
      Complex.exp (Complex.I * (theta (i + 1) : Complex))
  let initialSample : Complex :=
    Complex.exp (Complex.I * (theta 0 : Complex))
  let A : Real := -((r : Real) / q)
  let B : Real := ((P : Real) - r) / q
  have hrPos : 0 < r := positiveResidueRepresentative_pos q y
  have hrq : r ≤ q := positiveResidueRepresentative_le q y
  have hrP : r ≤ P := hrq.trans hqP
  have hqNat : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq : (0 : Real) < q := by exact_mod_cast hqNat
  have hsum :
      residueFifthPerturbationSum q z P y =
        rightSamples + initialSample := by
    change residueFifthPerturbationSum q z P y =
      (∑ i ∈ Finset.range n,
        Complex.exp (Complex.I *
          (residueAffinePhase q z r (i + 1) : Complex))) +
        Complex.exp
          (Complex.I * (residueAffinePhase q z r 0 : Complex))
    rw [residueFifthPerturbationSum_eq_sum_range q z P y hrP]
    change (∑ k ∈ Finset.range (n + 1),
        Complex.exp
          (Complex.I * fifthPerturbationPhase z (r + q * k) 0)) = _
    rw [Finset.sum_range_succ']
    simp_rw [fifthPerturbationPhase_progression]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
  have hnPhysicalNat : r + q * n ≤ P := by
    apply (mem_residueIndexRange_iff_add_mul_le q P n y hrP).mp
    change n < n + 1
    omega
  have hnPhysical : (q : Real) * n + r ≤ P := by
    have hphysical : q * n + r ≤ P := by omega
    exact_mod_cast hphysical
  have hqMulN : q * n ≤ P - r := by
    exact Nat.mul_div_le (P - r) q
  have hqMulSucc : P - r < q * (n + 1) := by
    exact Nat.lt_mul_div_succ (P - r) hqNat
  have hnB : (n : Real) ≤ B := by
    dsimp [B]
    apply (le_div_iff₀ hq).2
    rw [← Nat.cast_sub hrP]
    exact_mod_cast (by simpa [Nat.mul_comm] using hqMulN)
  have hBsucc : B ≤ (n : Real) + 1 := by
    apply (div_le_iff₀ hq).2
    have hcast :
        ((P - r : Nat) : Real) ≤ ((q * (n + 1) : Nat) : Real) := by
      exact_mod_cast hqMulSucc.le
    rw [← Nat.cast_sub hrP]
    push_cast at hcast
    nlinarith
  have hquad :
      ‖rightSamples - ∫ x in (0 : Real)..n, f x‖ ≤ 4 := by
    by_cases hzEq : z = 0
    · subst z
      simp [rightSamples, f, theta, residueAffinePhase]
    · have hzPos : 0 < z := lt_of_le_of_ne hz0 (Ne.symm hzEq)
      apply norm_sum_range_exp_right_sub_integral_le_four_of_deriv
        (theta := theta) (contDiff_residueAffinePhase q z r) n
      · apply (monotoneOn_deriv_residueAffinePhase q z r hz0).mono
        intro x hx
        exact hx.1
      · intro x hx
        exact deriv_residueAffinePhase_pos q z r hzPos hrPos x hx.1
      · exact deriv_residueAffinePhase_le_pi q z P r n hz0 hP
          (Nat.cast_nonneg n) hnPhysical hz
  have hinitial :
      ‖initialSample - ∫ x in A..0, f x‖ ≤ 1 := by
    simpa [initialSample, A, f, theta] using
      norm_exp_residueAffinePhase_zero_sub_initialIntegral_le_one
        q z P r hz0 hP hrq hrP hz
  have htail : ‖∫ x in (n : Real)..B, f x‖ ≤ 1 := by
    calc
      ‖∫ x in (n : Real)..B, f x‖ ≤ |B - n| := by
        simpa [f, theta] using
          norm_integral_exp_residueAffinePhase_le q z r (n : Real) B
      _ = B - n := abs_of_nonneg (sub_nonneg.mpr hnB)
      _ ≤ 1 := by linarith
  have hfCont : Continuous f := by
    dsimp [f, theta, residueAffinePhase]
    fun_prop
  have hsplit :
      (∫ x in A..B, f x) =
        (∫ x in A..0, f x) +
          (∫ x in (0 : Real)..n, f x) +
            (∫ x in (n : Real)..B, f x) := by
    have hA0 : IntervalIntegrable f volume A 0 :=
      hfCont.intervalIntegrable A 0
    have h0n : IntervalIntegrable f volume 0 (n : Real) :=
      hfCont.intervalIntegrable 0 (n : Real)
    have hnBInt : IntervalIntegrable f volume (n : Real) B :=
      hfCont.intervalIntegrable (n : Real) B
    rw [intervalIntegral.integral_add_adjacent_intervals hA0 h0n,
      intervalIntegral.integral_add_adjacent_intervals
        (hfCont.intervalIntegrable A (n : Real)) hnBInt]
  rw [hsum,
    inv_mul_fifthPerturbationIntegral_eq_residueAffineIntegral q z P r,
    show (∫ x in A..B, f x) =
        (∫ x in -((r : Real) / q)..(((P : Real) - r) / q),
          Complex.exp
            (Complex.I * (residueAffinePhase q z r x : Complex))) by rfl,
    hsplit]
  rw [show rightSamples + initialSample -
      ((∫ x in A..0, f x) + (∫ x in (0 : Real)..n, f x) +
        ∫ x in (n : Real)..B, f x) =
      (rightSamples - ∫ x in (0 : Real)..n, f x) +
        (initialSample - ∫ x in A..0, f x) -
          ∫ x in (n : Real)..B, f x by ring]
  calc
    _ ≤ ‖rightSamples - ∫ x in (0 : Real)..n, f x‖ +
          ‖initialSample - ∫ x in A..0, f x‖ +
            ‖∫ x in (n : Real)..B, f x‖ := by
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 4 + 1 + 1 := add_le_add (add_le_add hquad hinitial) htail
    _ = 6 := by norm_num

/-- The one-class sum-to-integral estimate required in Chen's small range. -/
theorem chenSeven_residueApproximation : ChenSevenResidueApproximation := by
  intro q _ z P hP hz y
  by_cases hPq : P < q
  · exact (norm_residueFifthPerturbationSum_sub_mainTerm_le_two_of_lt
      q z P y hPq).trans (by norm_num)
  have hqP : q ≤ P := Nat.le_of_not_gt hPq
  by_cases hz0 : 0 ≤ z
  · apply norm_residueFifthPerturbationSum_sub_mainTerm_le_six_of_nonneg
      q z P y hP hqP hz0
    simpa [abs_of_nonneg hz0] using hz
  · have hzNeg : z < 0 := lt_of_not_ge hz0
    have hnegNonneg : 0 ≤ -z := neg_nonneg.mpr hzNeg.le
    have hnegBound :
        -z ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4) := by
      simpa [abs_of_neg hzNeg] using hz
    have hneg :=
      norm_residueFifthPerturbationSum_sub_mainTerm_le_six_of_nonneg
        q (-z) P y hP hqP hnegNonneg hnegBound
    have hconj :
        conj (residueFifthPerturbationSum q (-z) P y -
          (q : Complex)⁻¹ * fifthPerturbationIntegral (-z) P) =
        residueFifthPerturbationSum q z P y -
          (q : Complex)⁻¹ * fifthPerturbationIntegral z P := by
      simp [conj_residueFifthPerturbationSum,
        conj_fifthPerturbationIntegral]
    rw [← hconj, Complex.norm_conj]
    exact hneg

/-- Chen's unconditional small-denominator conclusion. -/
theorem chenSeven_smallDenominator_bound
    (q : Nat) [NeZero q] (a : Nat) (z : Real) (P : Nat)
    (hPThreshold : (10 : Real) ^ 150 <= P)
    (hqLower : (P : Real) ^ (1 / 2 : Real) <= q)
    (hqUpper : (q : Real) <= (P : Real) ^ (19 / 20 : Real))
    (ha : IsUnit (a : ZMod q))
    (hz : |z| <= 1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    ‖∑ i ∈ Finset.range P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))‖ <=
      (P : Real) ^ (24 / 25 : Real) :=
  chenSeven_smallDenominator_bound_of_residueApproximation
    chenSeven_residueApproximation q a z P hPThreshold hqLower hqUpper ha hz

end Waring.Analytic
