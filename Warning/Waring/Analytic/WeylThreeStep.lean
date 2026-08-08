import Waring.Analytic.WeylDifferenceInequality
import Waring.Analytic.WeylTriangularCauchy

/-!
# Generic three-step positive-shift Weyl differencing

This file packages three finite Weyl-differencing steps for an arbitrary
unit-circle sequence.  Stored shifts are zero-based, so `h + 1` is the actual
positive shift.  The factor two in the third displayed inequality is the
corrected triangular Cauchy factor discussed in [CHEN1964-EN, p. 1555].
-/

namespace Waring.Analytic

open scoped BigOperators ComplexConjugate

/-- Correlate a sequence with its translate by the positive shift `h + 1`. -/
def positiveShiftCorrelation (z : Nat → Complex) (h x : Nat) : Complex :=
  z (x + h + 1) * conj (z x)

/-- The first shifted correlation on its exact remaining interval. -/
def firstPositiveShiftSum (z : Nat → Complex) (P h₁ : Nat) : Complex :=
  ∑ x ∈ Finset.range (P - h₁ - 1), positiveShiftCorrelation z h₁ x

/-- The twice-shifted correlation on its exact remaining interval. -/
def secondPositiveShiftSum
    (z : Nat → Complex) (P h₁ h₂ : Nat) : Complex :=
  ∑ x ∈ Finset.range (P - h₁ - 1 - h₂ - 1),
    positiveShiftCorrelation (positiveShiftCorrelation z h₁) h₂ x

/-- The three-times-shifted correlation on its exact remaining interval. -/
def thirdPositiveShiftSum
    (z : Nat → Complex) (P h₁ h₂ h₃ : Nat) : Complex :=
  ∑ x ∈ Finset.range (P - h₁ - 1 - h₂ - 1 - h₃ - 1),
    positiveShiftCorrelation
      (positiveShiftCorrelation (positiveShiftCorrelation z h₁) h₂) h₃ x

/-- The aggregate norm after one positive-shift differencing step. -/
noncomputable def weylDOne (z : Nat → Complex) (P : Nat) : Real :=
  ∑ h₁ ∈ Finset.range P, ‖firstPositiveShiftSum z P h₁‖

/-- The aggregate norm after two positive-shift differencing steps. -/
noncomputable def weylDTwo (z : Nat → Complex) (P : Nat) : Real :=
  ∑ h₁ ∈ Finset.range P, ∑ h₂ ∈ Finset.range (P - h₁ - 1),
    ‖secondPositiveShiftSum z P h₁ h₂‖

/-- The aggregate norm after three positive-shift differencing steps. -/
noncomputable def weylDThree (z : Nat → Complex) (P : Nat) : Real :=
  ∑ h₁ ∈ Finset.range P, ∑ h₂ ∈ Finset.range (P - h₁ - 1),
    ∑ h₃ ∈ Finset.range (P - h₁ - 1 - h₂ - 1),
      ‖thirdPositiveShiftSum z P h₁ h₂ h₃‖

/-- The level-two nested range is exactly `l₁ + l₂ ≤ P` for the actual
positive shifts `lᵢ = hᵢ + 1`. -/
theorem mem_two_positiveShift_range_iff (P h₁ h₂ : Nat) :
    h₁ ∈ Finset.range P ∧ h₂ ∈ Finset.range (P - h₁ - 1) ↔
      (h₁ + 1) + (h₂ + 1) ≤ P := by
  simp only [Finset.mem_range]
  omega

/-- The level-three nested range is exactly `l₁ + l₂ + l₃ ≤ P` for the
actual positive shifts `lᵢ = hᵢ + 1`. -/
theorem mem_three_positiveShift_range_iff (P h₁ h₂ h₃ : Nat) :
    h₁ ∈ Finset.range P ∧ h₂ ∈ Finset.range (P - h₁ - 1) ∧
        h₃ ∈ Finset.range (P - h₁ - 1 - h₂ - 1) ↔
      (h₁ + 1) + (h₂ + 1) + (h₃ + 1) ≤ P := by
  simp only [Finset.mem_range]
  omega

/-- Positive-shift correlation preserves the unit-circle condition. -/
theorem norm_positiveShiftCorrelation_eq_one
    (z : Nat → Complex) (h : Nat) (hz : ∀ x, ‖z x‖ = 1) (x : Nat) :
    ‖positiveShiftCorrelation z h x‖ = 1 := by
  simp [positiveShiftCorrelation, hz]

/-- The initial finite differencing inequality, with no polynomial-phase
assumption. -/
theorem norm_sum_range_sq_le_add_two_weylDOne
    (z : Nat → Complex) (P : Nat) (hz : ∀ x, ‖z x‖ = 1) :
    ‖∑ x ∈ Finset.range P, z x‖ ^ 2 ≤ P + 2 * weylDOne z P := by
  simpa [weylDOne, firstPositiveShiftSum, positiveShiftCorrelation] using
    norm_sum_range_sq_le_sum_shiftCorrelation z P (fun x _ ↦ hz x)

/-- Differencing a first correlation produces the exact level-two range. -/
theorem norm_firstPositiveShiftSum_sq_le
    (z : Nat → Complex) (P h₁ : Nat) (hz : ∀ x, ‖z x‖ = 1) :
    ‖firstPositiveShiftSum z P h₁‖ ^ 2 ≤
      (P - h₁ - 1 : Nat) + 2 *
        ∑ h₂ ∈ Finset.range (P - h₁ - 1),
          ‖secondPositiveShiftSum z P h₁ h₂‖ := by
  have hunit : ∀ x, ‖positiveShiftCorrelation z h₁ x‖ = 1 :=
    fun x ↦ norm_positiveShiftCorrelation_eq_one z h₁ hz x
  simpa [firstPositiveShiftSum, secondPositiveShiftSum,
    positiveShiftCorrelation] using
      norm_sum_range_sq_le_sum_shiftCorrelation
        (positiveShiftCorrelation z h₁) (P - h₁ - 1) (fun x _ ↦ hunit x)

/-- Differencing a second correlation produces the exact level-three range. -/
theorem norm_secondPositiveShiftSum_sq_le
    (z : Nat → Complex) (P h₁ h₂ : Nat) (hz : ∀ x, ‖z x‖ = 1) :
    ‖secondPositiveShiftSum z P h₁ h₂‖ ^ 2 ≤
      (P - h₁ - 1 - h₂ - 1 : Nat) + 2 *
        ∑ h₃ ∈ Finset.range (P - h₁ - 1 - h₂ - 1),
          ‖thirdPositiveShiftSum z P h₁ h₂ h₃‖ := by
  have hunit₁ : ∀ x, ‖positiveShiftCorrelation z h₁ x‖ = 1 :=
    fun x ↦ norm_positiveShiftCorrelation_eq_one z h₁ hz x
  have hunit₂ : ∀ x,
      ‖positiveShiftCorrelation (positiveShiftCorrelation z h₁) h₂ x‖ = 1 :=
    fun x ↦ norm_positiveShiftCorrelation_eq_one
      (positiveShiftCorrelation z h₁) h₂ hunit₁ x
  simpa [secondPositiveShiftSum, thirdPositiveShiftSum,
    positiveShiftCorrelation] using
      norm_sum_range_sq_le_sum_shiftCorrelation
        (positiveShiftCorrelation (positiveShiftCorrelation z h₁) h₂)
        (P - h₁ - 1 - h₂ - 1) (fun x _ ↦ hunit₂ x)

private theorem sum_range_le_card_mul
    (f : Nat → Real) (N : Nat) (C : Real)
    (hf : ∀ i < N, f i ≤ C) :
    (∑ i ∈ Finset.range N, f i) ≤ N * C := by
  calc
    (∑ i ∈ Finset.range N, f i) ≤
        ∑ _i ∈ Finset.range N, C := by
      exact Finset.sum_le_sum fun i hi ↦ hf i (Finset.mem_range.mp hi)
    _ = N * C := by simp

private theorem sum_first_remaining_le_sq (P : Nat) :
    (∑ h₁ ∈ Finset.range P, ((P - h₁ - 1 : Nat) : Real)) ≤
      (P : Real) ^ 2 := by
  calc
    (∑ h₁ ∈ Finset.range P, ((P - h₁ - 1 : Nat) : Real)) ≤
        (P : Real) * P := by
      apply sum_range_le_card_mul
      intro h₁ _
      exact_mod_cast Nat.sub_le (P - h₁) 1 |>.trans (Nat.sub_le P h₁)
    _ = (P : Real) ^ 2 := by ring

private theorem sum_second_remaining_le_cube (P : Nat) :
    (∑ h₁ ∈ Finset.range P,
      ∑ h₂ ∈ Finset.range (P - h₁ - 1),
        ((P - h₁ - 1 - h₂ - 1 : Nat) : Real)) ≤
      (P : Real) ^ 3 := by
  have hinner : ∀ h₁ < P,
      (∑ h₂ ∈ Finset.range (P - h₁ - 1),
        ((P - h₁ - 1 - h₂ - 1 : Nat) : Real)) ≤ (P : Real) ^ 2 := by
    intro h₁ _
    calc
      (∑ h₂ ∈ Finset.range (P - h₁ - 1),
          ((P - h₁ - 1 - h₂ - 1 : Nat) : Real)) ≤
          ((P - h₁ - 1 : Nat) : Real) * P := by
        apply sum_range_le_card_mul
        intro h₂ _
        exact_mod_cast
          (Nat.sub_le (P - h₁ - 1 - h₂) 1).trans
            ((Nat.sub_le (P - h₁ - 1) h₂).trans
              ((Nat.sub_le (P - h₁) 1).trans (Nat.sub_le P h₁)))
      _ ≤ (P : Real) * P := by
        gcongr
        exact_mod_cast (Nat.sub_le (P - h₁) 1).trans (Nat.sub_le P h₁)
      _ = (P : Real) ^ 2 := by ring
  calc
    (∑ h₁ ∈ Finset.range P,
      ∑ h₂ ∈ Finset.range (P - h₁ - 1),
        ((P - h₁ - 1 - h₂ - 1 : Nat) : Real)) ≤
        (P : Real) * (P : Real) ^ 2 := by
      exact sum_range_le_card_mul _ _ _ hinner
    _ = (P : Real) ^ 3 := by ring

/-- Cauchy and one more correlation identity give the first aggregate
inequality `D₁² ≤ P³ + 2 P D₂`. -/
theorem weylDOne_sq_le
    (z : Nat → Complex) (P : Nat) (hz : ∀ x, ‖z x‖ = 1) :
    weylDOne z P ^ 2 ≤
      (P : Real) ^ 3 + 2 * P * weylDTwo z P := by
  have hCauchy := sq_sum_le_card_mul_sum_sq
    (s := Finset.range P) (f := fun h₁ ↦ ‖firstPositiveShiftSum z P h₁‖)
  have hsum :
      (∑ h₁ ∈ Finset.range P, ‖firstPositiveShiftSum z P h₁‖ ^ 2) ≤
        (P : Real) ^ 2 + 2 * weylDTwo z P := by
    calc
      (∑ h₁ ∈ Finset.range P, ‖firstPositiveShiftSum z P h₁‖ ^ 2) ≤
          ∑ h₁ ∈ Finset.range P,
            (((P - h₁ - 1 : Nat) : Real) + 2 *
              ∑ h₂ ∈ Finset.range (P - h₁ - 1),
                ‖secondPositiveShiftSum z P h₁ h₂‖) := by
        exact Finset.sum_le_sum fun h₁ _ ↦
          norm_firstPositiveShiftSum_sq_le z P h₁ hz
      _ = (∑ h₁ ∈ Finset.range P,
            ((P - h₁ - 1 : Nat) : Real)) + 2 * weylDTwo z P := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, weylDTwo]
      _ ≤ (P : Real) ^ 2 + 2 * weylDTwo z P := by
        gcongr
        exact sum_first_remaining_le_sq P
  calc
    weylDOne z P ^ 2 ≤
        (P : Real) *
          ∑ h₁ ∈ Finset.range P, ‖firstPositiveShiftSum z P h₁‖ ^ 2 := by
      simpa [weylDOne] using hCauchy
    _ ≤ (P : Real) * ((P : Real) ^ 2 + 2 * weylDTwo z P) := by
      gcongr
    _ = (P : Real) ^ 3 + 2 * P * weylDTwo z P := by ring

/-- The corrected triangular Cauchy step and a third correlation identity
give `2 D₂² ≤ P⁵ + 2 P² D₃`. -/
theorem two_mul_weylDTwo_sq_le
    (z : Nat → Complex) (P : Nat) (hz : ∀ x, ‖z x‖ = 1) :
    2 * weylDTwo z P ^ 2 ≤
      (P : Real) ^ 5 + 2 * (P : Real) ^ 2 * weylDThree z P := by
  let Q : Real := ∑ h₁ ∈ Finset.range P,
    ∑ h₂ ∈ Finset.range (P - h₁ - 1),
      ‖secondPositiveShiftSum z P h₁ h₂‖ ^ 2
  have hCauchy := sq_sum_positiveShift_le_card_mul_sum_sq
    (fun h₁ h₂ ↦ ‖secondPositiveShiftSum z P h₁ h₂‖) P
  have hQnonneg : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hcardNat : 2 * (P * (P - 1) / 2) ≤ P * P := by
    calc
      2 * (P * (P - 1) / 2) = (P * (P - 1) / 2) * 2 := by omega
      _ ≤ P * (P - 1) := Nat.div_mul_le_self _ _
      _ ≤ P * P := Nat.mul_le_mul_left P (Nat.sub_le P 1)
  have hcard :
      2 * (((P * (P - 1) / 2 : Nat) : Real)) ≤ (P : Real) ^ 2 := by
    have hcast :
        2 * (((P * (P - 1) / 2 : Nat) : Real)) ≤ (P : Real) * P := by
      exact_mod_cast hcardNat
    simpa [pow_two] using hcast
  have htriangle : 2 * weylDTwo z P ^ 2 ≤ (P : Real) ^ 2 * Q := by
    calc
      2 * weylDTwo z P ^ 2 ≤
          2 * (((P * (P - 1) / 2 : Nat) : Real) * Q) := by
        gcongr
        simpa [weylDTwo, Q] using hCauchy
      _ = (2 * (((P * (P - 1) / 2 : Nat) : Real)) * Q) := by ring
      _ ≤ (P : Real) ^ 2 * Q := by
        exact mul_le_mul_of_nonneg_right hcard hQnonneg
  have hQ : Q ≤ (P : Real) ^ 3 + 2 * weylDThree z P := by
    calc
      Q ≤ ∑ h₁ ∈ Finset.range P,
          ∑ h₂ ∈ Finset.range (P - h₁ - 1),
            (((P - h₁ - 1 - h₂ - 1 : Nat) : Real) + 2 *
              ∑ h₃ ∈ Finset.range (P - h₁ - 1 - h₂ - 1),
                ‖thirdPositiveShiftSum z P h₁ h₂ h₃‖) := by
        dsimp [Q]
        apply Finset.sum_le_sum
        intro h₁ _
        exact Finset.sum_le_sum fun h₂ _ ↦
          norm_secondPositiveShiftSum_sq_le z P h₁ h₂ hz
      _ = (∑ h₁ ∈ Finset.range P,
            ∑ h₂ ∈ Finset.range (P - h₁ - 1),
              ((P - h₁ - 1 - h₂ - 1 : Nat) : Real)) +
            2 * weylDThree z P := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, weylDThree]
      _ ≤ (P : Real) ^ 3 + 2 * weylDThree z P := by
        gcongr
        exact sum_second_remaining_le_cube P
  calc
    2 * weylDTwo z P ^ 2 ≤ (P : Real) ^ 2 * Q := htriangle
    _ ≤ (P : Real) ^ 2 * ((P : Real) ^ 3 + 2 * weylDThree z P) := by
      gcongr
    _ = (P : Real) ^ 5 + 2 * (P : Real) ^ 2 * weylDThree z P := by ring

private theorem norm_sum_range_le_card_of_norm_one
    (w : Nat → Complex) (N : Nat) (hw : ∀ x, ‖w x‖ = 1) :
    ‖∑ x ∈ Finset.range N, w x‖ ≤ N := by
  calc
    ‖∑ x ∈ Finset.range N, w x‖ ≤
        ∑ x ∈ Finset.range N, ‖w x‖ := norm_sum_le _ _
    _ = N := by simp [hw]

/-- The first aggregate norm sum is nonnegative. -/
theorem weylDOne_nonneg (z : Nat → Complex) (P : Nat) : 0 ≤ weylDOne z P := by
  rw [weylDOne]
  positivity

/-- Trivial unit-circle bound after one differencing step. -/
theorem weylDOne_le_sq
    (z : Nat → Complex) (P : Nat) (hz : ∀ x, ‖z x‖ = 1) :
    weylDOne z P ≤ (P : Real) ^ 2 := by
  calc
    weylDOne z P ≤ ∑ _h₁ ∈ Finset.range P, (P : Real) := by
      apply Finset.sum_le_sum
      intro h₁ _
      calc
        ‖firstPositiveShiftSum z P h₁‖ ≤ (P - h₁ - 1 : Nat) := by
          apply norm_sum_range_le_card_of_norm_one
          exact fun x ↦ norm_positiveShiftCorrelation_eq_one z h₁ hz x
        _ ≤ P := by exact_mod_cast (Nat.sub_le (P - h₁) 1).trans (Nat.sub_le P h₁)
    _ = (P : Real) ^ 2 := by simp; ring

/-- The second aggregate norm sum is nonnegative. -/
theorem weylDTwo_nonneg (z : Nat → Complex) (P : Nat) : 0 ≤ weylDTwo z P := by
  rw [weylDTwo]
  positivity

/-- Trivial unit-circle bound after two differencing steps. -/
theorem weylDTwo_le_cube
    (z : Nat → Complex) (P : Nat) (hz : ∀ x, ‖z x‖ = 1) :
    weylDTwo z P ≤ (P : Real) ^ 3 := by
  have hterm : ∀ h₁ h₂,
      ‖secondPositiveShiftSum z P h₁ h₂‖ ≤ (P : Real) := by
    intro h₁ h₂
    have hunit₁ : ∀ x, ‖positiveShiftCorrelation z h₁ x‖ = 1 :=
      fun x ↦ norm_positiveShiftCorrelation_eq_one z h₁ hz x
    calc
      ‖secondPositiveShiftSum z P h₁ h₂‖ ≤
          (P - h₁ - 1 - h₂ - 1 : Nat) := by
        apply norm_sum_range_le_card_of_norm_one
        exact fun x ↦ norm_positiveShiftCorrelation_eq_one
          (positiveShiftCorrelation z h₁) h₂ hunit₁ x
      _ ≤ P := by
        exact_mod_cast
          (Nat.sub_le (P - h₁ - 1 - h₂) 1).trans
            ((Nat.sub_le (P - h₁ - 1) h₂).trans
              ((Nat.sub_le (P - h₁) 1).trans (Nat.sub_le P h₁)))
  have hinner : ∀ h₁ < P,
      (∑ h₂ ∈ Finset.range (P - h₁ - 1),
        ‖secondPositiveShiftSum z P h₁ h₂‖) ≤ (P : Real) ^ 2 := by
    intro h₁ _
    calc
      (∑ h₂ ∈ Finset.range (P - h₁ - 1),
          ‖secondPositiveShiftSum z P h₁ h₂‖) ≤
          ((P - h₁ - 1 : Nat) : Real) * P := by
        exact sum_range_le_card_mul _ _ _ fun h₂ _ ↦ hterm h₁ h₂
      _ ≤ (P : Real) * P := by
        gcongr
        exact_mod_cast (Nat.sub_le (P - h₁) 1).trans (Nat.sub_le P h₁)
      _ = (P : Real) ^ 2 := by ring
  calc
    weylDTwo z P ≤ (P : Real) * (P : Real) ^ 2 := by
      exact sum_range_le_card_mul _ _ _ hinner
    _ = (P : Real) ^ 3 := by ring

/-- The third aggregate norm sum is nonnegative. -/
theorem weylDThree_nonneg (z : Nat → Complex) (P : Nat) :
    0 ≤ weylDThree z P := by
  rw [weylDThree]
  positivity

/-- Trivial unit-circle bound after three differencing steps. -/
theorem weylDThree_le_fourth
    (z : Nat → Complex) (P : Nat) (hz : ∀ x, ‖z x‖ = 1) :
    weylDThree z P ≤ (P : Real) ^ 4 := by
  have hterm : ∀ h₁ h₂ h₃,
      ‖thirdPositiveShiftSum z P h₁ h₂ h₃‖ ≤ (P : Real) := by
    intro h₁ h₂ h₃
    have hunit₁ : ∀ x, ‖positiveShiftCorrelation z h₁ x‖ = 1 :=
      fun x ↦ norm_positiveShiftCorrelation_eq_one z h₁ hz x
    have hunit₂ : ∀ x,
        ‖positiveShiftCorrelation (positiveShiftCorrelation z h₁) h₂ x‖ = 1 :=
      fun x ↦ norm_positiveShiftCorrelation_eq_one
        (positiveShiftCorrelation z h₁) h₂ hunit₁ x
    calc
      ‖thirdPositiveShiftSum z P h₁ h₂ h₃‖ ≤
          (P - h₁ - 1 - h₂ - 1 - h₃ - 1 : Nat) := by
        apply norm_sum_range_le_card_of_norm_one
        exact fun x ↦ norm_positiveShiftCorrelation_eq_one
          (positiveShiftCorrelation (positiveShiftCorrelation z h₁) h₂)
            h₃ hunit₂ x
      _ ≤ P := by
        exact_mod_cast
          (Nat.sub_le (P - h₁ - 1 - h₂ - 1 - h₃) 1).trans
            ((Nat.sub_le (P - h₁ - 1 - h₂ - 1) h₃).trans
              ((Nat.sub_le (P - h₁ - 1 - h₂) 1).trans
                ((Nat.sub_le (P - h₁ - 1) h₂).trans
                  ((Nat.sub_le (P - h₁) 1).trans (Nat.sub_le P h₁)))))
  have hinner : ∀ h₁ h₂,
      (∑ h₃ ∈ Finset.range (P - h₁ - 1 - h₂ - 1),
        ‖thirdPositiveShiftSum z P h₁ h₂ h₃‖) ≤ (P : Real) ^ 2 := by
    intro h₁ h₂
    calc
      (∑ h₃ ∈ Finset.range (P - h₁ - 1 - h₂ - 1),
          ‖thirdPositiveShiftSum z P h₁ h₂ h₃‖) ≤
          ((P - h₁ - 1 - h₂ - 1 : Nat) : Real) * P := by
        exact sum_range_le_card_mul _ _ _ fun h₃ _ ↦ hterm h₁ h₂ h₃
      _ ≤ (P : Real) * P := by
        gcongr
        exact_mod_cast
          (Nat.sub_le (P - h₁ - 1 - h₂) 1).trans
            ((Nat.sub_le (P - h₁ - 1) h₂).trans
              ((Nat.sub_le (P - h₁) 1).trans (Nat.sub_le P h₁)))
      _ = (P : Real) ^ 2 := by ring
  have hmiddle : ∀ h₁ < P,
      (∑ h₂ ∈ Finset.range (P - h₁ - 1),
        ∑ h₃ ∈ Finset.range (P - h₁ - 1 - h₂ - 1),
          ‖thirdPositiveShiftSum z P h₁ h₂ h₃‖) ≤ (P : Real) ^ 3 := by
    intro h₁ _
    calc
      (∑ h₂ ∈ Finset.range (P - h₁ - 1),
        ∑ h₃ ∈ Finset.range (P - h₁ - 1 - h₂ - 1),
          ‖thirdPositiveShiftSum z P h₁ h₂ h₃‖) ≤
          ((P - h₁ - 1 : Nat) : Real) * (P : Real) ^ 2 := by
        exact sum_range_le_card_mul _ _ _ fun h₂ _ ↦ hinner h₁ h₂
      _ ≤ (P : Real) * (P : Real) ^ 2 := by
        gcongr
        exact_mod_cast (Nat.sub_le (P - h₁) 1).trans (Nat.sub_le P h₁)
      _ = (P : Real) ^ 3 := by ring
  calc
    weylDThree z P ≤ (P : Real) * (P : Real) ^ 3 := by
      exact sum_range_le_card_mul _ _ _ hmiddle
    _ = (P : Real) ^ 4 := by ring

end Waring.Analytic
