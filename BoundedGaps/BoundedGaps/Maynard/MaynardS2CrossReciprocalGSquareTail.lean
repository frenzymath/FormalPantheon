import BoundedGaps.Maynard.MaynardS2ReciprocalGSquarefreeFunction
import BoundedGaps.Maynard.MaynardSquarefreeRoughTail

noncomputable section

/-!
# Reciprocal-g square tail for the S2 cross variables

Maynard2013v3, source lines 384--393, bounds the nontrivial starred cross
variables with the squarefree weight `mu(s)^2 / g(s)^2`. This file supplies a
finite explicit rough tail for that weight.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def maynardS2CrossPrimeSquareWeight (p : ℕ) : ℝ :=
  (1 : ℝ) / ((p - 2 : ℕ) : ℝ) ^ 2

theorem maynardS2CrossPrimeSquareWeight_nonneg (p : ℕ) :
    0 ≤ maynardS2CrossPrimeSquareWeight p := by
  unfold maynardS2CrossPrimeSquareWeight
  positivity

theorem maynardS2CrossPrimeSquareWeight_le
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    maynardS2CrossPrimeSquareWeight p ≤
      4 * primeTotientSquareWeight p := by
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hp2 : 2 ≤ p := by omega
  have hpm2 : (0 : ℝ) < p - 2 := by linarith
  have hpm1 : (0 : ℝ) < p - 1 := by linarith
  have hcastTwo : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
    rw [Nat.cast_sub hp2]
    norm_num
  have hcastOne : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_le]
    norm_num
  unfold maynardS2CrossPrimeSquareWeight primeTotientSquareWeight
  rw [Nat.totient_prime hp, hcastTwo, hcastOne]
  rw [show 4 * (1 / ((p : ℝ) - 1) ^ 2) =
      4 / ((p : ℝ) - 1) ^ 2 by ring]
  rw [div_le_div_iff₀ (sq_pos_of_pos hpm2) (sq_pos_of_pos hpm1)]
  have hfactor : 0 ≤ ((p : ℝ) - 3) * (3 * p - 5) :=
    mul_nonneg (sub_nonneg.mpr hp3R) (by linarith)
  nlinarith

def squarefreeRoughReciprocalGSquareTail (D Q : ℕ) : ℝ :=
  ∑ n ∈ squarefreeRoughSupport D Q,
    (1 : ℝ) / (maynardS2G n : ℝ) ^ 2

theorem inv_maynardS2G_sq_eq_primeFactors_product
    {n : ℕ} (hn : Squarefree n) :
    (1 : ℝ) / (maynardS2G n : ℝ) ^ 2 =
      ∏ p ∈ n.primeFactors, maynardS2CrossPrimeSquareWeight p := by
  rw [maynardS2G_apply hn.ne_zero]
  push_cast
  unfold maynardS2CrossPrimeSquareWeight
  rw [← Finset.prod_pow]
  simp only [one_div, Finset.prod_inv_distrib]

theorem squarefreeRoughReciprocalGSquareTail_eq_primeFactorImageSum
    (D Q : ℕ) :
    squarefreeRoughReciprocalGSquareTail D Q =
      ∑ t ∈ (squarefreeRoughSupport D Q).image Nat.primeFactors,
        ∏ p ∈ t, maynardS2CrossPrimeSquareWeight p := by
  classical
  unfold squarefreeRoughReciprocalGSquareTail
  calc
    (∑ n ∈ squarefreeRoughSupport D Q,
        (1 : ℝ) / (maynardS2G n : ℝ) ^ 2) =
        ∑ n ∈ squarefreeRoughSupport D Q,
          ∏ p ∈ n.primeFactors, maynardS2CrossPrimeSquareWeight p := by
      apply Finset.sum_congr rfl
      intro n hn
      exact inv_maynardS2G_sq_eq_primeFactors_product
        (squarefreeRoughSupport_squarefree hn)
    _ = _ := by
      rw [Finset.sum_image]
      intro m hm n hn hmn
      exact primeFactors_injOn_squarefreeRoughSupport D Q hm hn hmn

theorem squarefreeRoughReciprocalGSquareTail_le_nonemptySubsetSum
    (D Q : ℕ) :
    squarefreeRoughReciprocalGSquareTail D Q ≤
      ∑ t ∈ (roughPrimeSupport D Q).powerset.erase ∅,
        ∏ p ∈ t, maynardS2CrossPrimeSquareWeight p := by
  classical
  rw [squarefreeRoughReciprocalGSquareTail_eq_primeFactorImageSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (primeFactorImage_subset_nonemptyPowerset D Q)
  intro t ht htNot
  exact Finset.prod_nonneg fun p hp =>
    maynardS2CrossPrimeSquareWeight_nonneg p

theorem reciprocalGNonemptySubsetSum_eq_eulerProduct_sub_one
    (D Q : ℕ) :
    (∑ t ∈ (roughPrimeSupport D Q).powerset.erase ∅,
        ∏ p ∈ t, maynardS2CrossPrimeSquareWeight p) =
      (∏ p ∈ roughPrimeSupport D Q,
        (1 + maynardS2CrossPrimeSquareWeight p)) - 1 := by
  classical
  have hempty : ∅ ∈ (roughPrimeSupport D Q).powerset := by simp
  have herase := Finset.sum_erase_add
    (s := (roughPrimeSupport D Q).powerset)
    (f := fun t => ∏ p ∈ t, maynardS2CrossPrimeSquareWeight p) hempty
  rw [Finset.prod_one_add]
  simp only [Finset.prod_empty] at herase
  linarith

theorem roughPrimeReciprocalGSquareWeightSum_le
    {D Q : ℕ} (hD : 2 ≤ D) :
    (∑ p ∈ roughPrimeSupport D Q,
      maynardS2CrossPrimeSquareWeight p) ≤ 32 / (D : ℝ) := by
  calc
    (∑ p ∈ roughPrimeSupport D Q,
        maynardS2CrossPrimeSquareWeight p) ≤
        ∑ p ∈ roughPrimeSupport D Q,
          4 * primeTotientSquareWeight p := by
      apply Finset.sum_le_sum
      intro p hpMem
      have hpData := Finset.mem_filter.mp hpMem
      have hpLower := (Finset.mem_Icc.mp hpData.1).1
      exact maynardS2CrossPrimeSquareWeight_le hpData.2 (by omega)
    _ = 4 * ∑ p ∈ roughPrimeSupport D Q,
        primeTotientSquareWeight p := by rw [Finset.mul_sum]
    _ ≤ 4 * (8 / (D : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (roughPrimeWeightSum_le (Q := Q) (by omega)) (by norm_num)
    _ = 32 / (D : ℝ) := by ring

theorem roughPrimeReciprocalGSquareEulerProduct_le_exp_thirtyTwo
    {D Q : ℕ} (hD : 2 ≤ D) :
    (∏ p ∈ roughPrimeSupport D Q,
        (1 + maynardS2CrossPrimeSquareWeight p)) ≤ Real.exp 32 := by
  calc
    (∏ p ∈ roughPrimeSupport D Q,
        (1 + maynardS2CrossPrimeSquareWeight p)) ≤
        Real.exp (∑ p ∈ roughPrimeSupport D Q,
          maynardS2CrossPrimeSquareWeight p) := by
      exact Real.prod_one_add_le_exp_sum _
        maynardS2CrossPrimeSquareWeight_nonneg
    _ ≤ Real.exp 32 := by
      apply Real.exp_le_exp.mpr
      have hsum := roughPrimeReciprocalGSquareWeightSum_le
        (Q := Q) hD
      have hDR : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
      have hDone : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
      calc
        (∑ p ∈ roughPrimeSupport D Q,
            maynardS2CrossPrimeSquareWeight p) ≤ 32 / (D : ℝ) := hsum
        _ ≤ 32 := (div_le_iff₀ hDR).mpr (by nlinarith)

theorem squarefreeRoughReciprocalGSquareTail_le
    {D Q : ℕ} (hD : 2 ≤ D) :
    squarefreeRoughReciprocalGSquareTail D Q ≤
      32 * Real.exp 32 / (D : ℝ) := by
  let A := ∑ p ∈ roughPrimeSupport D Q,
    maynardS2CrossPrimeSquareWeight p
  let E := ∏ p ∈ roughPrimeSupport D Q,
    (1 + maynardS2CrossPrimeSquareWeight p)
  have hA : A ≤ 32 / (D : ℝ) :=
    roughPrimeReciprocalGSquareWeightSum_le hD
  have hE : E ≤ Real.exp 32 :=
    roughPrimeReciprocalGSquareEulerProduct_le_exp_thirtyTwo hD
  have hA0 : 0 ≤ A := by
    unfold A
    exact Finset.sum_nonneg fun p hp =>
      maynardS2CrossPrimeSquareWeight_nonneg p
  have hE0 : 0 ≤ E := by
    unfold E
    exact Finset.prod_nonneg fun p hp =>
      add_nonneg zero_le_one (maynardS2CrossPrimeSquareWeight_nonneg p)
  calc
    squarefreeRoughReciprocalGSquareTail D Q ≤ E - 1 := by
      unfold E
      rw [← reciprocalGNonemptySubsetSum_eq_eulerProduct_sub_one]
      exact squarefreeRoughReciprocalGSquareTail_le_nonemptySubsetSum D Q
    _ ≤ A * E := by
      unfold A E
      exact eulerProduct_sub_one_le_sum_mul _ _
        maynardS2CrossPrimeSquareWeight_nonneg
    _ ≤ (32 / (D : ℝ)) * Real.exp 32 :=
      mul_le_mul hA hE hE0
        (div_nonneg (by norm_num) (Nat.cast_nonneg D))
    _ = 32 * Real.exp 32 / (D : ℝ) := by ring

end BoundedGaps.Maynard
