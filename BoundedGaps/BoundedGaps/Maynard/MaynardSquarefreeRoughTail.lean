import BoundedGaps.Maynard.MaynardLambdaTotientRegrouping
import BoundedGaps.Maynard.MaynardReciprocalSquareTail
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Exponential

noncomputable section

/-!
# A squarefree rough reciprocal-totient-square tail

Squarefree integers are encoded by subsets of a finite prime interval.  The
resulting Euler product upgrades the prime tail to the composite tail needed
for Maynard's cross variables.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def primeTotientSquareWeight (p : ℕ) : ℝ :=
  (1 : ℝ) / (Nat.totient p : ℝ) ^ 2

theorem primeTotientSquareWeight_nonneg (p : ℕ) :
    0 ≤ primeTotientSquareWeight p := by
  unfold primeTotientSquareWeight
  positivity

def roughPrimeSupport (D Q : ℕ) : Finset ℕ :=
  (Finset.Icc (D + 1) Q).filter Nat.Prime

def squarefreeRoughSupport (D Q : ℕ) : Finset ℕ :=
  (Finset.Icc 2 Q).filter fun n =>
    Squarefree n ∧ n.primeFactors ⊆ roughPrimeSupport D Q

def squarefreeRoughTotientSquareTail (D Q : ℕ) : ℝ :=
  ∑ n ∈ squarefreeRoughSupport D Q,
    (1 : ℝ) / (Nat.totient n : ℝ) ^ 2

theorem squarefreeRoughSupport_squarefree
    {D Q n : ℕ} (hn : n ∈ squarefreeRoughSupport D Q) :
    Squarefree n :=
  (Finset.mem_filter.mp hn).2.1

theorem squarefreeRoughSupport_one_lt
    {D Q n : ℕ} (hn : n ∈ squarefreeRoughSupport D Q) :
    1 < n := by
  exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1

theorem squarefreeRoughSupport_primeFactors_subset
    {D Q n : ℕ} (hn : n ∈ squarefreeRoughSupport D Q) :
    n.primeFactors ⊆ roughPrimeSupport D Q :=
  (Finset.mem_filter.mp hn).2.2

theorem primeFactors_injOn_squarefreeRoughSupport (D Q : ℕ) :
    Set.InjOn Nat.primeFactors (squarefreeRoughSupport D Q) := by
  intro m hm n hn hmn
  calc
    m = ∏ p ∈ m.primeFactors, p :=
      (Nat.prod_primeFactors_of_squarefree
        (squarefreeRoughSupport_squarefree hm)).symm
    _ = ∏ p ∈ n.primeFactors, p := by rw [hmn]
    _ = n := Nat.prod_primeFactors_of_squarefree
      (squarefreeRoughSupport_squarefree hn)

theorem totient_eq_prod_primeFactors_of_squarefree
    {n : ℕ} (hn : Squarefree n) :
    Nat.totient n = ∏ p ∈ n.primeFactors, Nat.totient p := by
  have htot : Nat.totient n = ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [Nat.totient_eq_div_primeFactors_mul,
      Nat.prod_primeFactors_of_squarefree hn,
      Nat.div_self (Nat.pos_of_ne_zero hn.ne_zero), one_mul]
  rw [htot]
  apply Finset.prod_congr rfl
  intro p hp
  exact (Nat.totient_prime (Nat.prime_of_mem_primeFactors hp)).symm

theorem inv_totient_sq_eq_primeFactors_product
    {n : ℕ} (hn : Squarefree n) :
    (1 : ℝ) / (Nat.totient n : ℝ) ^ 2 =
      ∏ p ∈ n.primeFactors, primeTotientSquareWeight p := by
  rw [totient_eq_prod_primeFactors_of_squarefree hn]
  push_cast
  unfold primeTotientSquareWeight
  rw [← Finset.prod_pow]
  simp only [one_div, Finset.prod_inv_distrib]

theorem squarefreeRoughTail_eq_primeFactorImageSum (D Q : ℕ) :
    squarefreeRoughTotientSquareTail D Q =
      ∑ t ∈ (squarefreeRoughSupport D Q).image Nat.primeFactors,
        ∏ p ∈ t, primeTotientSquareWeight p := by
  classical
  unfold squarefreeRoughTotientSquareTail
  calc
    (∑ n ∈ squarefreeRoughSupport D Q,
        (1 : ℝ) / (Nat.totient n : ℝ) ^ 2) =
        ∑ n ∈ squarefreeRoughSupport D Q,
          ∏ p ∈ n.primeFactors, primeTotientSquareWeight p := by
      apply Finset.sum_congr rfl
      intro n hn
      exact inv_totient_sq_eq_primeFactors_product
        (squarefreeRoughSupport_squarefree hn)
    _ = _ := by
      rw [Finset.sum_image]
      intro m hm n hn hmn
      exact primeFactors_injOn_squarefreeRoughSupport D Q hm hn hmn

theorem primeFactorImage_subset_nonemptyPowerset (D Q : ℕ) :
    (squarefreeRoughSupport D Q).image Nat.primeFactors ⊆
      (roughPrimeSupport D Q).powerset.erase ∅ := by
  intro t ht
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
  apply Finset.mem_erase.mpr
  refine ⟨?_, Finset.mem_powerset.mpr
    (squarefreeRoughSupport_primeFactors_subset hn)⟩
  exact (Nat.nonempty_primeFactors.mpr
    (squarefreeRoughSupport_one_lt hn)).ne_empty

theorem squarefreeRoughTail_le_nonemptySubsetSum (D Q : ℕ) :
    squarefreeRoughTotientSquareTail D Q ≤
      ∑ t ∈ (roughPrimeSupport D Q).powerset.erase ∅,
        ∏ p ∈ t, primeTotientSquareWeight p := by
  classical
  rw [squarefreeRoughTail_eq_primeFactorImageSum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (primeFactorImage_subset_nonemptyPowerset D Q)
  intro t ht htNot
  apply Finset.prod_nonneg
  intro p hp
  exact primeTotientSquareWeight_nonneg p

theorem nonemptySubsetSum_eq_eulerProduct_sub_one (D Q : ℕ) :
    (∑ t ∈ (roughPrimeSupport D Q).powerset.erase ∅,
        ∏ p ∈ t, primeTotientSquareWeight p) =
      (∏ p ∈ roughPrimeSupport D Q,
        (1 + primeTotientSquareWeight p)) - 1 := by
  classical
  have hempty : ∅ ∈ (roughPrimeSupport D Q).powerset := by simp
  have herase := Finset.sum_erase_add
    (s := (roughPrimeSupport D Q).powerset)
    (f := fun t => ∏ p ∈ t, primeTotientSquareWeight p) hempty
  rw [Finset.prod_one_add]
  simp only [Finset.prod_empty] at herase
  linarith

theorem eulerProduct_sub_one_le_sum_mul
    (P : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ p, 0 ≤ f p) :
    (∏ p ∈ P, (1 + f p)) - 1 ≤
      (∑ p ∈ P, f p) * ∏ p ∈ P, (1 + f p) := by
  nth_rw 1 [Finset.prod_one_add_ordered]
  simp only [add_sub_cancel_left]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (hf p)
  apply Finset.prod_le_prod_of_subset_of_one_le
    (Finset.filter_subset _ _)
  · intro q hq
    exact add_nonneg zero_le_one (hf q)
  intro q hq hqNot
  exact le_add_of_nonneg_right (hf q)

theorem roughPrimeWeightSum_eq_primeTail (D Q : ℕ) :
    (∑ p ∈ roughPrimeSupport D Q, primeTotientSquareWeight p) =
      primeTotientSquareTail D (Q + 1) := by
  unfold roughPrimeSupport primeTotientSquareWeight
    primeTotientSquareTail
  congr 2

theorem roughPrimeWeightSum_le
    {D Q : ℕ} (hD : 0 < D) :
    (∑ p ∈ roughPrimeSupport D Q, primeTotientSquareWeight p) ≤
      8 / (D : ℝ) := by
  rw [roughPrimeWeightSum_eq_primeTail]
  exact primeTotientSquareTail_le hD

theorem roughPrimeEulerProduct_le_exp_eight
    {D Q : ℕ} (hD : 0 < D) :
    (∏ p ∈ roughPrimeSupport D Q,
        (1 + primeTotientSquareWeight p)) ≤ Real.exp 8 := by
  calc
    (∏ p ∈ roughPrimeSupport D Q,
        (1 + primeTotientSquareWeight p)) ≤
        Real.exp (∑ p ∈ roughPrimeSupport D Q,
          primeTotientSquareWeight p) := by
      exact Real.prod_one_add_le_exp_sum _
        primeTotientSquareWeight_nonneg
    _ ≤ Real.exp 8 := by
      apply Real.exp_le_exp.mpr
      have hsum := roughPrimeWeightSum_le (Q := Q) hD
      have hDR : (0 : ℝ) < D := by exact_mod_cast hD
      have hDone : (1 : ℝ) ≤ D := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hD.ne')
      calc
        (∑ p ∈ roughPrimeSupport D Q,
            primeTotientSquareWeight p) ≤ 8 / (D : ℝ) := hsum
        _ ≤ 8 := by
          exact (div_le_iff₀ hDR).mpr (by nlinarith)

theorem squarefreeRoughTotientSquareTail_le
    {D Q : ℕ} (hD : 0 < D) :
    squarefreeRoughTotientSquareTail D Q ≤
      8 * Real.exp 8 / (D : ℝ) := by
  let A := ∑ p ∈ roughPrimeSupport D Q, primeTotientSquareWeight p
  let E := ∏ p ∈ roughPrimeSupport D Q,
    (1 + primeTotientSquareWeight p)
  have hA : A ≤ 8 / (D : ℝ) := roughPrimeWeightSum_le hD
  have hE : E ≤ Real.exp 8 := roughPrimeEulerProduct_le_exp_eight hD
  have hAnonneg : 0 ≤ A := by
    unfold A
    apply Finset.sum_nonneg
    intro p hp
    exact primeTotientSquareWeight_nonneg p
  have hEnonneg : 0 ≤ E := by
    unfold E
    apply Finset.prod_nonneg
    intro p hp
    exact add_nonneg zero_le_one (primeTotientSquareWeight_nonneg p)
  calc
    squarefreeRoughTotientSquareTail D Q ≤ E - 1 := by
      unfold E
      rw [← nonemptySubsetSum_eq_eulerProduct_sub_one]
      exact squarefreeRoughTail_le_nonemptySubsetSum D Q
    _ ≤ A * E := by
      unfold A E
      exact eulerProduct_sub_one_le_sum_mul _ _
        primeTotientSquareWeight_nonneg
    _ ≤ (8 / (D : ℝ)) * Real.exp 8 :=
      mul_le_mul hA hE hEnonneg
        (div_nonneg (by norm_num) (Nat.cast_nonneg D))
    _ = 8 * Real.exp 8 / (D : ℝ) := by ring

end BoundedGaps.Maynard
