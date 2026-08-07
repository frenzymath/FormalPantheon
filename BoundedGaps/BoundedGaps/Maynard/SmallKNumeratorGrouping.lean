import BoundedGaps.Maynard.SmallKCertificate
import BoundedGaps.Maynard.SmallKGrouping
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

/-!
# Scaled face grouping for the small-k numerator

The face-integrated coefficients in `Maynard2013v3`, printed Section 8,
Lemma `lmm:QuadraticForms` (source lines 716--751), have factorial
denominators bounded by `12!`. This module clears those denominators before
grouping the ordered face pairs.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def smallKFaceScale : ℤ := 479001600

def smallKIntegratedRationalCoefficient (i : Fin 42) (cp : Fin 6) : ℚ :=
  if _h : cp.1 ≤ smallKExponentC i then
    ((Nat.choose (smallKExponentC i) cp.1 : ℚ) *
        Nat.factorial (smallKExponentB i) *
        Nat.factorial (2 * smallKExponentC i - 2 * cp.1)) /
      Nat.factorial (smallKExponentB i + 2 * smallKExponentC i -
        2 * cp.1 + 1)
  else 0

def smallKIntegratedIntegerCoefficient (i : Fin 42) (cp : Fin 6) : ℤ :=
  if _h : cp.1 ≤ smallKExponentC i then
    smallKIntegerCoefficient i *
      (Nat.choose (smallKExponentC i) cp.1 *
        Nat.factorial (smallKExponentB i) *
        Nat.factorial (2 * smallKExponentC i - 2 * cp.1) *
        (Nat.factorial 12 /
          Nat.factorial (smallKExponentB i + 2 * smallKExponentC i -
            2 * cp.1 + 1)) : ℕ)
  else 0

/-! Scaling by `12!` gives the exact rational face coefficient. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem smallK_integratedIntegerCoefficient_cast (i : Fin 42) (cp : Fin 6) :
    (smallKIntegratedIntegerCoefficient i cp : ℚ) =
      smallKFaceScale * (smallKIntegerCoefficient i : ℚ) *
        smallKIntegratedRationalCoefficient i cp := by
  fin_cases i <;> fin_cases cp <;>
    norm_num [smallKIntegratedIntegerCoefficient,
      smallKIntegratedRationalCoefficient, smallKFaceScale,
      smallKIntegerCoefficient, smallKCoefficient, smallKExponentB,
      smallKExponentC, Nat.choose]

def smallKIntegratedExponentPair (t : Fin 42 × Fin 6) : ℕ × ℕ :=
  (smallKExponentB t.1 + 2 * smallKExponentC t.1 - 2 * t.2.1 + 1,
    t.2.1)

def smallKIntegratedPairExponentSum
    (tu : (Fin 42 × Fin 6) × (Fin 42 × Fin 6)) : ℕ × ℕ :=
  ((smallKIntegratedExponentPair tu.1).1 +
      (smallKIntegratedExponentPair tu.2).1,
    (smallKIntegratedExponentPair tu.1).2 +
      (smallKIntegratedExponentPair tu.2).2)

def smallKIntegratedPairExponentSums : Finset (ℕ × ℕ) :=
  Finset.univ.image smallKIntegratedPairExponentSum

def smallKGroupedIntegratedIntegerCoefficient (p : ℕ × ℕ) : ℤ :=
  ∑ tu ∈ Finset.univ.filter
      (fun tu : (Fin 42 × Fin 6) × (Fin 42 × Fin 6) =>
        smallKIntegratedPairExponentSum tu = p),
    smallKIntegratedIntegerCoefficient tu.1.1 tu.1.2 *
      smallKIntegratedIntegerCoefficient tu.2.1 tu.2.2

/-!
The grouped scaled face coefficients form the square of the transformed
single-polynomial encoding.
-/
set_option maxRecDepth 100000 in
theorem smallK_groupedIntegratedIntegerCoefficient_encoding (x : ℤ) :
    (∑ p ∈ smallKIntegratedPairExponentSums,
      smallKGroupedIntegratedIntegerCoefficient p *
        x ^ smallKExponentPairIndex p) =
      (∑ t : Fin 42 × Fin 6,
        smallKIntegratedIntegerCoefficient t.1 t.2 *
          x ^ smallKExponentPairIndex (smallKIntegratedExponentPair t)) ^ 2 := by
  classical
  unfold smallKGroupedIntegratedIntegerCoefficient
    smallKIntegratedPairExponentSums
  calc
    (∑ p ∈ Finset.univ.image smallKIntegratedPairExponentSum,
        (∑ tu ∈ Finset.univ.filter
          (fun tu : (Fin 42 × Fin 6) × (Fin 42 × Fin 6) =>
            smallKIntegratedPairExponentSum tu = p),
          smallKIntegratedIntegerCoefficient tu.1.1 tu.1.2 *
            smallKIntegratedIntegerCoefficient tu.2.1 tu.2.2) *
          x ^ smallKExponentPairIndex p) =
      ∑ p ∈ Finset.univ.image smallKIntegratedPairExponentSum,
        ∑ tu ∈ Finset.univ.filter
          (fun tu : (Fin 42 × Fin 6) × (Fin 42 × Fin 6) =>
            smallKIntegratedPairExponentSum tu = p),
          smallKIntegratedIntegerCoefficient tu.1.1 tu.1.2 *
            smallKIntegratedIntegerCoefficient tu.2.1 tu.2.2 *
              x ^ smallKExponentPairIndex
                (smallKIntegratedPairExponentSum tu) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro tu htu
      rw [(Finset.mem_filter.mp htu).2]
    _ = ∑ tu : (Fin 42 × Fin 6) × (Fin 42 × Fin 6),
        smallKIntegratedIntegerCoefficient tu.1.1 tu.1.2 *
          smallKIntegratedIntegerCoefficient tu.2.1 tu.2.2 *
            x ^ smallKExponentPairIndex
              (smallKIntegratedPairExponentSum tu) := by
      rw [Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ)
        (t := Finset.univ.image smallKIntegratedPairExponentSum)
        (g := smallKIntegratedPairExponentSum)]
      intro tu htu
      exact Finset.mem_image_of_mem _ htu
    _ = (∑ t : Fin 42 × Fin 6,
        smallKIntegratedIntegerCoefficient t.1 t.2 *
          x ^ smallKExponentPairIndex
            (smallKIntegratedExponentPair t)) ^ 2 := by
      rw [Fintype.sum_prod_type]
      have hindex (t u : Fin 42 × Fin 6) :
          smallKExponentPairIndex (smallKIntegratedPairExponentSum (t, u)) =
            smallKExponentPairIndex (smallKIntegratedExponentPair t) +
              smallKExponentPairIndex (smallKIntegratedExponentPair u) := by
        simp only [smallKExponentPairIndex, smallKIntegratedPairExponentSum]
        omega
      simp_rw [hindex, pow_add]
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      ring

set_option maxRecDepth 100000 in
theorem smallK_groupedIntegratedIntegerCoefficient_abs_le_l1_sq
    (p : ℕ × ℕ) :
    |smallKGroupedIntegratedIntegerCoefficient p| ≤
      (∑ t : Fin 42 × Fin 6,
        |smallKIntegratedIntegerCoefficient t.1 t.2|) ^ 2 := by
  classical
  unfold smallKGroupedIntegratedIntegerCoefficient
  calc
    |∑ tu ∈ Finset.univ.filter
        (fun tu : (Fin 42 × Fin 6) × (Fin 42 × Fin 6) =>
          smallKIntegratedPairExponentSum tu = p),
        smallKIntegratedIntegerCoefficient tu.1.1 tu.1.2 *
          smallKIntegratedIntegerCoefficient tu.2.1 tu.2.2| ≤
      ∑ tu ∈ Finset.univ.filter
        (fun tu : (Fin 42 × Fin 6) × (Fin 42 × Fin 6) =>
          smallKIntegratedPairExponentSum tu = p),
        |smallKIntegratedIntegerCoefficient tu.1.1 tu.1.2 *
          smallKIntegratedIntegerCoefficient tu.2.1 tu.2.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ tu : (Fin 42 × Fin 6) × (Fin 42 × Fin 6),
        |smallKIntegratedIntegerCoefficient tu.1.1 tu.1.2 *
          smallKIntegratedIntegerCoefficient tu.2.1 tu.2.2| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro tu htu hnot
        exact abs_nonneg _
    _ = (∑ t : Fin 42 × Fin 6,
        |smallKIntegratedIntegerCoefficient t.1 t.2|) ^ 2 := by
      rw [Fintype.sum_prod_type]
      simp_rw [abs_mul]
      rw [pow_two, Finset.sum_mul]
      simp_rw [Finset.mul_sum]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem smallK_integratedIntegerCoefficient_l1 :
    (∑ t : Fin 42 × Fin 6,
      |smallKIntegratedIntegerCoefficient t.1 t.2|) =
      2019306969156430452545280 := by
  rw [Fintype.sum_prod_type]
  norm_num [smallKIntegratedIntegerCoefficient, smallKIntegerCoefficient,
    smallKCoefficient, smallKExponentB, smallKExponentC, Nat.choose,
    Fin.sum_univ_succ]

def smallKIntegratedGroupedCoefficientBound : ℤ :=
  4077600635683729167001485870596161098030450278400

def smallKIntegratedGroupedCoefficientBase : ℤ :=
  8155201271367458334002971741192322196060900556801

theorem smallK_groupedIntegratedIntegerCoefficient_abs_le_bound
    (p : ℕ × ℕ) :
    |smallKGroupedIntegratedIntegerCoefficient p| ≤
      smallKIntegratedGroupedCoefficientBound := by
  calc
    |smallKGroupedIntegratedIntegerCoefficient p| ≤
        (∑ t : Fin 42 × Fin 6,
          |smallKIntegratedIntegerCoefficient t.1 t.2|) ^ 2 :=
      smallK_groupedIntegratedIntegerCoefficient_abs_le_l1_sq p
    _ = 2019306969156430452545280 ^ 2 := by
      rw [smallK_integratedIntegerCoefficient_l1]
    _ = smallKIntegratedGroupedCoefficientBound := by
      norm_num [smallKIntegratedGroupedCoefficientBound]

theorem smallK_integratedGroupedCoefficientBase_eq :
    smallKIntegratedGroupedCoefficientBase =
      2 * smallKIntegratedGroupedCoefficientBound + 1 := by
  norm_num [smallKIntegratedGroupedCoefficientBase,
    smallKIntegratedGroupedCoefficientBound]

theorem smallK_integratedExponentPair_bound (t : Fin 42 × Fin 6) :
    (smallKIntegratedExponentPair t).1 ≤ 12 ∧
      (smallKIntegratedExponentPair t).2 < 6 := by
  have hsource := smallK_exponent_bound t.1
  constructor
  · simp only [smallKIntegratedExponentPair]
    omega
  · exact t.2.isLt

end BoundedGaps.Maynard
