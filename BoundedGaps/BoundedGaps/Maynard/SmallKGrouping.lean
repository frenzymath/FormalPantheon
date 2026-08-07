import BoundedGaps.Maynard.BalancedEncoding
import BoundedGaps.Maynard.SmallKCertificate
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring

/-!
# Grouped exact small-k denominator

Maynard2013v3, source lines 716--733, gives the simplex integral as a
42-by-42 rational quadratic form. This module groups its ordered terms by the
sum of their two exponent pairs, without evaluating the grouped coefficients.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def smallKPairExponentSum (ij : Fin 42 × Fin 42) : ℕ × ℕ :=
  (smallKExponentB ij.1 + smallKExponentB ij.2,
    smallKExponentC ij.1 + smallKExponentC ij.2)

def smallKPairExponentSums : Finset (ℕ × ℕ) :=
  Finset.univ.image smallKPairExponentSum

def smallKGroupedCoefficient (p : ℕ × ℕ) : ℚ :=
  ∑ ij ∈ Finset.univ.filter (fun ij : Fin 42 × Fin 42 =>
      smallKPairExponentSum ij = p),
    smallKCoefficient ij.1 * smallKCoefficient ij.2

def smallKIntegerCoefficient (i : Fin 42) : ℤ :=
  (smallKCoefficient i).num

theorem smallK_integerCoefficient_cast (i : Fin 42) :
    (smallKIntegerCoefficient i : ℚ) = smallKCoefficient i := by
  fin_cases i <;> norm_num [smallKIntegerCoefficient, smallKCoefficient]

def smallKGroupedIntegerCoefficient (p : ℕ × ℕ) : ℤ :=
  ∑ ij ∈ Finset.univ.filter (fun ij : Fin 42 × Fin 42 =>
      smallKPairExponentSum ij = p),
    smallKIntegerCoefficient ij.1 * smallKIntegerCoefficient ij.2

theorem smallK_groupedIntegerCoefficient_cast (p : ℕ × ℕ) :
    (smallKGroupedIntegerCoefficient p : ℚ) = smallKGroupedCoefficient p := by
  classical
  unfold smallKGroupedIntegerCoefficient smallKGroupedCoefficient
  push_cast
  apply Finset.sum_congr rfl
  intro ij hij
  rw [smallK_integerCoefficient_cast, smallK_integerCoefficient_cast]

def smallKGroupedDenominator : ℚ :=
  ∑ p ∈ smallKPairExponentSums,
    smallKGroupedCoefficient p * smallKSimplexMoment p.1 p.2

theorem smallK_denominator_eq_grouped :
    smallKDenominator = smallKGroupedDenominator := by
  classical
  unfold smallKDenominator smallKGroupedDenominator smallKGroupedCoefficient
    smallKPairExponentSums smallKPairExponentSum
  rw [← Fintype.sum_prod_type']
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ.image fun ij : Fin 42 × Fin 42 =>
      (smallKExponentB ij.1 + smallKExponentB ij.2,
        smallKExponentC ij.1 + smallKExponentC ij.2))
    (g := fun ij : Fin 42 × Fin 42 =>
      (smallKExponentB ij.1 + smallKExponentB ij.2,
        smallKExponentC ij.1 + smallKExponentC ij.2))]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    have hpair := (Finset.mem_filter.mp hij).2
    have hb := congrArg Prod.fst hpair
    have hc := congrArg Prod.snd hpair
    simp only at hb hc
    rw [hb, hc]
  · intro ij hij
    exact Finset.mem_image_of_mem _ hij

theorem smallK_groupedIntegerCoefficient_sum_eq_square :
    (∑ p ∈ smallKPairExponentSums, smallKGroupedIntegerCoefficient p) =
      (∑ i : Fin 42, smallKIntegerCoefficient i) ^ 2 := by
  classical
  unfold smallKGroupedIntegerCoefficient smallKPairExponentSums
  rw [Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ.image smallKPairExponentSum)
    (g := smallKPairExponentSum)]
  · rw [Fintype.sum_prod_type]
    simp [pow_two, Finset.sum_mul, Finset.mul_sum, Finset.sum_comm, mul_comm]
  · intro ij hij
    exact Finset.mem_image_of_mem _ hij

set_option maxHeartbeats 2000000 in
theorem smallK_integerCoefficient_sum :
    (∑ i : Fin 42, smallKIntegerCoefficient i) = 18304414539680812 := by
  norm_num [smallKIntegerCoefficient, smallKCoefficient, Fin.sum_univ_succ]

def smallKExponentPairIndex (p : ℕ × ℕ) : ℕ := p.1 * 11 + p.2

theorem smallK_groupedIntegerCoefficient_encoding (x : ℤ) :
    (∑ p ∈ smallKPairExponentSums,
      smallKGroupedIntegerCoefficient p * x ^ smallKExponentPairIndex p) =
      (∑ i : Fin 42, smallKIntegerCoefficient i *
        x ^ smallKExponentPairIndex
          (smallKExponentB i, smallKExponentC i)) ^ 2 := by
  classical
  unfold smallKGroupedIntegerCoefficient smallKPairExponentSums
  calc
    (∑ p ∈ Finset.univ.image smallKPairExponentSum,
        (∑ ij ∈ Finset.univ.filter (fun ij : Fin 42 × Fin 42 =>
          smallKPairExponentSum ij = p),
          smallKIntegerCoefficient ij.1 * smallKIntegerCoefficient ij.2) *
          x ^ smallKExponentPairIndex p) =
      ∑ p ∈ Finset.univ.image smallKPairExponentSum,
        ∑ ij ∈ Finset.univ.filter (fun ij : Fin 42 × Fin 42 =>
          smallKPairExponentSum ij = p),
          smallKIntegerCoefficient ij.1 * smallKIntegerCoefficient ij.2 *
            x ^ smallKExponentPairIndex (smallKPairExponentSum ij) := by
              apply Finset.sum_congr rfl
              intro p hp
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro ij hij
              rw [(Finset.mem_filter.mp hij).2]
    _ = ∑ ij : Fin 42 × Fin 42,
        smallKIntegerCoefficient ij.1 * smallKIntegerCoefficient ij.2 *
          x ^ smallKExponentPairIndex (smallKPairExponentSum ij) := by
            rw [Finset.sum_fiberwise_of_maps_to
              (s := Finset.univ)
              (t := Finset.univ.image smallKPairExponentSum)
              (g := smallKPairExponentSum)]
            intro ij hij
            exact Finset.mem_image_of_mem _ hij
    _ = (∑ i : Fin 42, smallKIntegerCoefficient i *
        x ^ smallKExponentPairIndex
          (smallKExponentB i, smallKExponentC i)) ^ 2 := by
          rw [Fintype.sum_prod_type]
          have hindex (i j : Fin 42) :
              smallKExponentPairIndex (smallKPairExponentSum (i, j)) =
                smallKExponentPairIndex
                    (smallKExponentB i, smallKExponentC i) +
                  smallKExponentPairIndex
                    (smallKExponentB j, smallKExponentC j) := by
            simp only [smallKExponentPairIndex, smallKPairExponentSum]
            omega
          simp_rw [hindex, pow_add]
          rw [pow_two, Finset.sum_mul]
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring

theorem smallK_groupedIntegerCoefficient_abs_le_l1_sq (p : ℕ × ℕ) :
    |smallKGroupedIntegerCoefficient p| ≤
      (∑ i : Fin 42, |smallKIntegerCoefficient i|) ^ 2 := by
  classical
  unfold smallKGroupedIntegerCoefficient
  calc
    |∑ ij ∈ Finset.univ.filter (fun ij : Fin 42 × Fin 42 =>
        smallKPairExponentSum ij = p),
        smallKIntegerCoefficient ij.1 * smallKIntegerCoefficient ij.2| ≤
      ∑ ij ∈ Finset.univ.filter (fun ij : Fin 42 × Fin 42 =>
        smallKPairExponentSum ij = p),
        |smallKIntegerCoefficient ij.1 * smallKIntegerCoefficient ij.2| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ij : Fin 42 × Fin 42,
        |smallKIntegerCoefficient ij.1 * smallKIntegerCoefficient ij.2| := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · intro ij hij hnot
            exact abs_nonneg _
    _ = (∑ i : Fin 42, |smallKIntegerCoefficient i|) ^ 2 := by
          rw [Fintype.sum_prod_type]
          simp_rw [abs_mul]
          rw [pow_two, Finset.sum_mul]
          simp_rw [Finset.mul_sum]

set_option maxHeartbeats 2000000 in
theorem smallK_integerCoefficient_l1 :
    (∑ i : Fin 42, |smallKIntegerCoefficient i|) = 27954164601377036 := by
  norm_num [smallKIntegerCoefficient, smallKCoefficient, Fin.sum_univ_succ]

def smallKGroupedCoefficientBound : ℤ :=
  781435318560880942010147428145296

def smallKGroupedCoefficientBase : ℤ :=
  1562870637121761884020294856290593

theorem smallK_groupedIntegerCoefficient_abs_le_bound (p : ℕ × ℕ) :
    |smallKGroupedIntegerCoefficient p| ≤ smallKGroupedCoefficientBound := by
  calc
    |smallKGroupedIntegerCoefficient p| ≤
        (∑ i : Fin 42, |smallKIntegerCoefficient i|) ^ 2 :=
      smallK_groupedIntegerCoefficient_abs_le_l1_sq p
    _ = 27954164601377036 ^ 2 := by rw [smallK_integerCoefficient_l1]
    _ = smallKGroupedCoefficientBound := by
      norm_num [smallKGroupedCoefficientBound]

theorem smallK_groupedCoefficientBase_eq :
    smallKGroupedCoefficientBase = 2 * smallKGroupedCoefficientBound + 1 := by
  norm_num [smallKGroupedCoefficientBase, smallKGroupedCoefficientBound]

def smallKGroupedCoefficientDigits : List ℤ :=
  (List.range (23 * 11)).map fun n =>
    smallKGroupedIntegerCoefficient (n / 11, n % 11)

theorem smallK_groupedCoefficientDigits_length :
    smallKGroupedCoefficientDigits.length = 253 := by
  norm_num [smallKGroupedCoefficientDigits]

theorem smallK_groupedCoefficientDigits_abs_le {digit : ℤ}
    (hdigit : digit ∈ smallKGroupedCoefficientDigits) :
    |digit| ≤ smallKGroupedCoefficientBound := by
  rw [smallKGroupedCoefficientDigits, List.mem_map] at hdigit
  obtain ⟨n, hn, rfl⟩ := hdigit
  exact smallK_groupedIntegerCoefficient_abs_le_bound (n / 11, n % 11)

theorem smallK_groupedIntegerCoefficient_eq_zero_of_not_mem
    {p : ℕ × ℕ} (hp : p ∉ smallKPairExponentSums) :
    smallKGroupedIntegerCoefficient p = 0 := by
  classical
  unfold smallKGroupedIntegerCoefficient
  apply Finset.sum_eq_zero
  intro ij hij
  exfalso
  apply hp
  change p ∈ Finset.univ.image smallKPairExponentSum
  rw [← (Finset.mem_filter.mp hij).2]
  exact Finset.mem_image_of_mem smallKPairExponentSum
    ((Finset.mem_filter.mp hij).1)

def smallKRectanglePairs : Finset (ℕ × ℕ) :=
  (Finset.range 23).biUnion fun b =>
    (Finset.range 11).image fun c => (b, c)

/-! Every grouped exponent sum fits in the 23-by-11 rectangle. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem smallK_pairExponentSums_subset_rectangle :
    smallKPairExponentSums ⊆ smallKRectanglePairs := by
  decide

def smallKRectanglePairOfIndex (n : Fin 253) : ℕ × ℕ :=
  (n.1 / 11, n.1 % 11)

set_option maxRecDepth 100000 in
theorem smallK_rectanglePairs_eq_index_image :
    smallKRectanglePairs =
      Finset.univ.image smallKRectanglePairOfIndex := by
  decide

set_option maxRecDepth 100000 in
theorem smallK_rectanglePairs_card : smallKRectanglePairs.card = 253 := by
  decide

/-! The 253 rectangle slots are exactly reindexed by `Fin 253`. -/
set_option maxRecDepth 100000 in
theorem smallK_rectangle_sum_reindex {M : Type*} [AddCommMonoid M]
    (f : ℕ × ℕ → M) :
    (∑ n : Fin 253, f (smallKRectanglePairOfIndex n)) =
      ∑ p ∈ smallKRectanglePairs, f p := by
  classical
  rw [show (∑ n : Fin 253, f (smallKRectanglePairOfIndex n)) =
      ∑ n ∈ (Finset.univ : Finset (Fin 253)),
        f (smallKRectanglePairOfIndex n) by rfl]
  apply Finset.sum_bij (fun n _ => smallKRectanglePairOfIndex n)
  · intro n hn
    rw [smallK_rectanglePairs_eq_index_image]
    exact Finset.mem_image_of_mem _ hn
  · intro n₁ h₁ n₂ h₂ heq
    apply Fin.ext
    have hq := congrArg Prod.fst heq
    have hr := congrArg Prod.snd heq
    dsimp [smallKRectanglePairOfIndex] at hq hr
    have hn₁' := Nat.div_add_mod n₁.1 11
    have hn₂' := Nat.div_add_mod n₂.1 11
    omega
  · intro p hp
    rw [smallK_rectanglePairs_eq_index_image] at hp
    rcases Finset.mem_image.mp hp with ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  · intro n hn
    rfl

/-!
The true 253 signed digits encode the square of the original 42-term
coefficient polynomial at the fixed balanced base.
-/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem smallK_groupedCoefficientDigits_encoding :
    balancedIntegerEncode smallKGroupedCoefficientBase
      smallKGroupedCoefficientDigits =
      (∑ i : Fin 42, smallKIntegerCoefficient i *
        smallKGroupedCoefficientBase ^ smallKExponentPairIndex
          (smallKExponentB i, smallKExponentC i)) ^ 2 := by
  have henc := balancedIntegerEncode_eq_sum smallKGroupedCoefficientBase
    smallKGroupedCoefficientDigits
  norm_num [smallKGroupedCoefficientDigits] at henc
  change balancedIntegerEncode smallKGroupedCoefficientBase
      ((List.range 253).map fun n =>
        smallKGroupedIntegerCoefficient (n / 11, n % 11)) = _
  rw [henc]
  have hindex (n : Fin 253) :
      smallKExponentPairIndex (smallKRectanglePairOfIndex n) = n.1 := by
    simp only [smallKExponentPairIndex, smallKRectanglePairOfIndex]
    have hdiv := Nat.div_add_mod n.1 11
    omega
  have hrect := smallK_rectangle_sum_reindex (fun p : ℕ × ℕ =>
    smallKGroupedIntegerCoefficient p *
      smallKGroupedCoefficientBase ^ smallKExponentPairIndex p)
  have hsum :
      (∑ x : Fin 253,
        smallKGroupedIntegerCoefficient (x.1 / 11, x.1 % 11) *
          smallKGroupedCoefficientBase ^ x.1) =
        ∑ p ∈ smallKRectanglePairs,
          smallKGroupedIntegerCoefficient p *
            smallKGroupedCoefficientBase ^ smallKExponentPairIndex p := by
    calc
      (∑ x : Fin 253,
          smallKGroupedIntegerCoefficient (x.1 / 11, x.1 % 11) *
            smallKGroupedCoefficientBase ^ x.1) =
          ∑ x : Fin 253,
            smallKGroupedIntegerCoefficient (smallKRectanglePairOfIndex x) *
              smallKGroupedCoefficientBase ^
                smallKExponentPairIndex (smallKRectanglePairOfIndex x) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hindex x]
            rfl
      _ = ∑ p ∈ smallKRectanglePairs,
          smallKGroupedIntegerCoefficient p *
            smallKGroupedCoefficientBase ^ smallKExponentPairIndex p := hrect
  have hsubset :
      (∑ p ∈ smallKPairExponentSums,
        smallKGroupedIntegerCoefficient p *
          smallKGroupedCoefficientBase ^ smallKExponentPairIndex p) =
        ∑ p ∈ smallKRectanglePairs,
          smallKGroupedIntegerCoefficient p *
            smallKGroupedCoefficientBase ^ smallKExponentPairIndex p :=
    Finset.sum_subset smallK_pairExponentSums_subset_rectangle
      (fun p hpRect hpSupport => by
        rw [smallK_groupedIntegerCoefficient_eq_zero_of_not_mem hpSupport]
        simp)
  calc
    (∑ x : Fin 253,
        smallKGroupedIntegerCoefficient (x.1 / 11, x.1 % 11) *
          smallKGroupedCoefficientBase ^ x.1) =
        ∑ p ∈ smallKRectanglePairs,
          smallKGroupedIntegerCoefficient p *
            smallKGroupedCoefficientBase ^ smallKExponentPairIndex p := hsum
    _ = ∑ p ∈ smallKPairExponentSums,
          smallKGroupedIntegerCoefficient p *
            smallKGroupedCoefficientBase ^ smallKExponentPairIndex p := hsubset.symm
    _ = (∑ i : Fin 42, smallKIntegerCoefficient i *
        smallKGroupedCoefficientBase ^ smallKExponentPairIndex
          (smallKExponentB i, smallKExponentC i)) ^ 2 :=
      smallK_groupedIntegerCoefficient_encoding smallKGroupedCoefficientBase

end BoundedGaps.Maynard
