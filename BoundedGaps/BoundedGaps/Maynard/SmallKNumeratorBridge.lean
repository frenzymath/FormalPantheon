import BoundedGaps.Maynard.SmallKNumeratorGrouping
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Rational bridge for the small-k numerator

This module converts the source's dependent face ranges to the fixed `Fin 6`
index used by the scaled integer grouping certificate.

Source: `Maynard2013v3`, printed Section 8, Lemma
`lmm:QuadraticForms`, source lines 716--751. Semantic reviews: `SEM-082` and
`SEM-083`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def smallKSimplexMoment104 (b c : ℕ) : ℚ :=
  (Nat.factorial b : ℚ) / Nat.factorial (104 + b + 2 * c) * smallKG104 c

def smallKFacePairTerm (i j : Fin 42) (cp dp : ℕ) : ℚ :=
  ((Nat.choose (smallKExponentC i) cp : ℚ) *
      Nat.factorial (smallKExponentB i) *
      Nat.factorial (2 * smallKExponentC i - 2 * cp) /
    Nat.factorial (smallKExponentB i + 2 * smallKExponentC i -
      2 * cp + 1)) *
    ((Nat.choose (smallKExponentC j) dp : ℚ) *
      Nat.factorial (smallKExponentB j) *
      Nat.factorial (2 * smallKExponentC j - 2 * dp) /
    Nat.factorial (smallKExponentB j + 2 * smallKExponentC j -
      2 * dp + 1)) *
    ((Nat.factorial (smallKExponentB i + 2 * smallKExponentC i -
          2 * cp + 1 + smallKExponentB j +
          2 * smallKExponentC j - 2 * dp + 1) : ℚ) /
      Nat.factorial (104 + smallKExponentB i +
        2 * smallKExponentC i - 2 * cp + 1 +
        smallKExponentB j + 2 * smallKExponentC j - 2 * dp + 1 +
        2 * (cp + dp))) *
    smallKG104 (cp + dp)

theorem smallK_sum_range_succ_eq_fin6 {n : ℕ} (hn : n ≤ 5)
    (f : ℕ → ℚ) :
    (∑ cp ∈ Finset.range (n + 1), f cp) =
      ∑ cp : Fin 6, if cp.1 ≤ n then f cp.1 else 0 := by
  interval_cases n <;>
    norm_num [Fin.sum_univ_succ, Finset.sum_range_succ] <;>
    ring

/-! The source's dependent face ranges are exactly the bounded `Fin 6` sums. -/
theorem smallK_face_pair_sum_eq_fin6 (i j : Fin 42) :
    (∑ cp ∈ Finset.range (smallKExponentC i + 1),
      ∑ dp ∈ Finset.range (smallKExponentC j + 1),
        smallKFacePairTerm i j cp dp) =
      ∑ cp : Fin 6, ∑ dp : Fin 6,
        smallKIntegratedRationalCoefficient i cp *
          smallKIntegratedRationalCoefficient j dp *
            smallKSimplexMoment104
              (smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1 +
                smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1)
              (cp.1 + dp.1) := by
  have hi : smallKExponentC i ≤ 5 := by
    have h := smallK_exponent_bound i
    omega
  have hj : smallKExponentC j ≤ 5 := by
    have h := smallK_exponent_bound j
    omega
  rw [smallK_sum_range_succ_eq_fin6 hi]
  apply Finset.sum_congr rfl
  intro cp hcp
  by_cases hcpC : cp.1 ≤ smallKExponentC i
  · simp only [if_pos hcpC]
    rw [smallK_sum_range_succ_eq_fin6 hj]
    apply Finset.sum_congr rfl
    intro dp hdp
    by_cases hdpC : dp.1 ≤ smallKExponentC j
    · simp only [if_pos hdpC]
      simp only [smallKIntegratedRationalCoefficient, dif_pos hcpC,
        dif_pos hdpC, smallKFacePairTerm, smallKSimplexMoment104]
      have hsum :
          smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1 +
              smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1 =
            (smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1) +
              (smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1) := by
        omega
      have hden :
          104 + smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1 +
              smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1 +
              2 * (cp.1 + dp.1) =
            104 + ((smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1) +
              (smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1)) +
            2 * (cp.1 + dp.1) := by
        omega
      rw [hsum, hden]
      ring
    · simp only [if_neg hdpC]
      simp [smallKIntegratedRationalCoefficient, hdpC]
  · simp only [if_neg hcpC]
    simp [smallKIntegratedRationalCoefficient, hcpC]

def smallKGroupedNumeratorCoefficient (p : ℕ × ℕ) : ℚ :=
  (105 : ℚ) / (smallKFaceScale : ℚ) ^ 2 *
    (smallKGroupedIntegratedIntegerCoefficient p : ℚ)

def smallKGroupedNumerator : ℚ :=
  ∑ p ∈ smallKIntegratedPairExponentSums,
    smallKGroupedNumeratorCoefficient p *
      smallKSimplexMoment104 p.1 p.2

theorem smallK_scaled_face_pair_term (i j : Fin 42) (cp dp : Fin 6) :
    105 * smallKCoefficient i * smallKCoefficient j *
        (smallKIntegratedRationalCoefficient i cp *
          smallKIntegratedRationalCoefficient j dp *
            smallKSimplexMoment104
              ((smallKIntegratedExponentPair (i, cp)).1 +
                (smallKIntegratedExponentPair (j, dp)).1)
              (cp.1 + dp.1)) =
      (105 : ℚ) / (smallKFaceScale : ℚ) ^ 2 *
        (smallKIntegratedIntegerCoefficient i cp : ℚ) *
        (smallKIntegratedIntegerCoefficient j dp : ℚ) *
          smallKSimplexMoment104
            ((smallKIntegratedExponentPair (i, cp)).1 +
              (smallKIntegratedExponentPair (j, dp)).1)
            (cp.1 + dp.1) := by
  have hscale : (smallKFaceScale : ℚ) ≠ 0 := by
    norm_num [smallKFaceScale]
  rw [smallK_integratedIntegerCoefficient_cast,
    smallK_integratedIntegerCoefficient_cast,
    smallK_integerCoefficient_cast, smallK_integerCoefficient_cast]
  field_simp [hscale]

set_option maxHeartbeats 2000000 in
theorem smallK_numerator_eq_scaled_pair_sum :
    smallKNumerator =
      ∑ tu : (Fin 42 × Fin 6) × (Fin 42 × Fin 6),
        (105 : ℚ) / (smallKFaceScale : ℚ) ^ 2 *
          (smallKIntegratedIntegerCoefficient tu.1.1 tu.1.2 : ℚ) *
          (smallKIntegratedIntegerCoefficient tu.2.1 tu.2.2 : ℚ) *
            smallKSimplexMoment104
              (smallKIntegratedPairExponentSum tu).1
              (smallKIntegratedPairExponentSum tu).2 := by
  classical
  rw [show smallKNumerator =
      105 * ∑ i : Fin 42, ∑ j : Fin 42,
        smallKCoefficient i * smallKCoefficient j *
          (∑ cp ∈ Finset.range (smallKExponentC i + 1),
            ∑ dp ∈ Finset.range (smallKExponentC j + 1),
              smallKFacePairTerm i j cp dp) by
    simp [smallKNumerator, smallKFacePairTerm,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]]
  calc
    105 * ∑ i : Fin 42, ∑ j : Fin 42,
        smallKCoefficient i * smallKCoefficient j *
          (∑ cp ∈ Finset.range (smallKExponentC i + 1),
            ∑ dp ∈ Finset.range (smallKExponentC j + 1),
              smallKFacePairTerm i j cp dp) =
        ∑ i : Fin 42, ∑ j : Fin 42, ∑ cp : Fin 6, ∑ dp : Fin 6,
          105 * smallKCoefficient i * smallKCoefficient j *
            (smallKIntegratedRationalCoefficient i cp *
                smallKIntegratedRationalCoefficient j dp *
                  smallKSimplexMoment104
                  (smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1 +
                    smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1)
                  (cp.1 + dp.1)) := by
      simp_rw [show (105 : ℚ) * ∑ i : Fin 42, _ =
          ∑ i : Fin 42, 105 * _ by rw [Finset.mul_sum]]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [smallK_face_pair_sum_eq_fin6]
      calc
        105 * (smallKCoefficient i * smallKCoefficient j *
            (∑ cp : Fin 6, ∑ dp : Fin 6,
              smallKIntegratedRationalCoefficient i cp *
                smallKIntegratedRationalCoefficient j dp *
                  smallKSimplexMoment104
                    (smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1 +
                      smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1)
                    (cp.1 + dp.1))) =
            (105 * smallKCoefficient i * smallKCoefficient j) *
              (∑ cp : Fin 6, ∑ dp : Fin 6,
                smallKIntegratedRationalCoefficient i cp *
                  smallKIntegratedRationalCoefficient j dp *
                    smallKSimplexMoment104
                      (smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1 +
                        smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1)
                      (cp.1 + dp.1)) := by ring
        _ = ∑ cp : Fin 6, (105 * smallKCoefficient i * smallKCoefficient j) *
              (∑ dp : Fin 6,
                smallKIntegratedRationalCoefficient i cp *
                  smallKIntegratedRationalCoefficient j dp *
                    smallKSimplexMoment104
                      (smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1 +
                        smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1)
                      (cp.1 + dp.1)) := by
              rw [Finset.mul_sum]
        _ = ∑ cp : Fin 6, ∑ dp : Fin 6,
              105 * smallKCoefficient i * smallKCoefficient j *
                (smallKIntegratedRationalCoefficient i cp *
                  smallKIntegratedRationalCoefficient j dp *
                    smallKSimplexMoment104
                      (smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1 +
                        smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1)
                      (cp.1 + dp.1)) := by
              apply Finset.sum_congr rfl
              intro cp hcp
              rw [Finset.mul_sum]
    _ = ∑ i : Fin 42, ∑ j : Fin 42, ∑ cp : Fin 6, ∑ dp : Fin 6,
        (105 : ℚ) / (smallKFaceScale : ℚ) ^ 2 *
          (smallKIntegratedIntegerCoefficient i cp : ℚ) *
          (smallKIntegratedIntegerCoefficient j dp : ℚ) *
            smallKSimplexMoment104
              (smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1 +
                smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1)
              (cp.1 + dp.1) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro cp hcp
      apply Finset.sum_congr rfl
      intro dp hdp
      by_cases hcpC : cp.1 ≤ smallKExponentC i
      · by_cases hdpC : dp.1 ≤ smallKExponentC j
        · have hci : 2 * cp.1 ≤ smallKExponentB i + 2 * smallKExponentC i := by
            omega
          have hcj : 2 * dp.1 ≤ smallKExponentB j + 2 * smallKExponentC j := by
            omega
          have hpair :
              (smallKIntegratedExponentPair (i, cp)).1 +
                  (smallKIntegratedExponentPair (j, dp)).1 =
                smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1 +
                  smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1 := by
            simp [smallKIntegratedExponentPair]
            omega
          rw [← hpair]
          exact smallK_scaled_face_pair_term i j cp dp
        · simp [smallKIntegratedIntegerCoefficient,
            smallKIntegratedRationalCoefficient, hdpC]
      · simp [smallKIntegratedIntegerCoefficient,
          smallKIntegratedRationalCoefficient, hcpC]
    _ = ∑ i : Fin 42, ∑ cp : Fin 6, ∑ j : Fin 42, ∑ dp : Fin 6,
        (105 : ℚ) / (smallKFaceScale : ℚ) ^ 2 *
          (smallKIntegratedIntegerCoefficient i cp : ℚ) *
          (smallKIntegratedIntegerCoefficient j dp : ℚ) *
            smallKSimplexMoment104
              (smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1 +
                smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1)
              (cp.1 + dp.1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ tu : (Fin 42 × Fin 6) × (Fin 42 × Fin 6),
        (105 : ℚ) / (smallKFaceScale : ℚ) ^ 2 *
          (smallKIntegratedIntegerCoefficient tu.1.1 tu.1.2 : ℚ) *
          (smallKIntegratedIntegerCoefficient tu.2.1 tu.2.2 : ℚ) *
            smallKSimplexMoment104
              (smallKIntegratedPairExponentSum tu).1
              (smallKIntegratedPairExponentSum tu).2 := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro cp hcp
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro dp hdp
      by_cases hcpC : cp.1 ≤ smallKExponentC i
      · by_cases hdpC : dp.1 ≤ smallKExponentC j
        · simp only [smallKIntegratedPairExponentSum, smallKIntegratedExponentPair]
          have hci : 2 * cp.1 ≤ smallKExponentB i + 2 * smallKExponentC i := by
            omega
          have hcj : 2 * dp.1 ≤ smallKExponentB j + 2 * smallKExponentC j := by
            omega
          have hpair :
              smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1 +
                  smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1 =
                (smallKExponentB i + 2 * smallKExponentC i - 2 * cp.1 + 1) +
                  (smallKExponentB j + 2 * smallKExponentC j - 2 * dp.1 + 1) := by
            omega
          rw [hpair]
        · simp [smallKIntegratedIntegerCoefficient, hdpC]
      · simp [smallKIntegratedIntegerCoefficient, hcpC]

set_option maxRecDepth 100000 in
theorem smallK_groupedIntegratedIntegerCoefficient_cast (p : ℕ × ℕ) :
    (smallKGroupedIntegratedIntegerCoefficient p : ℚ) =
      ∑ tu ∈ Finset.univ.filter
        (fun tu : (Fin 42 × Fin 6) × (Fin 42 × Fin 6) =>
          smallKIntegratedPairExponentSum tu = p),
        (smallKIntegratedIntegerCoefficient tu.1.1 tu.1.2 : ℚ) *
          (smallKIntegratedIntegerCoefficient tu.2.1 tu.2.2 : ℚ) := by
  classical
  unfold smallKGroupedIntegratedIntegerCoefficient
  push_cast
  apply Finset.sum_congr rfl
  intro tu htu
  norm_num

set_option maxRecDepth 100000 in
theorem smallK_numerator_eq_grouped :
    smallKNumerator = smallKGroupedNumerator := by
  classical
  rw [smallK_numerator_eq_scaled_pair_sum]
  unfold smallKGroupedNumerator smallKGroupedNumeratorCoefficient
  simp_rw [smallK_groupedIntegratedIntegerCoefficient_cast]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ)
    (t := smallKIntegratedPairExponentSums)
    (g := smallKIntegratedPairExponentSum)]
  · apply Finset.sum_congr rfl
    intro p hp
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro tu htu
    have hpair := (Finset.mem_filter.mp htu).2
    rw [hpair]
    ring
  · intro tu htu
    exact Finset.mem_image_of_mem _ htu

end BoundedGaps.Maynard
