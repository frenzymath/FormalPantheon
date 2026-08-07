import BoundedGaps.Maynard.MaynardS2MainFactorDeviation

noncomputable section

/-!
# Fixed-divisor rough quotient tails

Squarefree pre-sieved multiples of a fixed divisor are reindexed by their
rough quotient. This supplies the scalar tail used in Maynard2013v3, source
lines 431--434.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable def preSievedFixedDivisorTotientSquareSupport
    (D r Q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 Q).filter fun a =>
    Squarefree a ∧ Nat.Coprime a (primorial D) ∧ r ∣ a

noncomputable def preSievedFixedDivisorStrictTotientSquareSum
    (D r Q : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ (preSievedFixedDivisorTotientSquareSupport D r Q).erase r,
    (1 : ℝ) / (Nat.totient a : ℝ) ^ 2

noncomputable def preSievedFixedDivisorTotientSquareSum
    (D r Q : ℕ) : ℝ := by
  classical
  exact ∑ a ∈ preSievedFixedDivisorTotientSquareSupport D r Q,
    (1 : ℝ) / (Nat.totient a : ℝ) ^ 2

theorem preSievedFixedDivisorStrictTotientSquareSum_le_roughTail
    {D r Q : ℕ} (hr : 0 < r) :
    preSievedFixedDivisorStrictTotientSquareSum D r Q ≤
      ((1 : ℝ) / (Nat.totient r : ℝ) ^ 2) *
        squarefreeRoughTotientSquareTail D Q := by
  classical
  let S := (preSievedFixedDivisorTotientSquareSupport D r Q).erase r
  let T := squarefreeRoughSupport D Q
  let quotient : ℕ → ℕ := fun a => a / r
  let fixedWeight : ℝ := (1 : ℝ) / (Nat.totient r : ℝ) ^ 2
  let quotientWeight : ℕ → ℝ := fun b =>
    (1 : ℝ) / (Nat.totient b : ℝ) ^ 2
  have hinj : Set.InjOn quotient S := by
    intro a ha b hb hab
    have haData := Finset.mem_filter.mp
      (Finset.mem_of_mem_erase ha)
    have hbData := Finset.mem_filter.mp
      (Finset.mem_of_mem_erase hb)
    have hab' : a / r = b / r := by simpa [quotient] using hab
    calc
      a = r * (a / r) := (Nat.mul_div_cancel' haData.2.2.2).symm
      _ = r * (b / r) := by rw [hab']
      _ = b := Nat.mul_div_cancel' hbData.2.2.2
  have himage : S.image quotient ⊆ T := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    have haErase := Finset.mem_erase.mp ha
    have haData := Finset.mem_filter.mp haErase.2
    have haBounds := Finset.mem_Icc.mp haData.1
    have haSq := haData.2.1
    have haCop := haData.2.2.1
    have hra := haData.2.2.2
    have haPos : 0 < a := zero_lt_one.trans_le haBounds.1
    have hrLe : r ≤ a := Nat.le_of_dvd haPos hra
    have hqPos : 0 < a / r := Nat.div_pos hrLe hr
    have hqNe : a / r ≠ 1 := by
      intro hq
      have hraEq : r = a := Nat.eq_of_dvd_of_div_eq_one hra hq
      exact haErase.1 hraEq.symm
    have hqTwo : 2 ≤ a / r := by omega
    have hqLe : a / r ≤ Q := (Nat.div_le_self a r).trans haBounds.2
    have hqDvdA : a / r ∣ a := Nat.div_dvd_of_dvd hra
    have hqSq : Squarefree (a / r) := haSq.squarefree_of_dvd hqDvdA
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hqTwo, hqLe⟩, hqSq, ?_⟩
    intro p hpMem
    have hp := Nat.prime_of_mem_primeFactors hpMem
    have hpDvdQ : p ∣ a / r := Nat.dvd_of_mem_primeFactors hpMem
    have hpDvdA : p ∣ a := dvd_trans hpDvdQ hqDvdA
    have hpGt : D < p :=
      prime_gt_of_dvd_coprime_primorial hp hpDvdA haCop
    have hpLeQ : p ≤ Q :=
      (Nat.le_of_dvd hqPos hpDvdQ).trans hqLe
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨by omega, hpLeQ⟩, hp⟩
  have hweight {a : ℕ} (ha : a ∈ S) :
      (1 : ℝ) / (Nat.totient a : ℝ) ^ 2 =
        fixedWeight * quotientWeight (quotient a) := by
    have haData := Finset.mem_filter.mp
      (Finset.mem_of_mem_erase ha)
    have hra := haData.2.2.2
    have hmul : r * (a / r) = a := Nat.mul_div_cancel' hra
    have hcopRQ : Nat.Coprime r (a / r) := by
      apply Nat.coprime_of_squarefree_mul
      simpa only [hmul] using haData.2.1
    have hphi := Nat.totient_mul hcopRQ
    have hphiA : Nat.totient a =
        Nat.totient r * Nat.totient (a / r) := by
      calc
        Nat.totient a = Nat.totient (r * (a / r)) :=
          congrArg Nat.totient hmul.symm
        _ = Nat.totient r * Nat.totient (a / r) := hphi
    have hqPos : 0 < a / r := by
      have haPos : 0 < a := zero_lt_one.trans_le
        (Finset.mem_Icc.mp haData.1).1
      exact Nat.div_pos (Nat.le_of_dvd haPos hra) hr
    have hphiR : (Nat.totient r : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hr))
    have hphiQ : (Nat.totient (a / r) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hqPos))
    unfold fixedWeight quotientWeight quotient
    rw [hphiA]
    push_cast
    field_simp [hphiR, hphiQ]
  unfold preSievedFixedDivisorStrictTotientSquareSum
  change (∑ a ∈ S, (1 : ℝ) / (Nat.totient a : ℝ) ^ 2) ≤ _
  calc
    (∑ a ∈ S, (1 : ℝ) / (Nat.totient a : ℝ) ^ 2) =
        ∑ a ∈ S, fixedWeight * quotientWeight (quotient a) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hweight ha
    _ = ∑ b ∈ S.image quotient, fixedWeight * quotientWeight b := by
      exact (Finset.sum_image
        (f := fun b => fixedWeight * quotientWeight b) hinj).symm
    _ ≤ ∑ b ∈ T, fixedWeight * quotientWeight b := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro b hb hbNot
      unfold fixedWeight quotientWeight
      positivity
    _ = fixedWeight * squarefreeRoughTotientSquareTail D Q := by
      unfold T squarefreeRoughTotientSquareTail
      rw [Finset.mul_sum]
    _ = ((1 : ℝ) / (Nat.totient r : ℝ) ^ 2) *
        squarefreeRoughTotientSquareTail D Q := by rfl

theorem preSievedFixedDivisorStrictTotientSquareSum_le
    {D r Q : ℕ} (hD : 0 < D) (hr : 0 < r) :
    preSievedFixedDivisorStrictTotientSquareSum D r Q ≤
      ((1 : ℝ) / (Nat.totient r : ℝ) ^ 2) *
        (8 * Real.exp 8 / (D : ℝ)) := by
  calc
    preSievedFixedDivisorStrictTotientSquareSum D r Q ≤
        ((1 : ℝ) / (Nat.totient r : ℝ) ^ 2) *
          squarefreeRoughTotientSquareTail D Q :=
      preSievedFixedDivisorStrictTotientSquareSum_le_roughTail hr
    _ ≤ ((1 : ℝ) / (Nat.totient r : ℝ) ^ 2) *
          (8 * Real.exp 8 / (D : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (squarefreeRoughTotientSquareTail_le hD) (by positivity)

theorem preSievedFixedDivisorTotientSquareSum_le_diag_add_strict
    (D r Q : ℕ) :
    preSievedFixedDivisorTotientSquareSum D r Q ≤
      (1 : ℝ) / (Nat.totient r : ℝ) ^ 2 +
        preSievedFixedDivisorStrictTotientSquareSum D r Q := by
  classical
  unfold preSievedFixedDivisorTotientSquareSum
    preSievedFixedDivisorStrictTotientSquareSum
  by_cases hrMem : r ∈ preSievedFixedDivisorTotientSquareSupport D r Q
  · have hsum := Finset.sum_erase_add
      (s := preSievedFixedDivisorTotientSquareSupport D r Q)
      (f := fun a => (1 : ℝ) / (Nat.totient a : ℝ) ^ 2) hrMem
    linarith
  · rw [Finset.erase_eq_self.mpr hrMem]
    exact le_add_of_nonneg_left (by positivity)

theorem preSievedFixedDivisorTotientSquareSum_le
    {D r Q : ℕ} (hD : 0 < D) (hr : 0 < r) :
    preSievedFixedDivisorTotientSquareSum D r Q ≤
      ((1 : ℝ) / (Nat.totient r : ℝ) ^ 2) *
        (1 + 8 * Real.exp 8 / (D : ℝ)) := by
  calc
    preSievedFixedDivisorTotientSquareSum D r Q ≤
        (1 : ℝ) / (Nat.totient r : ℝ) ^ 2 +
          preSievedFixedDivisorStrictTotientSquareSum D r Q :=
      preSievedFixedDivisorTotientSquareSum_le_diag_add_strict D r Q
    _ ≤ (1 : ℝ) / (Nat.totient r : ℝ) ^ 2 +
          ((1 : ℝ) / (Nat.totient r : ℝ) ^ 2) *
            (8 * Real.exp 8 / (D : ℝ)) := by
      simpa [add_comm] using
        add_le_add_left
          (preSievedFixedDivisorStrictTotientSquareSum_le
            (Q := Q) hD hr)
          ((1 : ℝ) / (Nat.totient r : ℝ) ^ 2)
    _ = ((1 : ℝ) / (Nat.totient r : ℝ) ^ 2) *
          (1 + 8 * Real.exp 8 / (D : ℝ)) := by ring

end BoundedGaps.Maynard
