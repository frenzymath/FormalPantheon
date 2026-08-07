import BoundedGaps.Maynard.ImprovedGPY.Mobius
import BoundedGaps.Maynard.IntervalDistribution

noncomputable section

/-!
# Exact prime-weighted pair expansion

Maynard2013v3, Section 5, defines `S₂` as the square sieve weight multiplied
by the number of prime shifts (source lines 205--216). This file records the
finite pair expansion and its compatible-pair restriction before any prime
progression estimate or Bombieri--Vinogradov input.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def primeWeightedPairInnerSum
    (H : Finset ℕ) (v W N : ℕ) (lambda : (H → ℕ) → ℝ)
    (d e : H → ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico N (2 * N),
    ∑ h ∈ H,
      if n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e ∧
          (n + h).Prime
      then lambda d * lambda e else 0

def compatiblePrimeWeightedPairSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (v W N : ℕ) (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D.filter (fun e => IsCrossCoordinateCoprime H d e),
    primeWeightedPairInnerSum H v W N lambda d e

def shiftedPrimeProgressionCount (N q a h : ℕ) : ℕ :=
  ((Finset.Ico N (2 * N)).filter (fun n =>
    n ≡ a [MOD q] ∧ (n + h).Prime)).card

def primeVariableProgressionCount (A B q r : ℕ) : ℕ :=
  ((Finset.Ico A B).filter (fun m => m.Prime ∧ m ≡ r [MOD q])).card

theorem primeWeightedSieveSum_preSieved_eq_pairPrimeIndicator
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (N v W : ℕ) :
    primeWeightedSieveSum H N
        (preSievedSquareDivisorWeight H D lambda v W) =
      ∑ d ∈ D, ∑ e ∈ D,
        primeWeightedPairInnerSum H v W N lambda d e := by
  classical
  unfold primeWeightedSieveSum
  simp_rw [primeShiftCount_eq_prime_indicator_sum]
  simp_rw [preSievedSquareDivisorWeight_eq_pair_indicator]
  unfold primeWeightedPairInnerSum
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hp : (n + h).Prime <;>
    by_cases hcond : n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e <;>
      simp [hp, hcond]

theorem primeWeightedSieveSum_preSieved_eq_compatiblePrimeWeightedPairSum
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {N v W R : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W) :
    primeWeightedSieveSum H N
        (preSievedSquareDivisorWeight H D lambda v W) =
      compatiblePrimeWeightedPairSum H D v W N lambda := by
  classical
  rw [primeWeightedSieveSum_preSieved_eq_pairPrimeIndicator]
  unfold compatiblePrimeWeightedPairSum
  apply Finset.sum_congr rfl
  intro d hd_mem
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he_mem
  by_cases hcross : IsCrossCoordinateCoprime H d e
  · simp [hcross]
  · have hd := hD d hd_mem
    have he := hD e he_mem
    have hinner : primeWeightedPairInnerSum H v W N lambda d e = 0 := by
      unfold primeWeightedPairInnerSum
      apply Finset.sum_eq_zero
      intro n hn
      apply Finset.sum_eq_zero
      intro h hh
      have hfalse :
          ¬(n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e) := by
        intro hcond
        exact hcross (isCrossCoordinateCoprime_of_pairCondition hd he
          hcoverage hcond.2)
      have hfalse' :
          ¬(n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e ∧
            (n + h).Prime) := by
        intro hcond
        exact hfalse ⟨hcond.1, hcond.2.1⟩
      simp [hfalse']
    simp [hcross, hinner]

theorem primeWeightedPairInnerSum_eq_shiftedPrimeProgressionCounts
    {H : Finset ℕ} {R W v N : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e)
    (lambda : (H → ℕ) → ℝ) :
    primeWeightedPairInnerSum H v W N lambda d e =
      ∑ h ∈ H,
        (shiftedPrimeProgressionCount N (divisorPairModulus H W d e)
          (divisorPairCrtResidue H R W v d e hd he hcross) h : ℝ) *
          (lambda d * lambda e) := by
  classical
  unfold primeWeightedPairInnerSum shiftedPrimeProgressionCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Finset.sum_filter]
  have hpred (n : ℕ) :
      (n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e ∧
          (n + h).Prime) ↔
        (n ≡ divisorPairCrtResidue H R W v d e hd he hcross
          [MOD divisorPairModulus H W d e] ∧ (n + h).Prime) := by
    constructor
    · rintro ⟨hres, hpair, hprime⟩
      exact ⟨(modEq_divisorPairCrtResidue_iff hd he hcross n).mpr
          ⟨hres, hpair⟩, hprime⟩
    · rintro ⟨hmod, hprime⟩
      obtain ⟨hres, hpair⟩ :=
        (modEq_divisorPairCrtResidue_iff hd he hcross n).mp hmod
      exact ⟨hres, hpair, hprime⟩
  have hfilter :
      (Finset.Ico N (2 * N)).filter (fun n =>
        n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e ∧
          (n + h).Prime) =
      (Finset.Ico N (2 * N)).filter (fun n =>
        n ≡ divisorPairCrtResidue H R W v d e hd he hcross
          [MOD divisorPairModulus H W d e] ∧ (n + h).Prime) := by
    ext n
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hn, hp⟩
      exact ⟨hn, (hpred n).mp hp⟩
    · rintro ⟨hn, hp⟩
      exact ⟨hn, (hpred n).mpr hp⟩
  rw [hfilter]
  rw [Finset.sum_const]
  simp [nsmul_eq_mul]

theorem shiftedPrimeProgressionCount_eq_primeVariableProgressionCount
    (N q a h : ℕ) :
    shiftedPrimeProgressionCount N q a h =
      primeVariableProgressionCount (N + h) (2 * N + h) q (a + h) := by
  unfold shiftedPrimeProgressionCount primeVariableProgressionCount
  apply Finset.card_bij (fun n hn => n + h)
  · intro n hn
    have hnI := Finset.mem_filter.mp hn
    have hnrange := Finset.mem_Ico.mp hnI.1
    have hprime := hnI.2.2
    have hmod := hnI.2.1
    apply Finset.mem_filter.mpr
    refine ⟨?_, hprime, ?_⟩
    · simp only [Finset.mem_Ico]
      omega
    · exact hmod.add_right h
  · intro n₁ hn₁ n₂ hn₂ heq
    omega
  · intro m hm
    have hmI := Finset.mem_filter.mp hm
    have hmrange := Finset.mem_Ico.mp hmI.1
    let n := m - h
    have hnrange : n ∈ Finset.Ico N (2 * N) := by
      simp only [Finset.mem_Ico]
      dsimp [n]
      omega
    have hnadd : n + h = m := by
      dsimp [n]
      omega
    have hnmod : n ≡ a [MOD q] := by
      apply Nat.ModEq.add_right_cancel' h
      simpa [hnadd] using hmI.2.2
    refine ⟨n, Finset.mem_filter.mpr ⟨hnrange, hnmod, ?_⟩, ?_⟩
    · simpa [hnadd] using hmI.2.1
    · exact hnadd

theorem cast_primeVariableProgressionCount
    (A B q r : ℕ) (hA : 0 < A) (hAB : A ≤ B) :
    (primeVariableProgressionCount A B q r : ℝ) =
      (primeCountUpTo (B - 1) q r : ℝ) -
        (primeCountUpTo (A - 1) q r : ℝ) := by
  unfold primeVariableProgressionCount primeCountUpTo
  simp only [Nat.ModEq]
  rw [Finset.natCast_card_filter, Finset.natCast_card_filter,
    Finset.natCast_card_filter]
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  have hAeq : A - 1 + 1 = A :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hA.ne')
  have hBeq : B - 1 + 1 = B :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hB.ne')
  simpa [hAeq, hBeq] using Finset.sum_Ico_eq_sub
    (f := fun n : ℕ => if n.Prime ∧ n % q = r % q then (1 : ℝ) else 0) hAB

theorem primeVariableProgressionCount_intervalDiscrepancy_le_global_sum
    {A B q r : ℕ} (hA : 0 < A) (hAB : A ≤ B) :
    |(primeVariableProgressionCount A B q r : ℝ) -
        ((primeCountTotal (B - 1) : ℝ) -
          (primeCountTotal (A - 1) : ℝ)) / (Nat.totient q : ℝ)| ≤
      progressionDiscrepancy (B - 1) q r +
        progressionDiscrepancy (A - 1) q r := by
  rw [cast_primeVariableProgressionCount A B q r hA hAB]
  let X : ℝ := (primeCountUpTo (B - 1) q r : ℝ) -
    (primeCountTotal (B - 1) : ℝ) / (Nat.totient q : ℝ)
  let Y : ℝ := (primeCountUpTo (A - 1) q r : ℝ) -
    (primeCountTotal (A - 1) : ℝ) / (Nat.totient q : ℝ)
  have hrearrange :
      ((primeCountUpTo (B - 1) q r : ℝ) -
          (primeCountUpTo (A - 1) q r : ℝ)) -
          ((primeCountTotal (B - 1) : ℝ) -
            (primeCountTotal (A - 1) : ℝ)) /
              (Nat.totient q : ℝ) = X - Y := by
    dsimp [X, Y]
    ring
  rw [hrearrange]
  change |X - Y| ≤ |X| + |Y|
  calc
    |X - Y| ≤ |X - 0| + |0 - Y| := abs_sub_le X 0 Y
    _ = |X| + |Y| := by simp only [sub_zero, zero_sub, abs_neg]

def shiftedPrimeProgressionIntervalDiscrepancy
    (N q a h : ℕ) : ℝ :=
  |(shiftedPrimeProgressionCount N q a h : ℝ) -
    ((primeCountTotal (2 * N + h - 1) : ℝ) -
      (primeCountTotal (N + h - 1) : ℝ)) / (Nat.totient q : ℝ)|

theorem shiftedPrimeProgressionIntervalDiscrepancy_le_global_sum
    {N q a h : ℕ} (hN : 0 < N) :
    shiftedPrimeProgressionIntervalDiscrepancy N q a h ≤
      progressionDiscrepancy (2 * N + h - 1) q (a + h) +
        progressionDiscrepancy (N + h - 1) q (a + h) := by
  unfold shiftedPrimeProgressionIntervalDiscrepancy
  rw [shiftedPrimeProgressionCount_eq_primeVariableProgressionCount]
  exact primeVariableProgressionCount_intervalDiscrepancy_le_global_sum
    (by omega) (by omega)

theorem shiftedPrimeProgressionIntervalDiscrepancy_le_global_max
    {N q a h : ℕ} (hN : 0 < N) (hq : 0 < q)
    (ha : (a + h) % q ∈ coprimeResidues q) :
    shiftedPrimeProgressionIntervalDiscrepancy N q a h ≤
      maxProgressionDiscrepancy (2 * N + h - 1) q +
        maxProgressionDiscrepancy (N + h - 1) q := by
  have hreduce (x : ℕ) : progressionDiscrepancy x q (a + h) =
      progressionDiscrepancy x q ((a + h) % q) := by
    unfold progressionDiscrepancy primeCountUpTo
    simp only [Nat.mod_mod]
  calc
    shiftedPrimeProgressionIntervalDiscrepancy N q a h ≤
        progressionDiscrepancy (2 * N + h - 1) q (a + h) +
          progressionDiscrepancy (N + h - 1) q (a + h) :=
      shiftedPrimeProgressionIntervalDiscrepancy_le_global_sum hN
    _ = progressionDiscrepancy (2 * N + h - 1) q ((a + h) % q) +
          progressionDiscrepancy (N + h - 1) q ((a + h) % q) := by
      rw [hreduce, hreduce]
    _ ≤ maxProgressionDiscrepancy (2 * N + h - 1) q +
          maxProgressionDiscrepancy (N + h - 1) q :=
      add_le_add (progressionDiscrepancy_le_max hq ha)
        (progressionDiscrepancy_le_max hq ha)

def shiftedPrimeProgressionIntervalMainTerm
    (N q _a h : ℕ) : ℝ :=
  ((primeCountTotal (2 * N + h - 1) : ℝ) -
      (primeCountTotal (N + h - 1) : ℝ)) / (Nat.totient q : ℝ)

def shiftedPrimeProgressionIntervalError
    (N q a h : ℕ) : ℝ :=
  (shiftedPrimeProgressionCount N q a h : ℝ) -
    shiftedPrimeProgressionIntervalMainTerm N q a h

theorem shiftedPrimeProgressionCount_interval_decomposition
    (N q a h : ℕ) :
    (shiftedPrimeProgressionCount N q a h : ℝ) =
      shiftedPrimeProgressionIntervalMainTerm N q a h +
        shiftedPrimeProgressionIntervalError N q a h := by
  unfold shiftedPrimeProgressionIntervalError
  ring

theorem abs_shiftedPrimeProgressionIntervalError_le_global_max
    {N q a h : ℕ} (hN : 0 < N) (hq : 0 < q)
    (ha : (a + h) % q ∈ coprimeResidues q) :
    |shiftedPrimeProgressionIntervalError N q a h| ≤
      maxProgressionDiscrepancy (2 * N + h - 1) q +
        maxProgressionDiscrepancy (N + h - 1) q := by
  exact shiftedPrimeProgressionIntervalDiscrepancy_le_global_max hN hq ha

end BoundedGaps.Maynard
