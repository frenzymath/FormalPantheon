import BoundedGaps.Maynard.AugmentedPreSievedPrimeMertens

noncomputable section

/-!
# Prime-log mass of a squarefree varying modulus

The extra modulus in the S2 coordinate fiber is squarefree.  Splitting its
prime divisors at a positive threshold bounds the small primes by the ordinary
prime Mertens sum and the large primes by `log(P) / T`.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real

theorem primeLogDivisorMass_le_primeLogHarmonicSum_add
    {P T : ℕ} (hPsq : Squarefree P) (hT : 0 < T) :
    primeLogDivisorMass P ≤
      primeLogHarmonicSum T + Real.log P / T := by
  classical
  let low := P.primeFactors.filter (fun p => p ≤ T)
  let high := P.primeFactors.filter (fun p => ¬p ≤ T)
  let f : ℕ → ℝ := fun p => Real.log p / (p : ℝ)
  have hsplit :
      (∑ p ∈ low, f p) + ∑ p ∈ high, f p =
        ∑ p ∈ P.primeFactors, f p := by
    exact Finset.sum_filter_add_sum_filter_not P.primeFactors
      (fun p => p ≤ T) f
  have hlow : (∑ p ∈ low, f p) ≤ primeLogHarmonicSum T := by
    unfold primeLogHarmonicSum
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hpData := Finset.mem_filter.mp hp
      have hpPrime := (Nat.mem_primeFactors.mp hpData.1).1
      exact Nat.mem_primesLE.mpr ⟨hpData.2, hpPrime⟩
    · intro p hpT hpNot
      positivity
  have hhighPoint : ∀ p ∈ high, f p ≤ Real.log p / T := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpPrime := (Nat.mem_primeFactors.mp hpData.1).1
    have hTp : T ≤ p := by omega
    exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg p)
      (by exact_mod_cast hT) (by exact_mod_cast hTp)
  have hhighSubset : high ⊆ P.primeFactors := Finset.filter_subset _ _
  have hlogsum :
      (∑ p ∈ P.primeFactors, Real.log p) = Real.log P := by
    have hprodNat := Nat.prod_primeFactors_of_squarefree hPsq
    have hprodReal : (∏ p ∈ P.primeFactors, (p : ℝ)) = (P : ℝ) := by
      rw [← Nat.cast_prod]
      exact congrArg (fun n : ℕ => (n : ℝ)) hprodNat
    calc
      (∑ p ∈ P.primeFactors, Real.log p) =
          Real.log (∏ p ∈ P.primeFactors, (p : ℝ)) := by
        exact (Real.log_prod (fun p hp => by
          have hpPrime := (Nat.mem_primeFactors.mp hp).1
          exact_mod_cast hpPrime.ne_zero)).symm
      _ = Real.log P := congrArg Real.log hprodReal
  have hhigh : (∑ p ∈ high, f p) ≤ Real.log P / T := by
    calc
      (∑ p ∈ high, f p) ≤
          ∑ p ∈ high, Real.log p / T := by
        exact Finset.sum_le_sum hhighPoint
      _ ≤ ∑ p ∈ P.primeFactors, Real.log p / T := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hhighSubset
        intro p hpP hpNot
        positivity
      _ = Real.log P / T := by
        rw [← Finset.sum_div, hlogsum]
  unfold primeLogDivisorMass
  change (∑ p ∈ P.primeFactors, f p) ≤ _
  rw [← hsplit]
  exact add_le_add hlow hhigh

theorem exists_uniform_primeLogDivisorMass_bound :
    ∃ C : ℝ, ∀ {P T : ℕ}, Squarefree P → 0 < T →
      primeLogDivisorMass P ≤
        Real.log T + C + Real.log P / T := by
  obtain ⟨C, hC⟩ := exists_uniform_abs_primeLogHarmonicSum_sub_log
  refine ⟨C, fun {P T} hPsq hT => ?_⟩
  have hbase := primeLogDivisorMass_le_primeLogHarmonicSum_add hPsq hT
  have hprime := (abs_le.mp (hC T)).2
  linarith

theorem exists_uniform_augmentedPreSievedPrimeLogInterval_rough_bounds :
    ∃ K C : ℝ, 0 < K ∧
      ∀ {D P T w z : ℕ}, 0 < P → Squarefree P → 0 < T →
        2 ≤ w → w ≤ z →
        -(K + Real.log D +
            (Real.log T + C + Real.log P / T)) ≤
          augmentedPreSievedPrimeLogIntervalSum D P w z -
            Real.log ((z : ℝ) / (w : ℝ)) ∧
        augmentedPreSievedPrimeLogIntervalSum D P w z -
            Real.log ((z : ℝ) / (w : ℝ)) ≤ K := by
  obtain ⟨K, hK, hinterval⟩ :=
    exists_uniform_augmentedPreSievedPrimeLogInterval_bounds
  obtain ⟨C, hmass⟩ := exists_uniform_primeLogDivisorMass_bound
  refine ⟨K, C, hK, fun {D P T w z} hP hPsq hT hw hwz => ?_⟩
  have hbounds := hinterval (D := D) (P := P) hP hw hwz
  have hmassBound := hmass (P := P) (T := T) hPsq hT
  constructor
  · linarith [hbounds.1]
  · exact hbounds.2

end BoundedGaps.Maynard
