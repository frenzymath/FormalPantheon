import BoundedGaps.Maynard.MaynardS1CrossPrime
import BoundedGaps.Maynard.MaynardS1CrossTupleTail

noncomputable section

/-!
# Rough support of nonzero starred Y cross terms

A nonzero lower Y factor transfers squarefreeness and primorial coprimality
to every cross divisor.  Thus the starred auxiliary sum may be restricted to
the rough cross box used by the tuple tail estimate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance starredRoughDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem squarefreeRoughUnitSupport_subset_Icc
    {D Q : ℕ} (hQ : 0 < Q) :
    squarefreeRoughUnitSupport D Q ⊆ Finset.Icc 1 Q := by
  intro n hn
  rw [squarefreeRoughUnitSupport, Finset.mem_insert] at hn
  rcases hn with rfl | hn
  · exact Finset.mem_Icc.mpr ⟨le_rfl, hQ⟩
  · have hbounds := Finset.mem_Icc.mp
      (Finset.mem_filter.mp hn).1
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_of_lt hbounds.1, hbounds.2⟩

theorem roughCrossTupleSupport_subset_crossMoebiusTupleBox
    {H : Finset ℕ} {D R : ℕ} (hR : 0 < R) :
    roughCrossTupleSupport H D R ⊆ crossMoebiusTupleBox H R := by
  intro s hs
  rw [roughCrossTupleSupport, Finset.mem_pi] at hs
  rw [crossMoebiusTupleBox, Finset.mem_pi]
  intro ab hab
  exact squarefreeRoughUnitSupport_subset_Icc hR (hs ab hab)

theorem roughCrossCoordinate_of_leftYFactor_ne_zero
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R (primorial D) y)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hs : s ∈ crossMoebiusTupleBox H R)
    (hl : leftCrossYFactor H y u s ≠ 0)
    (ab : H × H) (hab : ab ∈ offDiagonalPairs H) :
    s ab hab ∈ squarefreeRoughUnitSupport D R := by
  have hlSupport := hy _ (leftCrossYFactor_ne_zero_y_ne_zero hl)
  have hsMem := (Finset.mem_pi.mp hs) ab hab
  have hsBounds := Finset.mem_Icc.mp hsMem
  let n := s ab hab
  have hnDvd : n ∣ leftCrossLowerTuple H u s ab.1 :=
    cross_dvd_leftCrossLowerTuple u s ab hab
  have hnSquarefree : Squarefree n :=
    (hlSupport.coordinate_squarefree ab.1).squarefree_of_dvd hnDvd
  have hnCoprime : Nat.Coprime n (primorial D) :=
    Nat.Coprime.of_dvd_left hnDvd
      (hlSupport.coordinate_coprime_W ab.1)
  rw [squarefreeRoughUnitSupport, Finset.mem_insert]
  by_cases hnOne : n = 1
  · exact Or.inl hnOne
  · apply Or.inr
    rw [squarefreeRoughSupport, Finset.mem_filter]
    refine ⟨Finset.mem_Icc.mpr ⟨?_, hsBounds.2⟩,
      hnSquarefree, ?_⟩
    · have hnPos : 0 < n := hsBounds.1
      omega
    · intro p hpMem
      have hpPrime := Nat.prime_of_mem_primeFactors hpMem
      have hpDvd := Nat.dvd_of_mem_primeFactors hpMem
      have hpGt : D < p :=
        prime_gt_of_dvd_coprime_primorial hpPrime hpDvd hnCoprime
      have hpLeN : p ≤ n := Nat.le_of_dvd hsBounds.1 hpDvd
      rw [roughPrimeSupport, Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, hpLeN.trans hsBounds.2⟩,
        hpPrime⟩

theorem roughCrossTupleSupport_of_leftYFactor_ne_zero
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R (primorial D) y)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hs : s ∈ crossMoebiusTupleBox H R)
    (hl : leftCrossYFactor H y u s ≠ 0) :
    s ∈ roughCrossTupleSupport H D R := by
  rw [roughCrossTupleSupport, Finset.mem_pi]
  intro ab hab
  exact roughCrossCoordinate_of_leftYFactor_ne_zero
    hy hs hl ab hab

def nontrivialStarredRoughAuxiliaryYSum
    (H : Finset ℕ) (R D : ℕ) (y : (H → ℕ) → ℝ) : ℝ :=
  ∑ s ∈ roughCrossTupleSupport H D R,
    if s ≠ oneCrossMoebiusTuple H then
      crossMoebiusTupleTerm H s *
        ∑ u ∈ maynardDivisorTupleBox H R,
          if IsStarredCrossTuple H u s then
            (∏ h : H, (Nat.totient (u h) : ℝ)) *
              leftCrossYFactor H y u s * rightCrossYFactor H y u s
          else 0
    else 0

theorem nontrivialStarredAuxiliaryYSum_eq_rough
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (hR : 0 < R)
    (hy : IsSupportedMaynardY H R (primorial D) y) :
    nontrivialStarredAuxiliaryYSum H R y =
      nontrivialStarredRoughAuxiliaryYSum H R D y := by
  classical
  unfold nontrivialStarredAuxiliaryYSum
    nontrivialStarredRoughAuxiliaryYSum
  apply (Finset.sum_subset
    (roughCrossTupleSupport_subset_crossMoebiusTupleBox hR) ?_).symm
  intro s hsBox hsNotRough
  by_cases hsNe : s ≠ oneCrossMoebiusTuple H
  · rw [if_pos hsNe]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro u hu
    by_cases hstar : IsStarredCrossTuple H u s
    · rw [if_pos hstar]
      have hl : leftCrossYFactor H y u s = 0 := by
        by_contra hl
        exact hsNotRough
          (roughCrossTupleSupport_of_leftYFactor_ne_zero hy hsBox hl)
      simp [hl]
    · rw [if_neg hstar]
  · rw [if_neg hsNe]

end BoundedGaps.Maynard
