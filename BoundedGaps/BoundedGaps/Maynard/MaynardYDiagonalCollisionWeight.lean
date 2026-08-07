import BoundedGaps.Maynard.MaynardYDiagonalCollisionBox

noncomputable section

namespace BoundedGaps.Maynard

open Set
open scoped BigOperators

/-! Remove the bounded quadratic test function from the collision estimate. -/

theorem abs_simplexQuadraticIntegrand_le_one
    {k b c : ℕ} {t : Fin k → ℝ} (ht : t ∈ maynardSimplex k) :
    |simplexQuadraticIntegrand k b c t| ≤ 1 := by
  have hcoord : ∀ i : Fin k, t i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    simpa [maynardSimplex, maynardCube, maynardCubeOf] using
      ht.1 i (Set.mem_univ i)
  have hsumNonneg : 0 ≤ ∑ i, t i :=
    Finset.sum_nonneg fun i hi => (hcoord i).1
  have hslackNonneg : 0 ≤ 1 - ∑ i, t i := sub_nonneg.mpr ht.2
  have hslackLe : 1 - ∑ i, t i ≤ 1 := by linarith
  have hsqNonneg : 0 ≤ ∑ i, (t i) ^ 2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg (t i)
  have hsqLeSum : (∑ i, (t i) ^ 2) ≤ ∑ i, t i := by
    apply Finset.sum_le_sum
    intro i hi
    have hiData := hcoord i
    nlinarith [mul_nonneg hiData.1 (sub_nonneg.mpr hiData.2)]
  have hsqLe : (∑ i, (t i) ^ 2) ≤ 1 := hsqLeSum.trans ht.2
  have hslackPowNonneg : 0 ≤ (1 - ∑ i, t i) ^ b :=
    pow_nonneg hslackNonneg b
  have hsqPowNonneg : 0 ≤ (∑ i, (t i) ^ 2) ^ c :=
    pow_nonneg hsqNonneg c
  have hslackPowLe : (1 - ∑ i, t i) ^ b ≤ 1 :=
    pow_le_one₀ hslackNonneg hslackLe
  have hsqPowLe : (∑ i, (t i) ^ 2) ^ c ≤ 1 :=
    pow_le_one₀ hsqNonneg hsqLe
  unfold simplexQuadraticIntegrand
  rw [abs_of_nonneg (mul_nonneg hslackPowNonneg hsqPowNonneg)]
  nlinarith [mul_nonneg hslackPowNonneg hsqPowNonneg,
    mul_nonneg (sub_nonneg.mpr hslackPowLe) (sub_nonneg.mpr hsqPowLe)]

set_option maxRecDepth 2000 in
theorem normalizedEngelsmaLogTuple_mem_simplex_of_independent
    {R W : ℕ} {u : BoundedGaps.engelsmaTuple → ℕ}
    (hR : 1 < R)
    (hu : u ∈ preSievedSimplexTupleSupport BoundedGaps.engelsmaTuple R W) :
    (fun i => normalizedDivisorLogTuple BoundedGaps.engelsmaTuple R u
      (engelsmaIndexEquiv.symm i)) ∈ maynardSimplex 105 := by
  have huCommon := (mem_preSievedSimplexTupleSupport_iff.mp hu).1
  have huBox : u ∈ maynardDivisorTupleBox BoundedGaps.engelsmaTuple R := by
    rw [mem_maynardDivisorTupleBox_iff]
    intro h
    have huh := Fintype.mem_piFinset.mp huCommon h
    have huhData := Finset.mem_filter.mp huh
    exact ⟨huhData.2.1, Finset.mem_range.mp huhData.1⟩
  constructor
  · rw [maynardCube, maynardCubeOf, Set.mem_pi]
    intro i hi
    exact normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
      hR huBox (engelsmaIndexEquiv.symm i)
  · have hsum :
        (∑ i : Fin 105,
          normalizedDivisorLogTuple BoundedGaps.engelsmaTuple R u
            (engelsmaIndexEquiv.symm i)) =
        ∑ h : BoundedGaps.engelsmaTuple,
          normalizedDivisorLogTuple BoundedGaps.engelsmaTuple R u h :=
      engelsmaIndexEquiv.symm.sum_comp _
    rw [hsum]
    apply le_of_lt
    apply (divisorTupleProduct_lt_iff_sum_normalizedDivisorLogTuple_lt_one
      hR (fun h => (mem_maynardDivisorTupleBox_iff.mp huBox h).1)).mp
    exact (mem_preSievedSimplexTupleSupport_iff.mp hu).2

set_option maxRecDepth 2000 in
theorem abs_engelsmaCollisionQuadraticMomentSum_le_weight
    {alpha : ℝ} {N b c : ℕ}
    (hR : 1 < engelsmaMaynardRadius alpha N) :
    |engelsmaCollisionQuadraticMomentSum alpha N b c| ≤
      ∑ u ∈ preSievedSimplexCollisionSupport BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
        reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u := by
  unfold engelsmaCollisionQuadraticMomentSum
  calc
    |∑ u ∈ preSievedSimplexCollisionSupport BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
      simplexQuadraticIntegrand 105 b c (fun m =>
        normalizedDivisorLogTuple BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N) u (engelsmaIndexEquiv.symm m)) /
        ∏ h : BoundedGaps.engelsmaTuple,
          (Nat.totient (u h) : ℝ)| ≤
        ∑ u ∈ preSievedSimplexCollisionSupport BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
          |simplexQuadraticIntegrand 105 b c (fun m =>
            normalizedDivisorLogTuple BoundedGaps.engelsmaTuple
              (engelsmaMaynardRadius alpha N) u
              (engelsmaIndexEquiv.symm m)) /
            ∏ h : BoundedGaps.engelsmaTuple,
              (Nat.totient (u h) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ preSievedSimplexCollisionSupport BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
          reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u := by
      apply Finset.sum_le_sum
      intro u hu
      have huIndependent := (Finset.mem_filter.mp hu).1
      have hsimplex := normalizedEngelsmaLogTuple_mem_simplex_of_independent
        hR huIndependent
      have hquad := abs_simplexQuadraticIntegrand_le_one
        (b := b) (c := c) hsimplex
      have hdenNat : 0 < commonTotientProduct BoundedGaps.engelsmaTuple u := by
        apply Finset.prod_pos
        intro h hh
        exact Nat.totient_pos.mpr
          (preSievedSimplexTupleSupport_coordinate huIndependent h).1
      have hden : 0 <
          (commonTotientProduct BoundedGaps.engelsmaTuple u : ℝ) := by
        exact_mod_cast hdenNat
      have hprod : (commonTotientProduct BoundedGaps.engelsmaTuple u : ℝ) =
          ∏ h : BoundedGaps.engelsmaTuple,
            (Nat.totient (u h) : ℝ) := by
        unfold commonTotientProduct
        push_cast
        simp
      rw [abs_div, ← hprod, abs_of_pos hden]
      calc
        |simplexQuadraticIntegrand 105 b c (fun m =>
            normalizedDivisorLogTuple BoundedGaps.engelsmaTuple
              (engelsmaMaynardRadius alpha N) u
              (engelsmaIndexEquiv.symm m))| /
              (commonTotientProduct BoundedGaps.engelsmaTuple u : ℝ) ≤
            1 / (commonTotientProduct BoundedGaps.engelsmaTuple u : ℝ) := by
          exact div_le_div_of_nonneg_right hquad hden.le
        _ = reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u := by
          rw [inv_commonTotientProduct_eq_product]
          rfl

end BoundedGaps.Maynard
