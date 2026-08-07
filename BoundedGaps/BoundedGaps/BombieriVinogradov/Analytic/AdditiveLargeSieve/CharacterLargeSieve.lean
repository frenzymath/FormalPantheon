import BoundedGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.ReducedFractionLargeSieve
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveCharacterAdditiveReduction

/-!
# The primitive-character large sieve

This file composes the reduced-fraction additive large sieve with SEM-443's
fixed-modulus Gauss/Parseval reduction. The resulting theorem is
AkbaryHambrook2013v2, equation (6.1), for a natural consecutive interval.
See SEM-448.
-/

open scoped BigOperators

noncomputable section

namespace BoundedGaps.Maynard

private theorem Icc_one_eq_Ioc_zero (Q : ℕ) :
    Finset.Icc 1 Q = Finset.Ioc 0 Q := by
  ext q
  simp
  omega

private theorem sum_positiveModuliUpTo_eq_sum_Ioc
    (Q : ℕ) (f : ℕ → ℝ) :
    (∑ q : positiveModuliUpTo Q, f q.1) =
      ∑ q ∈ Finset.Ioc 0 Q, f q := by
  calc
    (∑ q : positiveModuliUpTo Q, f q.1) =
        ∑ q ∈ Finset.Icc 1 Q, f q :=
      (Finset.sum_subtype (p := fun q => q ∈ Finset.Icc 1 Q)
        (Finset.Icc 1 Q) (by simp) f).symm
    _ = ∑ q ∈ Finset.Ioc 0 Q, f q := by rw [Icc_one_eq_Ioc_zero]

private theorem sum_units_eq_sum_reduced
    (Q : ℕ) (f : reducedFractionIndices Q → ℝ) :
    (∑ q : positiveModuliUpTo Q, ∑ u : (ZMod q.1)ˣ, f ⟨q, u⟩) =
      ∑ z : reducedFractionIndices Q, f z := by
  rw [← Finset.sum_sigma]
  apply Finset.sum_congr
  · ext z
    simp
  · intro z _hz
    rfl

/-- Akbary--Hambrook equation (6.1): the weighted square norm of all
primitive character twists of a consecutive interval is bounded by the exact
large-sieve coefficient `N + Q^2`. -/
theorem sum_weighted_norm_sq_primitiveTwists_Ioc_le
    (Q m0 N : ℕ) (c : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (Nat.totient q : ℝ) *
        ∑ psi : primitiveCharacters q,
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N),
            c n * psi.1 n‖ ^ 2) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) *
        ∑ n ∈ Finset.Ioc m0 (m0 + N), ‖c n‖ ^ 2 := by
  classical
  have hfixed :
      (∑ q : positiveModuliUpTo Q,
        (q.1 : ℝ) / (Nat.totient q.1 : ℝ) *
          ∑ psi : primitiveCharacters q.1,
            ‖∑ n ∈ Finset.Ioc m0 (m0 + N),
              c n * psi.1 n‖ ^ 2) ≤
        ∑ q : positiveModuliUpTo Q,
          ∑ u : (ZMod q.1)ˣ,
            ‖∑ n ∈ Finset.Ioc m0 (m0 + N),
              c n * ZMod.stdAddChar
                ((u : ZMod q.1) * (n : ZMod q.1))‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro q _hq
    exact weighted_sum_norm_sq_primitiveTwists_le_unitAdditiveSums
      (q := q.1) (Finset.Ioc m0 (m0 + N)) c
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (Nat.totient q : ℝ) *
          ∑ psi : primitiveCharacters q,
            ‖∑ n ∈ Finset.Ioc m0 (m0 + N),
              c n * psi.1 n‖ ^ 2) =
        ∑ q : positiveModuliUpTo Q,
          (q.1 : ℝ) / (Nat.totient q.1 : ℝ) *
            ∑ psi : primitiveCharacters q.1,
              ‖∑ n ∈ Finset.Ioc m0 (m0 + N),
                c n * psi.1 n‖ ^ 2 :=
      (sum_positiveModuliUpTo_eq_sum_Ioc Q fun q =>
        (q : ℝ) / (Nat.totient q : ℝ) *
          ∑ psi : primitiveCharacters q,
            ‖∑ n ∈ Finset.Ioc m0 (m0 + N),
              c n * psi.1 n‖ ^ 2).symm
    _ ≤ ∑ q : positiveModuliUpTo Q,
          ∑ u : (ZMod q.1)ˣ,
            ‖∑ n ∈ Finset.Ioc m0 (m0 + N),
              c n * ZMod.stdAddChar
                ((u : ZMod q.1) * (n : ZMod q.1))‖ ^ 2 := hfixed
    _ = ∑ z : reducedFractionIndices Q,
          ‖∑ n ∈ Finset.Ioc m0 (m0 + N),
            c n * ZMod.stdAddChar
              ((z.2 : ZMod z.1.1) * (n : ZMod z.1.1))‖ ^ 2 := by
      exact sum_units_eq_sum_reduced Q fun z =>
        ‖∑ n ∈ Finset.Ioc m0 (m0 + N),
          c n * ZMod.stdAddChar
            ((z.2 : ZMod z.1.1) * (n : ZMod z.1.1))‖ ^ 2
    _ ≤ ((N : ℝ) + (Q : ℝ) ^ 2) *
          ∑ n ∈ Finset.Ioc m0 (m0 + N), ‖c n‖ ^ 2 :=
      sum_norm_sq_reducedFraction_stdAddChar_Ioc_le Q m0 N c

private theorem sum_zeroExtension_mul
    (s t : Finset ℕ) (hst : s ⊆ t) (c f : ℕ → ℂ) :
    (∑ n ∈ t, (if n ∈ s then c n else 0) * f n) =
      ∑ n ∈ s, c n * f n := by
  calc
    (∑ n ∈ t, (if n ∈ s then c n else 0) * f n) =
        ∑ n ∈ s, (if n ∈ s then c n else 0) * f n := by
      symm
      apply Finset.sum_subset hst
      intro n _hnt hns
      simp [hns]
    _ = ∑ n ∈ s, c n * f n := by
      apply Finset.sum_congr rfl
      intro n hns
      simp [hns]

private theorem sum_norm_sq_zeroExtension
    (s t : Finset ℕ) (hst : s ⊆ t) (c : ℕ → ℂ) :
    (∑ n ∈ t, ‖if n ∈ s then c n else 0‖ ^ 2) =
      ∑ n ∈ s, ‖c n‖ ^ 2 := by
  calc
    (∑ n ∈ t, ‖if n ∈ s then c n else 0‖ ^ 2) =
        ∑ n ∈ s, ‖if n ∈ s then c n else 0‖ ^ 2 := by
      symm
      apply Finset.sum_subset hst
      intro n _hnt hns
      simp [hns]
    _ = ∑ n ∈ s, ‖c n‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hns
      simp [hns]

/-- Sparse-support form of the primitive-character large sieve. The bound
retains the length `N` of the containing interval, not the support cardinality.
-/
theorem sum_weighted_norm_sq_primitiveTwists_subset_Ioc_le
    (Q m0 N : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.Ioc m0 (m0 + N)) (c : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (Nat.totient q : ℝ) *
        ∑ psi : primitiveCharacters q,
          ‖∑ n ∈ s, c n * psi.1 n‖ ^ 2) ≤
      ((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ s, ‖c n‖ ^ 2 := by
  classical
  let d : ℕ → ℂ := fun n => if n ∈ s then c n else 0
  have htwist (q : ℕ) (psi : primitiveCharacters q) :
      (∑ n ∈ Finset.Ioc m0 (m0 + N), d n * psi.1 n) =
        ∑ n ∈ s, c n * psi.1 n := by
    simpa only [d] using sum_zeroExtension_mul s
      (Finset.Ioc m0 (m0 + N)) hs c (fun n => psi.1 n)
  have henergy :
      (∑ n ∈ Finset.Ioc m0 (m0 + N), ‖d n‖ ^ 2) =
        ∑ n ∈ s, ‖c n‖ ^ 2 := by
    simpa only [d] using sum_norm_sq_zeroExtension s
      (Finset.Ioc m0 (m0 + N)) hs c
  have hlarge := sum_weighted_norm_sq_primitiveTwists_Ioc_le Q m0 N d
  simp_rw [htwist] at hlarge
  rw [henergy] at hlarge
  exact hlarge

end BoundedGaps.Maynard
