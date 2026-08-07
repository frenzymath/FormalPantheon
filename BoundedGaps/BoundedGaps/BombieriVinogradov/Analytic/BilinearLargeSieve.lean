import BoundedGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.Real.Sqrt

/-!
# The rectangular bilinear character large sieve

This file proves the character-independent rectangular estimate used in the
Cauchy--Schwarz step of AkbaryHambrook2013v2, Lemma 6.1, printed p. 18. The
product cutoff and maximal Perron argument are separate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

private theorem sum_weighted_norm_mul_primitiveTwists_le
    (Q : ℕ)
    (A B : (q : ℕ) → primitiveCharacters q → ℂ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ psi : primitiveCharacters q, ‖A q psi * B q psi‖) ≤
      Real.sqrt
          (∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q, ‖A q psi‖ ^ 2) *
        Real.sqrt
          (∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q, ‖B q psi‖ ^ 2) := by
  classical
  let indices : Finset (Σ q : ℕ, primitiveCharacters q) :=
    (Finset.Ioc 0 Q).sigma fun q => (Finset.univ : Finset (primitiveCharacters q))
  let weight : ℕ → ℝ := fun q => (q : ℝ) / (q.totient : ℝ)
  let f : (Σ q : ℕ, primitiveCharacters q) → ℝ := fun z =>
    Real.sqrt (weight z.1) * ‖A z.1 z.2‖
  let g : (Σ q : ℕ, primitiveCharacters q) → ℝ := fun z =>
    Real.sqrt (weight z.1) * ‖B z.1 z.2‖
  have hweight (q : ℕ) (hq : q ∈ Finset.Ioc 0 Q) : 0 ≤ weight q := by
    have hqpos : 0 < q := (Finset.mem_Ioc.mp hq).1
    have hphi : 0 < (q.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hqpos
    exact div_nonneg (Nat.cast_nonneg q) hphi.le
  have hleft :
      (∑ z ∈ indices, f z ^ 2) =
        ∑ q ∈ Finset.Ioc 0 Q,
          weight q * ∑ psi : primitiveCharacters q, ‖A q psi‖ ^ 2 := by
    rw [show (∑ z ∈ indices, f z ^ 2) =
        ∑ q ∈ Finset.Ioc 0 Q,
          ∑ psi : primitiveCharacters q, f ⟨q, psi⟩ ^ 2 by
      simpa only [indices] using
        Finset.sum_sigma (Finset.Ioc 0 Q)
          (fun q => (Finset.univ : Finset (primitiveCharacters q)))
          (fun z => f z ^ 2)]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro psi _hpsi
    simp only [f, mul_pow, Real.sq_sqrt (hweight q hq)]
  have hright :
      (∑ z ∈ indices, g z ^ 2) =
        ∑ q ∈ Finset.Ioc 0 Q,
          weight q * ∑ psi : primitiveCharacters q, ‖B q psi‖ ^ 2 := by
    rw [show (∑ z ∈ indices, g z ^ 2) =
        ∑ q ∈ Finset.Ioc 0 Q,
          ∑ psi : primitiveCharacters q, g ⟨q, psi⟩ ^ 2 by
      simpa only [indices] using
        Finset.sum_sigma (Finset.Ioc 0 Q)
          (fun q => (Finset.univ : Finset (primitiveCharacters q)))
          (fun z => g z ^ 2)]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro psi _hpsi
    simp only [g, mul_pow, Real.sq_sqrt (hweight q hq)]
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q, ‖A q psi * B q psi‖) =
        ∑ z ∈ indices, f z * g z := by
      rw [show (∑ z ∈ indices, f z * g z) =
          ∑ q ∈ Finset.Ioc 0 Q,
            ∑ psi : primitiveCharacters q, f ⟨q, psi⟩ * g ⟨q, psi⟩ by
        simpa only [indices] using
          Finset.sum_sigma (Finset.Ioc 0 Q)
            (fun q => (Finset.univ : Finset (primitiveCharacters q)))
            (fun z => f z * g z)]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro psi _hpsi
      rw [norm_mul]
      simp only [f, g]
      change weight q * (‖A q psi‖ * ‖B q psi‖) =
        (Real.sqrt (weight q) * ‖A q psi‖) *
          (Real.sqrt (weight q) * ‖B q psi‖)
      calc
        weight q * (‖A q psi‖ * ‖B q psi‖) =
            Real.sqrt (weight q) ^ 2 * (‖A q psi‖ * ‖B q psi‖) := by
          rw [Real.sq_sqrt (hweight q hq)]
        _ = (Real.sqrt (weight q) * ‖A q psi‖) *
            (Real.sqrt (weight q) * ‖B q psi‖) := by ring
    _ ≤ Real.sqrt (∑ z ∈ indices, f z ^ 2) *
        Real.sqrt (∑ z ∈ indices, g z ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt indices f g
    _ = Real.sqrt
          (∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q, ‖A q psi‖ ^ 2) *
        Real.sqrt
          (∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q, ‖B q psi‖ ^ 2) := by
      rw [hleft, hright]

private theorem bilinear_sum_eq_mul_twists
    (q : ℕ) (psi : primitiveCharacters q)
    (sm sn : Finset ℕ) (a b : ℕ → ℂ) :
    (∑ m ∈ sm, ∑ n ∈ sn, a m * b n * psi.1 (m * n)) =
      (∑ m ∈ sm, a m * psi.1 m) * (∑ n ∈ sn, b n * psi.1 n) := by
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  rw [map_mul]
  ring

/-- The sparse rectangular bilinear consequence of the primitive-character
large sieve. Both containing-interval spans remain explicit. -/
theorem sum_weighted_norm_bilinear_primitiveTwists_subset_Ioc_le
    (Q m0 M n0 N : ℕ) (sm sn : Finset ℕ)
    (hm : sm ⊆ Finset.Ioc m0 (m0 + M))
    (hn : sn ⊆ Finset.Ioc n0 (n0 + N))
    (a b : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ psi : primitiveCharacters q,
          ‖∑ m ∈ sm, ∑ n ∈ sn,
            a m * b n * psi.1 (m * n)‖) ≤
      Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
        Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
        Real.sqrt (∑ m ∈ sm, ‖a m‖ ^ 2) *
        Real.sqrt (∑ n ∈ sn, ‖b n‖ ^ 2) := by
  let A : (q : ℕ) → primitiveCharacters q → ℂ := fun q psi =>
    ∑ m ∈ sm, a m * psi.1 m
  let B : (q : ℕ) → primitiveCharacters q → ℂ := fun q psi =>
    ∑ n ∈ sn, b n * psi.1 n
  have hcauchy := sum_weighted_norm_mul_primitiveTwists_le Q A B
  have hA := sum_weighted_norm_sq_primitiveTwists_subset_Ioc_le
    Q m0 M sm hm a
  have hB := sum_weighted_norm_sq_primitiveTwists_subset_Ioc_le
    Q n0 N sn hn b
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ psi : primitiveCharacters q,
            ‖∑ m ∈ sm, ∑ n ∈ sn,
              a m * b n * psi.1 (m * n)‖) =
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ psi : primitiveCharacters q, ‖A q psi * B q psi‖ := by
      apply Finset.sum_congr rfl
      intro q _hq
      congr 1
      apply Finset.sum_congr rfl
      intro psi _hpsi
      rw [bilinear_sum_eq_mul_twists]
    _ ≤ Real.sqrt
          (∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q, ‖A q psi‖ ^ 2) *
        Real.sqrt
          (∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ psi : primitiveCharacters q, ‖B q psi‖ ^ 2) := hcauchy
    _ ≤ Real.sqrt
          (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ sm, ‖a m‖ ^ 2) *
        Real.sqrt
          (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ sn, ‖b n‖ ^ 2) := by
      exact mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
        Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
        Real.sqrt (∑ m ∈ sm, ‖a m‖ ^ 2) *
        Real.sqrt (∑ n ∈ sn, ‖b n‖ ^ 2) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ (M : ℝ) + (Q : ℝ) ^ 2),
        Real.sqrt_mul (by positivity : 0 ≤ (N : ℝ) + (Q : ℝ) ^ 2)]
      ring

/-- Full consecutive-rectangle specialization of the bilinear character
large sieve. -/
theorem sum_weighted_norm_bilinear_primitiveTwists_Ioc_le
    (Q m0 M n0 N : ℕ) (a b : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ psi : primitiveCharacters q,
          ‖∑ m ∈ Finset.Ioc m0 (m0 + M),
            ∑ n ∈ Finset.Ioc n0 (n0 + N),
              a m * b n * psi.1 (m * n)‖) ≤
      Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
        Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
        Real.sqrt
          (∑ m ∈ Finset.Ioc m0 (m0 + M), ‖a m‖ ^ 2) *
        Real.sqrt
          (∑ n ∈ Finset.Ioc n0 (n0 + N), ‖b n‖ ^ 2) := by
  exact sum_weighted_norm_bilinear_primitiveTwists_subset_Ioc_le
    Q m0 M n0 N (Finset.Ioc m0 (m0 + M))
      (Finset.Ioc n0 (n0 + N)) (by rfl) (by rfl) a b

end

end BoundedGaps.Maynard
