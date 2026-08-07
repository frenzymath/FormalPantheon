import BoundedGaps.BombieriVinogradov.Analytic.BilinearProductCutoffMaximum
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveConductorFibers

/-!
# Primitive-character aggregation of the bilinear Perron estimate

This file sums the product-cutoff maximum independently over primitive
characters and positive moduli. It first retains the raw Perron factor `pi`,
then divides by it to prove the exact finite natural form of equation (6.4).

Source: `AkbaryHambrook2013v2`, Section 6, pp. 17--18, equation (6.4).
Semantic review: `SEM-454`.
-/

open MeasureTheory
open scoped Interval BigOperators

namespace BoundedGaps.Maynard

noncomputable section

/-- The total `q / phi(q)` weight of primitive characters through `Q` is at
most `Q^2`. -/
theorem sum_weighted_card_primitiveCharacters_le_sq (Q : ℕ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        (Fintype.card (primitiveCharacters q) : ℝ)) ≤ (Q : ℝ) ^ 2 := by
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          (Fintype.card (primitiveCharacters q) : ℝ)) ≤
        ∑ q ∈ Finset.Ioc 0 Q, (q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q := (Finset.mem_Ioc.mp hq).1
      have hphi : 0 < (q.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hqpos
      calc
        (q : ℝ) / (q.totient : ℝ) *
            (Fintype.card (primitiveCharacters q) : ℝ) ≤
            (q : ℝ) / (q.totient : ℝ) * (q.totient : ℝ) := by
          gcongr
          exact_mod_cast card_primitiveCharacters_le_totient hqpos
        _ = (q : ℝ) := by field_simp
    _ ≤ ∑ _q ∈ Finset.Ioc 0 Q, (Q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact_mod_cast (Finset.mem_Ioc.mp hq).2
    _ = (Q : ℝ) ^ 2 := by
      simp [Nat.card_Ioc]
      ring

/-- Raw primitive-character and modulus aggregate. The maximum is taken
separately for every primitive character, and `pi` is not yet divided out. -/
theorem pi_mul_sum_weighted_bilinearProductCutoffMaximum_le
    {K : ℕ} (hK : 0 < K) (Q : ℕ)
    (sm sn : Finset ℕ) (a b : ℕ → ℂ) {T : ℝ} (hT : 0 < T)
    (hmPos : ∀ m ∈ sm, 0 < m)
    (hnPos : ∀ n ∈ sn, 0 < n)
    (hprod : ∀ m ∈ sm, ∀ n ∈ sn, m * n ≤ K) :
    Real.pi *
        (∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ ψ : primitiveCharacters q,
              bilinearProductCutoffMaximum K q ψ.1 sm sn a b) ≤
      (∫ t in -T..T,
        perronEnvelope (Real.log (2 * (K : ℝ))) t *
          ∑ q ∈ Finset.Ioc 0 Q,
            (q : ℝ) / (q.totient : ℝ) *
              ∑ ψ : primitiveCharacters q,
                ‖∑ m ∈ sm, ∑ n ∈ sn,
                  (a m * natLogTwist m t) *
                    (b n * natLogTwist n t) * ψ.1 (m * n)‖) +
      (2 * (K : ℝ) / (T * Real.log (4 / 3 : ℝ)) *
        (∑ m ∈ sm, ‖a m‖) * (∑ n ∈ sn, ‖b n‖)) * (Q : ℝ) ^ 2 := by
  let weight : ℕ → ℝ := fun q => (q : ℝ) / (q.totient : ℝ)
  let rect : (q : ℕ) → primitiveCharacters q → ℝ → ℂ :=
    fun _q ψ t => ∑ m ∈ sm, ∑ n ∈ sn,
      (a m * natLogTwist m t) * (b n * natLogTwist n t) * ψ.1 (m * n)
  let envelope : ℝ → ℝ := perronEnvelope (Real.log (2 * (K : ℝ)))
  let f : (q : ℕ) → primitiveCharacters q → ℝ → ℝ :=
    fun q ψ t => envelope t * ‖rect q ψ t‖
  let error : ℝ := 2 * (K : ℝ) / (T * Real.log (4 / 3 : ℝ)) *
    (∑ m ∈ sm, ‖a m‖) * (∑ n ∈ sn, ‖b n‖)
  have hB : 0 ≤ Real.log (2 * (K : ℝ)) := by
    apply Real.log_nonneg
    have hKone : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    nlinarith
  have hrect (q : ℕ) (ψ : primitiveCharacters q) :
      Continuous (rect q ψ) := by
    dsimp only [rect, natLogTwist]
    fun_prop
  have hf (q : ℕ) (ψ : primitiveCharacters q) : Continuous (f q ψ) := by
    exact (continuous_perronEnvelope hB).mul (hrect q ψ).norm
  have hweight {q : ℕ} (hq : q ∈ Finset.Ioc 0 Q) : 0 ≤ weight q := by
    have hqpos : 0 < q := (Finset.mem_Ioc.mp hq).1
    have hphi : 0 < (q.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hqpos
    exact div_nonneg (Nat.cast_nonneg q) hphi.le
  have hfixed (q : ℕ) (_hq : q ∈ Finset.Ioc 0 Q)
      (ψ : primitiveCharacters q) :
      Real.pi * bilinearProductCutoffMaximum K q ψ.1 sm sn a b ≤
        (∫ t in -T..T, f q ψ t) + error := by
    simpa only [f, envelope, rect, error] using
      pi_mul_bilinearProductCutoffMaximum_le_integral_perronEnvelope_add
        hK ψ.1 sm sn a b hT hmPos hnPos hprod
  have hsum :
      (∑ q ∈ Finset.Ioc 0 Q, weight q *
        ∑ ψ : primitiveCharacters q,
          Real.pi * bilinearProductCutoffMaximum K q ψ.1 sm sn a b) ≤
      ∑ q ∈ Finset.Ioc 0 Q, weight q *
        ∑ ψ : primitiveCharacters q,
          ((∫ t in -T..T, f q ψ t) + error) := by
    apply Finset.sum_le_sum
    intro q hq
    apply mul_le_mul_of_nonneg_left _ (hweight hq)
    apply Finset.sum_le_sum
    intro ψ _hψ
    exact hfixed q hq ψ
  have hinterchange :
      (∑ q ∈ Finset.Ioc 0 Q, weight q *
        ∑ ψ : primitiveCharacters q, ∫ t in -T..T, f q ψ t) =
      ∫ t in -T..T,
        ∑ q ∈ Finset.Ioc 0 Q, weight q *
          ∑ ψ : primitiveCharacters q, f q ψ t := by
    symm
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q _hq
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum]
      intro ψ _hψ
      exact (hf q ψ).intervalIntegrable _ _
    · intro q _hq
      have hsumContinuous : Continuous (fun t =>
          ∑ ψ : primitiveCharacters q, f q ψ t) :=
        continuous_finsetSum Finset.univ (fun ψ _hψ => hf q ψ)
      exact (continuous_const.mul hsumContinuous).intervalIntegrable _ _
  have hmass :
      (∑ q ∈ Finset.Ioc 0 Q, weight q *
        (Fintype.card (primitiveCharacters q) : ℝ)) ≤ (Q : ℝ) ^ 2 := by
    simpa only [weight] using sum_weighted_card_primitiveCharacters_le_sq Q
  have herror : 0 ≤ error := by
    dsimp only [error]
    positivity
  calc
    Real.pi *
        (∑ q ∈ Finset.Ioc 0 Q, weight q *
          ∑ ψ : primitiveCharacters q,
            bilinearProductCutoffMaximum K q ψ.1 sm sn a b) =
        ∑ q ∈ Finset.Ioc 0 Q, weight q *
          ∑ ψ : primitiveCharacters q,
            Real.pi * bilinearProductCutoffMaximum K q ψ.1 sm sn a b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      calc
        Real.pi * (weight q *
            ∑ ψ : primitiveCharacters q,
              bilinearProductCutoffMaximum K q ψ.1 sm sn a b) =
            weight q * (Real.pi *
              ∑ ψ : primitiveCharacters q,
                bilinearProductCutoffMaximum K q ψ.1 sm sn a b) := by
          ring
        _ = weight q *
            ∑ ψ : primitiveCharacters q,
              Real.pi * bilinearProductCutoffMaximum K q ψ.1 sm sn a b := by
          rw [Finset.mul_sum]
    _ ≤ ∑ q ∈ Finset.Ioc 0 Q, weight q *
          ∑ ψ : primitiveCharacters q,
            ((∫ t in -T..T, f q ψ t) + error) := hsum
    _ = (∑ q ∈ Finset.Ioc 0 Q, weight q *
          ∑ ψ : primitiveCharacters q, ∫ t in -T..T, f q ψ t) +
        error * (∑ q ∈ Finset.Ioc 0 Q, weight q *
          (Fintype.card (primitiveCharacters q) : ℝ)) := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      calc
        (∑ q ∈ Finset.Ioc 0 Q,
            weight q * ((Fintype.card (primitiveCharacters q) : ℝ) * error)) =
            ∑ q ∈ Finset.Ioc 0 Q,
              (weight q * (Fintype.card (primitiveCharacters q) : ℝ)) * error := by
          apply Finset.sum_congr rfl
          intro q _hq
          ring
        _ = (∑ q ∈ Finset.Ioc 0 Q,
              weight q * (Fintype.card (primitiveCharacters q) : ℝ)) * error := by
          rw [Finset.sum_mul]
        _ = error * (∑ q ∈ Finset.Ioc 0 Q,
              weight q * (Fintype.card (primitiveCharacters q) : ℝ)) := by ring
    _ = (∫ t in -T..T,
          ∑ q ∈ Finset.Ioc 0 Q, weight q *
            ∑ ψ : primitiveCharacters q, f q ψ t) +
        error * (∑ q ∈ Finset.Ioc 0 Q, weight q *
          (Fintype.card (primitiveCharacters q) : ℝ)) := by
      rw [hinterchange]
    _ ≤ (∫ t in -T..T,
          ∑ q ∈ Finset.Ioc 0 Q, weight q *
            ∑ ψ : primitiveCharacters q, f q ψ t) +
        error * (Q : ℝ) ^ 2 := by gcongr
    _ = _ := by
      dsimp only [weight, error]
      congr 1
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only [f, envelope, rect]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      apply Finset.sum_congr rfl
      intro ψ _hψ
      ring

/-- Exact finite natural form of Akbary--Hambrook equation (6.4). -/
theorem sum_weighted_bilinearProductCutoffMaximum_le
    {K : ℕ} (hK : 0 < K) (Q : ℕ)
    (sm sn : Finset ℕ) (a b : ℕ → ℂ) {T : ℝ} (hT : 0 < T)
    (hmPos : ∀ m ∈ sm, 0 < m)
    (hnPos : ∀ n ∈ sn, 0 < n)
    (hprod : ∀ m ∈ sm, ∀ n ∈ sn, m * n ≤ K) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ ψ : primitiveCharacters q,
          bilinearProductCutoffMaximum K q ψ.1 sm sn a b) ≤
      1 / Real.pi *
        (∫ t in -T..T,
          perronEnvelope (Real.log (2 * (K : ℝ))) t *
            ∑ q ∈ Finset.Ioc 0 Q,
              (q : ℝ) / (q.totient : ℝ) *
                ∑ ψ : primitiveCharacters q,
                  ‖∑ m ∈ sm, ∑ n ∈ sn,
                    (a m * natLogTwist m t) *
                      (b n * natLogTwist n t) * ψ.1 (m * n)‖) +
      2 * (K : ℝ) * (Q : ℝ) ^ 2 /
          (Real.pi * Real.log (4 / 3 : ℝ) * T) *
        (∑ m ∈ sm, ‖a m‖) * (∑ n ∈ sn, ‖b n‖) := by
  let S : ℝ := ∑ q ∈ Finset.Ioc 0 Q,
    (q : ℝ) / (q.totient : ℝ) *
      ∑ ψ : primitiveCharacters q,
        bilinearProductCutoffMaximum K q ψ.1 sm sn a b
  let I : ℝ := ∫ t in -T..T,
    perronEnvelope (Real.log (2 * (K : ℝ))) t *
      ∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ ψ : primitiveCharacters q,
            ‖∑ m ∈ sm, ∑ n ∈ sn,
              (a m * natLogTwist m t) *
                (b n * natLogTwist n t) * ψ.1 (m * n)‖
  let A : ℝ := ∑ m ∈ sm, ‖a m‖
  let B : ℝ := ∑ n ∈ sn, ‖b n‖
  have hraw : Real.pi * S ≤
      I + (2 * (K : ℝ) / (T * Real.log (4 / 3 : ℝ)) * A * B) *
        (Q : ℝ) ^ 2 := by
    simpa only [S, I, A, B] using
      pi_mul_sum_weighted_bilinearProductCutoffMaximum_le
        hK Q sm sn a b hT hmPos hnPos hprod
  calc
    S ≤ (I + (2 * (K : ℝ) / (T * Real.log (4 / 3 : ℝ)) * A * B) *
        (Q : ℝ) ^ 2) / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      simpa only [mul_comm] using hraw
    _ = 1 / Real.pi * I +
        2 * (K : ℝ) * (Q : ℝ) ^ 2 /
            (Real.pi * Real.log (4 / 3 : ℝ) * T) * A * B := by
      have hlog : Real.log (4 / 3 : ℝ) ≠ 0 :=
        (Real.log_pos (by norm_num)).ne'
      field_simp [Real.pi_ne_zero, hT.ne', hlog]
    _ = _ := by rfl

/-- Sparse translated-rectangle specialization of equation (6.4). The cap is
the product of upper endpoints, not the product of interval spans. -/
theorem sum_weighted_bilinearProductCutoffMaximum_subset_Ioc_le
    (Q m0 M n0 N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (sm sn : Finset ℕ)
    (hsm : sm ⊆ Finset.Ioc m0 (m0 + M))
    (hsn : sn ⊆ Finset.Ioc n0 (n0 + N))
    (a b : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ ψ : primitiveCharacters q,
          bilinearProductCutoffMaximum
            ((m0 + M) * (n0 + N)) q ψ.1 sm sn a b) ≤
      1 / Real.pi *
        (∫ t in -T..T,
          perronEnvelope
              (Real.log (2 * (((m0 + M) * (n0 + N) : ℕ) : ℝ))) t *
            ∑ q ∈ Finset.Ioc 0 Q,
              (q : ℝ) / (q.totient : ℝ) *
                ∑ ψ : primitiveCharacters q,
                  ‖∑ m ∈ sm, ∑ n ∈ sn,
                    (a m * natLogTwist m t) *
                      (b n * natLogTwist n t) * ψ.1 (m * n)‖) +
      2 * (((m0 + M) * (n0 + N) : ℕ) : ℝ) * (Q : ℝ) ^ 2 /
          (Real.pi * Real.log (4 / 3 : ℝ) * T) *
        (∑ m ∈ sm, ‖a m‖) * (∑ n ∈ sn, ‖b n‖) := by
  have hmUpperPos : 0 < m0 + M := by omega
  have hnUpperPos : 0 < n0 + N := by omega
  have hK : 0 < (m0 + M) * (n0 + N) :=
    Nat.mul_pos hmUpperPos hnUpperPos
  have hmPos : ∀ m ∈ sm, 0 < m := by
    intro m hm
    have hmBounds := Finset.mem_Ioc.mp (hsm hm)
    omega
  have hnPos : ∀ n ∈ sn, 0 < n := by
    intro n hn
    have hnBounds := Finset.mem_Ioc.mp (hsn hn)
    omega
  have hprod :
      ∀ m ∈ sm, ∀ n ∈ sn, m * n ≤ (m0 + M) * (n0 + N) := by
    intro m hm n hn
    exact Nat.mul_le_mul
      (Finset.mem_Ioc.mp (hsm hm)).2
      (Finset.mem_Ioc.mp (hsn hn)).2
  exact sum_weighted_bilinearProductCutoffMaximum_le
    hK Q sm sn a b hT hmPos hnPos hprod

end

end BoundedGaps.Maynard
