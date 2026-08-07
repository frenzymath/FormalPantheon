import BoundedGaps.BombieriVinogradov.Analytic.MaximalBilinearLargeSieve

/-!
# The optimized maximal bilinear theorem

This file specializes the preoptimized estimate at the source Perron radius
and exports the sparse and full forms of AkbaryHambrook2013v2, Lemma 6.1,
printed pp. 17--18.

Semantic review: `SEM-455`.
-/

open scoped BigOperators

namespace BoundedGaps.Maynard

noncomputable section

/-- Positivity of the exact constant in Akbary--Hambrook Lemma 6.1. -/
theorem akbaryHambrookC3_pos : 0 < akbaryHambrookC3 := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogFourThirds : 0 < Real.log (4 / 3 : ℝ) :=
    Real.log_pos (by norm_num)
  have hlogCompare : Real.log (4 / 3 : ℝ) < Real.log 2 :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have hratio : 1 < Real.log 2 / Real.log (4 / 3 : ℝ) :=
    (one_lt_div hlogFourThirds).2 hlogCompare
  have hlogRatio : 0 <
      Real.log (Real.log 2 / Real.log (4 / 3 : ℝ)) :=
    Real.log_pos hratio
  unfold akbaryHambrookC3
  positivity

/-- Sparse translated-interval form of Akbary--Hambrook Lemma 6.1 with the
exact constant `c3`. -/
theorem sum_weighted_bilinearProductCutoffMaximum_subset_Ioc_le_c3
    (Q m0 M n0 N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (sm sn : Finset ℕ)
    (hsm : sm ⊆ Finset.Ioc m0 (m0 + M))
    (hsn : sn ⊆ Finset.Ioc n0 (n0 + N))
    (a b : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ psi : primitiveCharacters q,
          bilinearProductCutoffMaximum
            ((m0 + M) * (n0 + N)) q psi.1 sm sn a b) ≤
      akbaryHambrookC3 *
        Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
        Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
        Real.sqrt (∑ m ∈ sm, ‖a m‖ ^ 2) *
        Real.sqrt (∑ n ∈ sn, ‖b n‖ ^ 2) *
        Real.log
          (2 * (((m0 + M) * (n0 + N) : ℕ) : ℝ)) := by
  let K : ℕ := (m0 + M) * (n0 + N)
  let P : ℝ := (K : ℝ)
  let B : ℝ := Real.log (2 * P)
  let T : ℝ := akbaryHambrookPerronTime P
  let G : ℝ := Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
    Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
    Real.sqrt (∑ m ∈ sm, ‖a m‖ ^ 2) *
    Real.sqrt (∑ n ∈ sn, ‖b n‖ ^ 2)
  let L : ℝ := ∑ q ∈ Finset.Ioc 0 Q,
    (q : ℝ) / (q.totient : ℝ) *
      ∑ psi : primitiveCharacters q,
        bilinearProductCutoffMaximum K q psi.1 sm sn a b
  have hK : 0 < K := Nat.mul_pos (by omega) (by omega)
  have hP : 1 ≤ P := by
    dsimp only [P]
    exact_mod_cast hK
  have hB : 0 < B := by
    dsimp only [B]
    exact Real.log_pos (by nlinarith)
  have hT : 0 < T := by
    exact akbaryHambrookPerronTime_pos hP
  have hregime : 1 ≤ T * B := by
    exact one_le_akbaryHambrookPerronTime_mul_log hP
  have hpre :=
    sum_weighted_bilinearProductCutoffMaximum_subset_Ioc_le_preoptimized
      Q m0 M n0 N hM hN sm sn hsm hsn a b hT hregime
  change L ≤ G *
    (2 / Real.pi * Real.log (Real.exp 1 * T * B) +
      2 * P * Real.sqrt P /
        (Real.pi * Real.log (4 / 3 : ℝ) * T)) at hpre
  have heq := akbaryHambrook_equation_six_five hP
  change 2 / Real.pi *
      (Real.log (Real.exp 1 * T * B) +
        P * Real.sqrt P / (Real.log (4 / 3 : ℝ) * T)) / B ≤
    akbaryHambrookC3 at heq
  have hraw := (div_le_iff₀ hB).mp heq
  have hcoefficient :
      2 / Real.pi * Real.log (Real.exp 1 * T * B) +
          2 * P * Real.sqrt P /
            (Real.pi * Real.log (4 / 3 : ℝ) * T) ≤
        akbaryHambrookC3 * B := by
    calc
      2 / Real.pi * Real.log (Real.exp 1 * T * B) +
          2 * P * Real.sqrt P /
            (Real.pi * Real.log (4 / 3 : ℝ) * T) =
          2 / Real.pi *
            (Real.log (Real.exp 1 * T * B) +
              P * Real.sqrt P /
                (Real.log (4 / 3 : ℝ) * T)) := by ring
      _ ≤ akbaryHambrookC3 * B := hraw
  have hfinal : L ≤ akbaryHambrookC3 * G * B := by
    calc
      L ≤ G *
          (2 / Real.pi * Real.log (Real.exp 1 * T * B) +
            2 * P * Real.sqrt P /
              (Real.pi * Real.log (4 / 3 : ℝ) * T)) := hpre
      _ ≤ G * (akbaryHambrookC3 * B) :=
        mul_le_mul_of_nonneg_left hcoefficient (by positivity)
      _ = akbaryHambrookC3 * G * B := by ring
  simpa only [L, G, B, P, K, mul_assoc] using hfinal

/-- Full consecutive-interval specialization of the maximal bilinear theorem. -/
theorem sum_weighted_bilinearProductCutoffMaximum_Ioc_le_c3
    (Q m0 M n0 N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (a b : ℕ → ℂ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ psi : primitiveCharacters q,
          bilinearProductCutoffMaximum
            ((m0 + M) * (n0 + N)) q psi.1
            (Finset.Ioc m0 (m0 + M)) (Finset.Ioc n0 (n0 + N)) a b) ≤
      akbaryHambrookC3 *
        Real.sqrt ((M : ℝ) + (Q : ℝ) ^ 2) *
        Real.sqrt ((N : ℝ) + (Q : ℝ) ^ 2) *
        Real.sqrt
          (∑ m ∈ Finset.Ioc m0 (m0 + M), ‖a m‖ ^ 2) *
        Real.sqrt
          (∑ n ∈ Finset.Ioc n0 (n0 + N), ‖b n‖ ^ 2) *
        Real.log
          (2 * (((m0 + M) * (n0 + N) : ℕ) : ℝ)) := by
  exact sum_weighted_bilinearProductCutoffMaximum_subset_Ioc_le_c3
    Q m0 M n0 N hM hN
      (Finset.Ioc m0 (m0 + M)) (Finset.Ioc n0 (n0 + N))
      (by rfl) (by rfl) a b

end

end BoundedGaps.Maynard
