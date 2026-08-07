import BoundedGaps.BombieriVinogradov.Analytic.FiniteBilinearPerron

/-!
# Bilinear product-cutoff maxima

This file replaces the source's maximum over real product cutoffs by an exact
finite maximum over positive natural cutoffs. It proves both directions of the
real-endpoint bridge and lifts SEM-453's uniform fixed-cutoff estimate to that
maximum.

Source: `AkbaryHambrook2013v2`, Section 6, p. 17, proof of Lemma 6.1 through
the display immediately before equation (6.4). Semantic review: `SEM-454`.
-/

open MeasureTheory
open scoped Interval BigOperators

namespace BoundedGaps.Maynard

noncomputable section

/-- A finite bilinear sum truncated by a natural product endpoint. -/
def bilinearProductCutoffSum
    (k q : ℕ) (χ : DirichletCharacter ℂ q)
    (sm sn : Finset ℕ) (a b : ℕ → ℂ) : ℂ :=
  ∑ m ∈ sm, ∑ n ∈ sn.filter (fun n => m * n ≤ k),
    a m * b n * χ (m * n)

/-- The same finite bilinear sum truncated at an arbitrary real endpoint. -/
noncomputable def bilinearRealProductCutoffSum
    (y : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (sm sn : Finset ℕ) (a b : ℕ → ℂ) : ℂ :=
  ∑ m ∈ sm, ∑ n ∈ sn.filter (fun n => ((m * n : ℕ) : ℝ) ≤ y),
    a m * b n * χ (m * n)

/-- Maximum cutoff norm through `K`, totalized to zero at `K = 0`. -/
noncomputable def bilinearProductCutoffMaximum
    (K q : ℕ) (χ : DirichletCharacter ℂ q)
    (sm sn : Finset ℕ) (a b : ℕ → ℂ) : ℝ :=
  if hK : 1 ≤ K then
    (Finset.Icc 1 K).sup' (Finset.nonempty_Icc.mpr hK)
      (fun k => ‖bilinearProductCutoffSum k q χ sm sn a b‖)
  else 0

/-- A natural cutoff is represented exactly by the source's half-integer
real endpoint. -/
theorem bilinearProductCutoffSum_eq_realProductCutoffSum_add_half
    (k q : ℕ) (χ : DirichletCharacter ℂ q)
    (sm sn : Finset ℕ) (a b : ℕ → ℂ) :
    bilinearProductCutoffSum k q χ sm sn a b =
      bilinearRealProductCutoffSum ((k : ℝ) + 1 / 2) q χ sm sn a b := by
  classical
  unfold bilinearProductCutoffSum bilinearRealProductCutoffSum
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr
  · apply Finset.filter_congr
    intro n _hn
    constructor
    · intro hmn
      have hmnReal : ((m * n : ℕ) : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast hmn
      linarith
    · intro hmn
      by_contra hnot
      have hstep : k + 1 ≤ m * n := by omega
      have hstepReal : (k : ℝ) + 1 ≤ ((m * n : ℕ) : ℝ) := by
        exact_mod_cast hstep
      linarith
  · intro n _hn
    rfl

/-- Every product-cutoff maximum is nonnegative. -/
theorem bilinearProductCutoffMaximum_nonneg
    (K q : ℕ) (χ : DirichletCharacter ℂ q)
    (sm sn : Finset ℕ) (a b : ℕ → ℂ) :
    0 ≤ bilinearProductCutoffMaximum K q χ sm sn a b := by
  unfold bilinearProductCutoffMaximum
  split_ifs with hK
  · exact (norm_nonneg _).trans
      (Finset.le_sup'
        (fun k => ‖bilinearProductCutoffSum k q χ sm sn a b‖)
        (Finset.mem_Icc.mpr ⟨le_rfl, hK⟩))
  · exact le_rfl

/-- Every positive natural cutoff through `K` is bounded by the maximum. -/
theorem norm_bilinearProductCutoffSum_le_maximum
    (K q : ℕ) (χ : DirichletCharacter ℂ q)
    (sm sn : Finset ℕ) (a b : ℕ → ℂ)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 K) :
    ‖bilinearProductCutoffSum k q χ sm sn a b‖ ≤
      bilinearProductCutoffMaximum K q χ sm sn a b := by
  have hK : 1 ≤ K := (Finset.mem_Icc.mp hk).1.trans (Finset.mem_Icc.mp hk).2
  rw [bilinearProductCutoffMaximum, dif_pos hK]
  exact Finset.le_sup'
    (fun j => ‖bilinearProductCutoffSum j q χ sm sn a b‖) hk

/-- The finite maximum is attained at one of the source's real half-integer
endpoints. -/
theorem exists_norm_bilinearRealProductCutoffSum_eq_maximum
    {K q : ℕ} (hK : 0 < K) (χ : DirichletCharacter ℂ q)
    (sm sn : Finset ℕ) (a b : ℕ → ℂ) :
    ∃ y : ℝ,
      ‖bilinearRealProductCutoffSum y q χ sm sn a b‖ =
        bilinearProductCutoffMaximum K q χ sm sn a b := by
  let g : ℕ → ℝ := fun k => ‖bilinearProductCutoffSum k q χ sm sn a b‖
  have hKone : 1 ≤ K := hK
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image
    (Finset.Icc 1 K) g (Finset.nonempty_Icc.mpr hKone)
  refine ⟨(k : ℝ) + 1 / 2, ?_⟩
  rw [← bilinearProductCutoffSum_eq_realProductCutoffSum_add_half]
  rw [bilinearProductCutoffMaximum, dif_pos hKone]
  change g k = (Finset.Icc 1 K).sup' (Finset.nonempty_Icc.mpr hKone) g
  exact le_antisymm (Finset.le_sup' g hk) (Finset.sup'_le _ _ hmax)

/-- Under the source's positive-support and product-cap assumptions, every
real endpoint is bounded by the finite natural maximum. -/
theorem norm_bilinearRealProductCutoffSum_le_maximum
    {K q : ℕ} (hK : 0 < K) (χ : DirichletCharacter ℂ q)
    (sm sn : Finset ℕ) (a b : ℕ → ℂ)
    (hmPos : ∀ m ∈ sm, 0 < m)
    (hnPos : ∀ n ∈ sn, 0 < n)
    (hprod : ∀ m ∈ sm, ∀ n ∈ sn, m * n ≤ K)
    (y : ℝ) :
    ‖bilinearRealProductCutoffSum y q χ sm sn a b‖ ≤
      bilinearProductCutoffMaximum K q χ sm sn a b := by
  classical
  by_cases hy : y < 1
  · have hsumzero : bilinearRealProductCutoffSum y q χ sm sn a b = 0 := by
      unfold bilinearRealProductCutoffSum
      apply Finset.sum_eq_zero
      intro m hm
      apply Finset.sum_eq_zero
      intro n hn
      have hnmem := (Finset.mem_filter.mp hn).1
      have hncut := (Finset.mem_filter.mp hn).2
      have hmnpos : 0 < m * n := Nat.mul_pos (hmPos m hm) (hnPos n hnmem)
      have hmnone : (1 : ℝ) ≤ ((m * n : ℕ) : ℝ) := by
        exact_mod_cast hmnpos
      exfalso
      linarith
    rw [hsumzero, norm_zero]
    exact bilinearProductCutoffMaximum_nonneg K q χ sm sn a b
  have hyone : (1 : ℝ) ≤ y := le_of_not_gt hy
  rcases le_total y (K : ℝ) with hyK | hKy
  · let k : ℕ := ⌊y⌋₊
    have hkone : 1 ≤ k := (Nat.one_le_floor_iff y).2 hyone
    have hkK : k ≤ K := Nat.floor_le_of_le hyK
    have heq : bilinearRealProductCutoffSum y q χ sm sn a b =
        bilinearProductCutoffSum k q χ sm sn a b := by
      unfold bilinearRealProductCutoffSum bilinearProductCutoffSum
      apply Finset.sum_congr rfl
      intro m _hm
      apply Finset.sum_congr
      · apply Finset.filter_congr
        intro n _hn
        exact (Nat.le_floor_iff (zero_le_one.trans hyone)).symm
      · intro n _hn
        rfl
    rw [heq]
    exact norm_bilinearProductCutoffSum_le_maximum K q χ sm sn a b
      (Finset.mem_Icc.mpr ⟨hkone, hkK⟩)
  · have hreal : bilinearRealProductCutoffSum y q χ sm sn a b =
        ∑ m ∈ sm, ∑ n ∈ sn, a m * b n * χ (m * n) := by
      unfold bilinearRealProductCutoffSum
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.filter_eq_self.2]
      intro n hn
      have hcast : ((m * n : ℕ) : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast hprod m hm n hn
      exact hcast.trans hKy
    have hnat : bilinearProductCutoffSum K q χ sm sn a b =
        ∑ m ∈ sm, ∑ n ∈ sn, a m * b n * χ (m * n) := by
      unfold bilinearProductCutoffSum
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.filter_eq_self.2]
      exact fun n hn => hprod m hm n hn
    rw [hreal, ← hnat]
    exact norm_bilinearProductCutoffSum_le_maximum K q χ sm sn a b
      (Finset.mem_Icc.mpr ⟨hK, le_rfl⟩)

/-- SEM-453 lifted to the exact product-cutoff maximum. The estimate remains
unnormalized by `pi`. -/
theorem pi_mul_bilinearProductCutoffMaximum_le_integral_perronEnvelope_add
    {K q : ℕ} (hK : 0 < K) (χ : DirichletCharacter ℂ q)
    (sm sn : Finset ℕ) (a b : ℕ → ℂ) {T : ℝ} (hT : 0 < T)
    (hmPos : ∀ m ∈ sm, 0 < m)
    (hnPos : ∀ n ∈ sn, 0 < n)
    (hprod : ∀ m ∈ sm, ∀ n ∈ sn, m * n ≤ K) :
    Real.pi * bilinearProductCutoffMaximum K q χ sm sn a b ≤
      (∫ t in -T..T,
        perronEnvelope (Real.log (2 * (K : ℝ))) t *
          ‖∑ m ∈ sm, ∑ n ∈ sn,
            (a m * natLogTwist m t) * (b n * natLogTwist n t) *
              χ (m * n)‖) +
      2 * (K : ℝ) / (T * Real.log (4 / 3 : ℝ)) *
        (∑ m ∈ sm, ‖a m‖) * (∑ n ∈ sn, ‖b n‖) := by
  let s := Finset.Icc 1 K
  let f : ℕ → ℝ := fun k => ‖bilinearProductCutoffSum k q χ sm sn a b‖
  have hKone : 1 ≤ K := hK
  have hs : s.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hKone⟩⟩
  obtain ⟨k, hk, hmax⟩ := Finset.exists_mem_eq_sup' hs f
  have hkBounds := Finset.mem_Icc.mp hk
  have hkKReal : (k : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hkBounds.2
  have hprodReal :
      ∀ m ∈ sm, ∀ n ∈ sn, ((m * n : ℕ) : ℝ) ≤ (K : ℝ) := by
    intro m hm n hn
    exact_mod_cast hprod m hm n hn
  have hfixed :=
    pi_mul_norm_bilinearCutoff_le_integral_perronEnvelope_add
      q χ sm sn a b hkBounds.1 (by positivity) hkKReal hT
        hmPos hnPos hprodReal
  rw [bilinearProductCutoffMaximum, dif_pos hKone]
  change Real.pi * s.sup' hs f ≤ _
  rw [hmax]
  simpa only [f, bilinearProductCutoffSum] using hfixed

end

end BoundedGaps.Maynard
