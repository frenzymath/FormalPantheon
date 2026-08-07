import BoundedGaps.Maynard.ImprovedGPY.S2Restricted
import BoundedGaps.Maynard.ImprovedGPY.S2Multiplicity

noncomputable section

/-!
# Conditional distribution bound for the concrete S2 index

Maynard2013v3, in the error estimate of `lmm:S2Expression1` (source lines
353--369), groups the compatible divisor-pair errors by their CRT modulus.
This file instantiates the generic indexed level-of-distribution theorem for
the exact pair/shift index, retaining the fiber cap as an explicit hypothesis.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def compatiblePairShiftWeightedDiscrepancySum
    (H : Finset ℕ) (D : Finset (H → ℕ)) (W x : ℕ)
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ i ∈ compatiblePairShiftIndex H D,
    |lambda i.1.1 * lambda i.1.2| *
      maxProgressionDiscrepancy x (compatiblePairShiftModulus H W i)

theorem compatiblePairShiftWeightedDiscrepancySum_le
    {H : Finset ℕ} {D : Finset (H → ℕ)} {W x : ℕ}
    {lambda : (H → ℕ) → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hbound : ∀ d ∈ D, |lambda d| ≤ L) :
    compatiblePairShiftWeightedDiscrepancySum H D W x lambda ≤
      L ^ 2 *
        (∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy x (compatiblePairShiftModulus H W i)) := by
  classical
  unfold compatiblePairShiftWeightedDiscrepancySum
  have hterm : ∀ i ∈ compatiblePairShiftIndex H D,
      |lambda i.1.1 * lambda i.1.2| ≤ L ^ 2 := by
    intro i hi
    obtain ⟨hiProd, _⟩ := Finset.mem_filter.mp hi
    obtain ⟨hiPair, _⟩ := Finset.mem_product.mp hiProd
    obtain ⟨hiPairD, _⟩ := Finset.mem_filter.mp hiPair
    obtain ⟨hdD, heD⟩ := Finset.mem_product.mp hiPairD
    rw [abs_mul]
    calc
      |lambda i.1.1| * |lambda i.1.2| ≤ L * L :=
        mul_le_mul (hbound i.1.1 hdD) (hbound i.1.2 heD)
          (abs_nonneg _) hL
      _ = L ^ 2 := by ring
  calc
    (∑ i ∈ compatiblePairShiftIndex H D,
        |lambda i.1.1 * lambda i.1.2| *
          maxProgressionDiscrepancy x (compatiblePairShiftModulus H W i)) ≤
        ∑ i ∈ compatiblePairShiftIndex H D,
          L ^ 2 * maxProgressionDiscrepancy x
            (compatiblePairShiftModulus H W i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hterm i hi)
        (maxProgressionDiscrepancy_nonneg x
          (compatiblePairShiftModulus H W i))
    _ = L ^ 2 *
        (∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy x (compatiblePairShiftModulus H W i)) := by
      rw [Finset.mul_sum]

def compatiblePairShiftWeightedIntervalErrorSum
    (H : Finset ℕ) (D : Finset (H → ℕ)) (W N : ℕ)
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ i ∈ compatiblePairShiftIndex H D,
    |lambda i.1.1 * lambda i.1.2| *
      maxIntervalError N (compatiblePairShiftModulus H W i)

theorem compatiblePairShiftWeightedIntervalErrorSum_le
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W N : ℕ}
    {lambda : (H → ℕ) → ℝ} {L : ℝ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hN : 0 < N) (hL : 0 ≤ L)
    (hbound : ∀ d ∈ D, |lambda d| ≤ L) :
    compatiblePairShiftWeightedIntervalErrorSum H D W N lambda ≤
      L ^ 2 *
        ((compatiblePairShiftIndex H D).card : ℝ) +
      L ^ 2 *
        (∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy (2 * N - 1)
            (compatiblePairShiftModulus H W i)) +
      L ^ 2 *
        (∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy (N - 1)
            (compatiblePairShiftModulus H W i)) := by
  classical
  unfold compatiblePairShiftWeightedIntervalErrorSum
  have hterm : ∀ i ∈ compatiblePairShiftIndex H D,
      |lambda i.1.1 * lambda i.1.2| ≤ L ^ 2 := by
    intro i hi
    obtain ⟨hiProd, _⟩ := Finset.mem_filter.mp hi
    obtain ⟨hiPair, _⟩ := Finset.mem_product.mp hiProd
    obtain ⟨hiPairD, _⟩ := Finset.mem_filter.mp hiPair
    obtain ⟨hdD, heD⟩ := Finset.mem_product.mp hiPairD
    rw [abs_mul]
    calc
      |lambda i.1.1| * |lambda i.1.2| ≤ L * L :=
        mul_le_mul (hbound i.1.1 hdD) (hbound i.1.2 heD)
          (abs_nonneg _) hL
      _ = L ^ 2 := by ring
  have herror_nonneg : ∀ q : ℕ, 0 ≤ maxIntervalError N q := by
    intro q
    by_cases hq : 0 < q
    · rw [maxIntervalError, dif_pos hq]
      obtain ⟨a, ha⟩ := coprimeResidues_nonempty hq
      have hsup : 0 ≤ (coprimeResidues q).sup'
          (coprimeResidues_nonempty hq) (intervalProgressionDiscrepancy N q) :=
        (abs_nonneg _).trans (Finset.le_sup'
          (intervalProgressionDiscrepancy N q) ha)
      linarith
    · simp [maxIntervalError, hq]
  calc
    (∑ i ∈ compatiblePairShiftIndex H D,
        |lambda i.1.1 * lambda i.1.2| *
          maxIntervalError N (compatiblePairShiftModulus H W i)) ≤
        ∑ i ∈ compatiblePairShiftIndex H D,
          L ^ 2 * (1 + maxProgressionDiscrepancy (2 * N - 1)
            (compatiblePairShiftModulus H W i) +
            maxProgressionDiscrepancy (N - 1)
              (compatiblePairShiftModulus H W i)) := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hiProd, _⟩ := Finset.mem_filter.mp hi
      obtain ⟨hiPair, _⟩ := Finset.mem_product.mp hiProd
      obtain ⟨hiPairD, _⟩ := Finset.mem_filter.mp hiPair
      obtain ⟨hdD, heD⟩ := Finset.mem_product.mp hiPairD
      have hq : 0 < compatiblePairShiftModulus H W i := by
        exact divisorPairModulus_pos hW (hD i.1.1 hdD) (hD i.1.2 heD)
      have herr := maxIntervalError_le_global_sum hN hq
      have hcoef := hterm i hi
      calc
        |lambda i.1.1 * lambda i.1.2| *
            maxIntervalError N (compatiblePairShiftModulus H W i) ≤
            L ^ 2 * maxIntervalError N (compatiblePairShiftModulus H W i) :=
          mul_le_mul_of_nonneg_right hcoef (herror_nonneg _)
        _ ≤ L ^ 2 * (1 + maxProgressionDiscrepancy (2 * N - 1)
              (compatiblePairShiftModulus H W i) +
              maxProgressionDiscrepancy (N - 1)
                (compatiblePairShiftModulus H W i)) :=
          mul_le_mul_of_nonneg_left herr (sq_nonneg L)
    _ = L ^ 2 * ((compatiblePairShiftIndex H D).card : ℝ) +
        L ^ 2 *
          (∑ i ∈ compatiblePairShiftIndex H D,
            maxProgressionDiscrepancy (2 * N - 1)
              (compatiblePairShiftModulus H W i)) +
        L ^ 2 *
          (∑ i ∈ compatiblePairShiftIndex H D,
            maxProgressionDiscrepancy (N - 1)
              (compatiblePairShiftModulus H W i)) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.mul_sum]
      ring

theorem compatiblePairShiftModulus_fiberCard_le_trivial
    {H : Finset ℕ} {D : Finset (H → ℕ)} {W m : ℕ} :
    modulusFiberCard (compatiblePairShiftIndex H D)
        (compatiblePairShiftModulus H W) m ≤
      D.card * D.card * H.card := by
  classical
  calc
    modulusFiberCard (compatiblePairShiftIndex H D)
        (compatiblePairShiftModulus H W) m ≤
        (compatiblePairShiftIndex H D).card :=
      modulusFiberCard_le_card _ _ _
    _ ≤ (((D ×ˢ D).filter (fun de : (H → ℕ) × (H → ℕ) =>
          IsCrossCoordinateCoprime H de.1 de.2)).product Finset.univ).card := by
      unfold compatiblePairShiftIndex
      exact Finset.card_filter_le _ _
    _ = ((D ×ˢ D).filter (fun de : (H → ℕ) × (H → ℕ) =>
          IsCrossCoordinateCoprime H de.1 de.2)).card * Finset.univ.card :=
      Finset.card_product _ _
    _ ≤ (D ×ˢ D).card * Finset.univ.card := by
      exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ = D.card * D.card * H.card := by
      rw [Finset.card_product]
      rw [Finset.card_univ, Fintype.card_coe]

theorem PrimeLevelWitness.sum_maxProgressionDiscrepancy_compatiblePairShiftModulus
    {θ A C : ℝ} {X₀ x : ℕ} (hw : PrimeLevelWitness θ A C X₀)
    (hx : X₀ ≤ x)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W : ℕ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (M : ℕ)
    (hM : ∀ m ∈
      (compatiblePairShiftIndex H D).image (compatiblePairShiftModulus H W),
      modulusFiberCard (compatiblePairShiftIndex H D)
        (compatiblePairShiftModulus H W) m ≤ M)
    (hcut : W * R * R ≤ modulusCutoff θ x) :
    (∑ i ∈ compatiblePairShiftIndex H D,
      maxProgressionDiscrepancy x (compatiblePairShiftModulus H W i)) ≤
      (M : ℝ) *
        (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
  apply hw.sum_maxProgressionDiscrepancy_comp hx
    (compatiblePairShiftIndex H D) (compatiblePairShiftModulus H W) M hM
  exact compatiblePairShiftModulus_image_subset_cutoff hW hD hcut

theorem PrimeLevelWitness.sum_maxProgressionDiscrepancy_compatiblePairShiftModulus_trivial
    {θ A C : ℝ} {X₀ x : ℕ} (hw : PrimeLevelWitness θ A C X₀)
    (hx : X₀ ≤ x)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W : ℕ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcut : W * R * R ≤ modulusCutoff θ x) :
    (∑ i ∈ compatiblePairShiftIndex H D,
      maxProgressionDiscrepancy x (compatiblePairShiftModulus H W i)) ≤
      (D.card * D.card * H.card : ℝ) *
        (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
  simpa only [Nat.cast_mul] using
    (hw.sum_maxProgressionDiscrepancy_compatiblePairShiftModulus hx hW hD
      (D.card * D.card * H.card) (by
        intro m hm
        exact compatiblePairShiftModulus_fiberCard_le_trivial
          (H := H) (D := D) (W := W) (m := m)) hcut)

theorem hasPrimeLevel_sum_maxProgressionDiscrepancy_compatiblePairShiftModulus
    {θ : ℝ} (hlevel : hasPrimeLevel θ)
    (A : ℝ) (hA : 0 < A)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W : ℕ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (M : ℕ)
    (hM : ∀ m ∈
      (compatiblePairShiftIndex H D).image (compatiblePairShiftModulus H W),
      modulusFiberCard (compatiblePairShiftIndex H D)
        (compatiblePairShiftModulus H W) m ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ∀ x : ℕ, X₀ ≤ x →
        W * R * R ≤ modulusCutoff θ x →
        (∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy x (compatiblePairShiftModulus H W i)) ≤
          (M : ℝ) *
            (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
  obtain ⟨C, hC, X₀, hX₀, hbound⟩ :=
    hasPrimeLevel_sum_maxProgressionDiscrepancy_comp hlevel A hA
      (compatiblePairShiftIndex H D) (compatiblePairShiftModulus H W) M hM
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro x hx hcut
  apply hbound x hx
  exact compatiblePairShiftModulus_image_subset_cutoff hW hD hcut

theorem hasPrimeLevel_sum_maxProgressionDiscrepancy_compatiblePairShiftModulus_trivial
    {θ : ℝ} (hlevel : hasPrimeLevel θ)
    (A : ℝ) (hA : 0 < A)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W : ℕ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ∀ x : ℕ, X₀ ≤ x →
        W * R * R ≤ modulusCutoff θ x →
        (∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy x (compatiblePairShiftModulus H W i)) ≤
          (D.card * D.card * H.card : ℝ) *
            (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
  simpa only [Nat.cast_mul] using
    (hasPrimeLevel_sum_maxProgressionDiscrepancy_compatiblePairShiftModulus
      hlevel A hA hW hD (D.card * D.card * H.card) (by
        intro m hm
        exact compatiblePairShiftModulus_fiberCard_le_trivial
          (H := H) (D := D) (W := W) (m := m)))

theorem hasPrimeLevel_compatiblePairShiftWeightedDiscrepancySum_trivial
    {θ : ℝ} (hlevel : hasPrimeLevel θ)
    (A : ℝ) (hA : 0 < A)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W : ℕ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (lambda : (H → ℕ) → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hbound : ∀ d ∈ D, |lambda d| ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ∀ x : ℕ, X₀ ≤ x →
        W * R * R ≤ modulusCutoff θ x →
        compatiblePairShiftWeightedDiscrepancySum H D W x lambda ≤
          (L ^ 2 * (D.card * D.card * H.card : ℝ)) *
            (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
  obtain ⟨C, hC, X₀, hX₀, hdist⟩ :=
    hasPrimeLevel_sum_maxProgressionDiscrepancy_compatiblePairShiftModulus_trivial
      hlevel A hA hW hD
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro x hx hcut
  calc
    compatiblePairShiftWeightedDiscrepancySum H D W x lambda ≤
        L ^ 2 *
          (∑ i ∈ compatiblePairShiftIndex H D,
            maxProgressionDiscrepancy x (compatiblePairShiftModulus H W i)) :=
      compatiblePairShiftWeightedDiscrepancySum_le hL hbound
    _ ≤ L ^ 2 *
        ((D.card * D.card * H.card : ℝ) *
          (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A)) :=
      mul_le_mul_of_nonneg_left (hdist x hx hcut) (sq_nonneg L)
    _ = (L ^ 2 * (D.card * D.card * H.card : ℝ)) *
          (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
      ring

theorem hasPrimeLevel_compatiblePairShiftWeightedIntervalErrorSum_le
    {θ : ℝ} (hlevel : hasPrimeLevel θ)
    (A : ℝ) (hA : 0 < A)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W : ℕ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (lambda : (H → ℕ) → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hbound : ∀ d ∈ D, |lambda d| ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ∀ N : ℕ, 0 < N → X₀ ≤ N - 1 → X₀ ≤ 2 * N - 1 →
        W * R * R ≤ modulusCutoff θ (N - 1) →
        W * R * R ≤ modulusCutoff θ (2 * N - 1) →
        compatiblePairShiftWeightedIntervalErrorSum H D W N lambda ≤
          L ^ 2 * (D.card * D.card * H.card : ℝ) +
          L ^ 2 * ((D.card * D.card * H.card : ℝ) *
            (C * ((2 * N - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((2 * N - 1 : ℕ) : ℝ)) A)) +
          L ^ 2 * ((D.card * D.card * H.card : ℝ) *
            (C * ((N - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((N - 1 : ℕ) : ℝ)) A)) := by
  classical
  obtain ⟨C, hC, X₀, hX₀, hdist⟩ :=
    hasPrimeLevel_sum_maxProgressionDiscrepancy_compatiblePairShiftModulus_trivial
      hlevel A hA hW hD
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro N hN hXlower hXupper hcutlower hcutupper
  have hinterval := compatiblePairShiftWeightedIntervalErrorSum_le
    hW hD hN hL hbound
  have hupper := hdist (2 * N - 1) hXupper hcutupper
  have hlower := hdist (N - 1) hXlower hcutlower
  have hcardNat : (compatiblePairShiftIndex H D).card ≤
      D.card * D.card * H.card := by
    calc
      (compatiblePairShiftIndex H D).card ≤
          (((D ×ˢ D).filter (fun de : (H → ℕ) × (H → ℕ) =>
            IsCrossCoordinateCoprime H de.1 de.2)).product Finset.univ).card := by
        unfold compatiblePairShiftIndex
        exact Finset.card_filter_le _ _
      _ = ((D ×ˢ D).filter (fun de : (H → ℕ) × (H → ℕ) =>
          IsCrossCoordinateCoprime H de.1 de.2)).card * Finset.univ.card :=
        Finset.card_product _ _
      _ ≤ (D ×ˢ D).card * Finset.univ.card := by
        exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
      _ = D.card * D.card * H.card := by
        rw [Finset.card_product]
        rw [Finset.card_univ, Fintype.card_coe]
  have hcard : ((compatiblePairShiftIndex H D).card : ℝ) ≤
      (D.card * D.card * H.card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    compatiblePairShiftWeightedIntervalErrorSum H D W N lambda ≤
        L ^ 2 * ((compatiblePairShiftIndex H D).card : ℝ) +
          L ^ 2 *
            (∑ i ∈ compatiblePairShiftIndex H D,
              maxProgressionDiscrepancy (2 * N - 1)
                (compatiblePairShiftModulus H W i)) +
          L ^ 2 *
            (∑ i ∈ compatiblePairShiftIndex H D,
              maxProgressionDiscrepancy (N - 1)
                (compatiblePairShiftModulus H W i)) := hinterval
    _ ≤ L ^ 2 * (D.card * D.card * H.card : ℝ) +
          L ^ 2 *
            (∑ i ∈ compatiblePairShiftIndex H D,
              maxProgressionDiscrepancy (2 * N - 1)
                (compatiblePairShiftModulus H W i)) +
          L ^ 2 *
            (∑ i ∈ compatiblePairShiftIndex H D,
              maxProgressionDiscrepancy (N - 1)
                (compatiblePairShiftModulus H W i)) := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hcard (sq_nonneg L)) le_rfl) le_rfl
    _ ≤ L ^ 2 * (D.card * D.card * H.card : ℝ) +
          L ^ 2 * ((D.card * D.card * H.card : ℝ) *
            (C * ((2 * N - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((2 * N - 1 : ℕ) : ℝ)) A)) +
          L ^ 2 * ((D.card * D.card * H.card : ℝ) *
            (C * ((N - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((N - 1 : ℕ) : ℝ)) A)) := by
      exact add_le_add (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hupper (sq_nonneg L)))
        (mul_le_mul_of_nonneg_left hlower (sq_nonneg L))

end BoundedGaps.Maynard
