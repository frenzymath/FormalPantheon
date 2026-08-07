import BoundedGaps.Maynard.ImprovedGPY.S2Moduli

noncomputable section

/-!
# Finite modulus-fiber multiplicities for S2

Maynard2013v3, in the error aggregation of `lmm:S2Expression1` (source lines
395--410), groups divisor-pair contributions by their CRT modulus. This file
records the exact finite fiber identity and a bound with explicit maximum fiber
cardinality.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def modulusFiberCard (I : Finset ι) (q : ι → ℕ) (m : ℕ) : ℕ :=
  (I.filter fun i => q i = m).card

theorem modulusFiberCard_le_card (I : Finset ι) (q : ι → ℕ) (m : ℕ) :
    modulusFiberCard I q m ≤ I.card := by
  exact Finset.card_filter_le _ _

theorem sum_comp_eq_sum_modulusFiberCard
    (I : Finset ι) (q : ι → ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ I, f (q i)) =
      ∑ m ∈ I.image q, (modulusFiberCard I q m : ℝ) * f m := by
  symm
  calc
    (∑ m ∈ I.image q, (modulusFiberCard I q m : ℝ) * f m) =
        ∑ m ∈ I.image q, ∑ i ∈ I with q i = m, f m := by
      apply Finset.sum_congr rfl
      intro m hm
      simp [modulusFiberCard, nsmul_eq_mul]
    _ = ∑ i ∈ I, f (q i) :=
      Finset.sum_fiberwise_of_maps_to'
        (fun i hi => Finset.mem_image_of_mem q hi) f

theorem sum_comp_le_fiberBound_mul_sum_image
    (I : Finset ι) (q : ι → ℕ) (f : ℕ → ℝ) (M : ℕ)
    (hM : ∀ m ∈ I.image q, modulusFiberCard I q m ≤ M)
    (hf : ∀ m ∈ I.image q, 0 ≤ f m) :
    (∑ i ∈ I, f (q i)) ≤ (M : ℝ) * ∑ m ∈ I.image q, f m := by
  rw [sum_comp_eq_sum_modulusFiberCard]
  calc
    (∑ m ∈ I.image q, (modulusFiberCard I q m : ℝ) * f m) ≤
        ∑ m ∈ I.image q, (M : ℝ) * f m := by
      apply Finset.sum_le_sum
      intro m hm
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hM m hm
      · exact hf m hm
    _ = (M : ℝ) * ∑ m ∈ I.image q, f m := by
      rw [Finset.mul_sum]

theorem sum_maxProgressionDiscrepancy_comp_le_fiberBound
    (x : ℕ) (I : Finset ι) (q : ι → ℕ) (M : ℕ)
    (hM : ∀ m ∈ I.image q, modulusFiberCard I q m ≤ M) :
    (∑ i ∈ I, maxProgressionDiscrepancy x (q i)) ≤
      (M : ℝ) * ∑ m ∈ I.image q, maxProgressionDiscrepancy x m := by
  apply sum_comp_le_fiberBound_mul_sum_image I q
    (maxProgressionDiscrepancy x) M hM
  intro m hm
  exact maxProgressionDiscrepancy_nonneg x m

theorem PrimeLevelWitness.sum_maxProgressionDiscrepancy_comp
    {θ A C : ℝ} {X₀ x : ℕ} (hw : PrimeLevelWitness θ A C X₀)
    (hx : X₀ ≤ x) (I : Finset ι) (q : ι → ℕ) (M : ℕ)
    (hM : ∀ m ∈ I.image q, modulusFiberCard I q m ≤ M)
    (hsubset : I.image q ⊆ Finset.Icc 1 (modulusCutoff θ x)) :
    (∑ i ∈ I, maxProgressionDiscrepancy x (q i)) ≤
      (M : ℝ) *
        (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
  have hfiber :=
    sum_maxProgressionDiscrepancy_comp_le_fiberBound x I q M hM
  have himage := hw.sum_maxProgressionDiscrepancy_subset hx (I.image q) hsubset
  exact hfiber.trans
    (mul_le_mul_of_nonneg_left himage (Nat.cast_nonneg M))

theorem hasPrimeLevel_sum_maxProgressionDiscrepancy_comp
    {θ : ℝ} (hlevel : hasPrimeLevel θ)
    (A : ℝ) (hA : 0 < A)
    (I : Finset ι) (q : ι → ℕ) (M : ℕ)
    (hM : ∀ m ∈ I.image q, modulusFiberCard I q m ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ∀ x : ℕ, X₀ ≤ x →
        I.image q ⊆ Finset.Icc 1 (modulusCutoff θ x) →
        (∑ i ∈ I, maxProgressionDiscrepancy x (q i)) ≤
          (M : ℝ) *
            (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
  obtain ⟨C, hC, X₀, hX₀, hbound⟩ :=
    hasPrimeLevel_sum_maxProgressionDiscrepancy_subset hlevel A hA
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro x hx hsubset
  have hfiber :=
    sum_maxProgressionDiscrepancy_comp_le_fiberBound x I q M hM
  have himage := hbound x hx (I.image q) hsubset
  exact hfiber.trans (mul_le_mul_of_nonneg_left himage (Nat.cast_nonneg M))

end BoundedGaps.Maynard
