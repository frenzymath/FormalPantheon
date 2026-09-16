import Mathlib.MeasureTheory.Integral.Bochner.Set
/-! # FiniteIntegralCover -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem setIntegral_le_finset_measureReal_mul_of_cover
    {X : Type*} [MeasurableSpace X]
    {ι : Type*} [DecidableEq ι]
    (μ : Measure X)
    (cells : Finset ι)
    (target : Set X)
    (cell : ι → Set X)
    (f : X -> Real)
    (upper : ι → Real)
    (htarget : MeasurableSet target)
    (hcellMeasurable : ∀ i ∈ cells, MeasurableSet (cell i))
    (hcellFinite : ∀ i ∈ cells, μ (cell i) ≠ ⊤)
    (hf : IntegrableOn f target μ)
    (hupperNonneg : ∀ i ∈ cells, 0 <= upper i)
    (hcover : target ⊆ ⋃ i ∈ cells, cell i)
    (hbound : ∀ i ∈ cells, ∀ x ∈ target ∩ cell i,
      f x <= upper i) :
    ∫ x in target, f x ∂μ <=
      ∑ i ∈ cells, μ.real (cell i) * upper i := by
  let majorant : X → Real := fun x ↦
    ∑ i ∈ cells, (cell i).indicator (fun _ ↦ upper i) x
  have htermIntegrable : ∀ i ∈ cells,
      Integrable ((cell i).indicator (fun _ ↦ upper i)) μ := by
    intro i hi
    exact (integrableOn_const (hcellFinite i hi)).integrable_indicator
      (hcellMeasurable i hi)
  have hmajorantIntegrable : Integrable majorant μ := by
    exact integrable_finsetSum cells htermIntegrable
  have hpointwise : target.indicator f ≤ majorant := by
    intro x
    by_cases hxtarget : x ∈ target
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover hxtarget)
      obtain ⟨hi, hxcell⟩ := Set.mem_iUnion.mp hxi
      rw [Set.indicator_of_mem hxtarget]
      calc
        f x ≤ upper i := hbound i hi x ⟨hxtarget, hxcell⟩
        _ = (cell i).indicator (fun _ ↦ upper i) x :=
          (Set.indicator_of_mem hxcell
            (fun _ : X ↦ upper i)).symm
        _ ≤ majorant x := by
          apply Finset.single_le_sum (s := cells) (f := fun j ↦
            (cell j).indicator (fun _ ↦ upper j) x)
          · intro j hj
            by_cases hxj : x ∈ cell j
            · simpa [Set.indicator_of_mem hxj] using hupperNonneg j hj
            · simp [Set.indicator_of_notMem hxj]
          · exact hi
    · rw [Set.indicator_of_notMem hxtarget]
      exact Finset.sum_nonneg fun i hi ↦ by
        by_cases hxi : x ∈ cell i
        · simpa [Set.indicator_of_mem hxi] using hupperNonneg i hi
        · simp [Set.indicator_of_notMem hxi]
  calc
    ∫ x in target, f x ∂μ = ∫ x, target.indicator f x ∂μ :=
      (integral_indicator (f := f) htarget).symm
    _ ≤ ∫ x, majorant x ∂μ :=
      integral_mono (hf.integrable_indicator htarget) hmajorantIntegrable hpointwise
    _ = ∑ i ∈ cells,
        ∫ x, (cell i).indicator (fun _ ↦ upper i) x ∂μ :=
      integral_finsetSum (f := fun i x ↦
        (cell i).indicator (fun _ ↦ upper i) x) cells htermIntegrable
    _ = ∑ i ∈ cells, μ.real (cell i) * upper i := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa [smul_eq_mul] using
        (integral_indicator_const (μ := μ) (upper i) (hcellMeasurable i hi))

theorem setIntegral_le_finset_setIntegral_of_cover
    {X : Type*} [MeasurableSpace X]
    {ι : Type*} [DecidableEq ι]
    (μ : Measure X) (cells : Finset ι)
    (target : Set X) (cell : ι → Set X) (f : X → Real)
    (htarget : MeasurableSet target)
    (hcellMeasurable : ∀ i ∈ cells, MeasurableSet (cell i))
    (hcellIntegrable : ∀ i ∈ cells, IntegrableOn f (cell i) μ)
    (hcellNonneg : ∀ i ∈ cells, ∀ x ∈ cell i, 0 <= f x)
    (hcover : target ⊆ ⋃ i ∈ cells, cell i) :
    ∫ x in target, f x ∂μ <=
      ∑ i ∈ cells, ∫ x in cell i, f x ∂μ := by
  let majorant : X → Real := fun x ↦
    ∑ i ∈ cells, (cell i).indicator f x
  have htargetIntegrable : IntegrableOn f target μ :=
    (integrableOn_finset_iUnion.2 hcellIntegrable).mono_set hcover
  have htermIntegrable : ∀ i ∈ cells,
      Integrable ((cell i).indicator f) μ := by
    intro i hi
    exact (hcellIntegrable i hi).integrable_indicator
      (hcellMeasurable i hi)
  have hmajorantIntegrable : Integrable majorant μ :=
    integrable_finsetSum cells htermIntegrable
  have hpointwise : target.indicator f ≤ majorant := by
    intro x
    by_cases hxtarget : x ∈ target
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover hxtarget)
      obtain ⟨hi, hxcell⟩ := Set.mem_iUnion.mp hxi
      rw [Set.indicator_of_mem hxtarget]
      calc
        f x = (cell i).indicator f x :=
          (Set.indicator_of_mem hxcell f).symm
        _ ≤ majorant x := by
          apply Finset.single_le_sum (s := cells) (f := fun j ↦
            (cell j).indicator f x)
          · intro j hj
            by_cases hxj : x ∈ cell j
            · simpa [Set.indicator_of_mem hxj] using
                hcellNonneg j hj x hxj
            · simp [Set.indicator_of_notMem hxj]
          · exact hi
    · rw [Set.indicator_of_notMem hxtarget]
      exact Finset.sum_nonneg fun i hi ↦ by
        by_cases hxi : x ∈ cell i
        · simpa [Set.indicator_of_mem hxi] using
            hcellNonneg i hi x hxi
        · simp [Set.indicator_of_notMem hxi]
  calc
    ∫ x in target, f x ∂μ =
        ∫ x, target.indicator f x ∂μ :=
      (integral_indicator (f := f) htarget).symm
    _ ≤ ∫ x, majorant x ∂μ :=
      integral_mono (htargetIntegrable.integrable_indicator htarget)
        hmajorantIntegrable hpointwise
    _ = ∑ i ∈ cells, ∫ x, (cell i).indicator f x ∂μ :=
      integral_finsetSum
        (f := fun i x ↦ (cell i).indicator f x) cells htermIntegrable
    _ = ∑ i ∈ cells, ∫ x in cell i, f x ∂μ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_indicator (hcellMeasurable i hi)

end

end PrimesRestrictedDigits
