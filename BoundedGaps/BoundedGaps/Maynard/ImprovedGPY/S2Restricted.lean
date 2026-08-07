import BoundedGaps.Maynard.ImprovedGPY.S2PrimeSupport
import BoundedGaps.Maynard.ImprovedGPY.S2Moduli

noncomputable section

/-!
# Restricted compatible pair-shift indices for S2

Maynard2013v3, in the proof of `lmm:S2Expression1` (source lines 351--360),
restricts the `m`-shift contribution to supported pairs with `d_m=e_m=1`.
This file records the exact finite restricted sum and its pair/shift index.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance outerPairDecidable (p : Prop) : Decidable p := Classical.propDecidable p

def compatiblePairShiftIndex
    (H : Finset ℕ) (D : Finset (H → ℕ)) :
    Finset (((H → ℕ) × (H → ℕ)) × H) := by
  classical
  exact (((D ×ˢ D).filter (fun de =>
      IsCrossCoordinateCoprime H de.1 de.2)).product Finset.univ).filter
    (fun deh => deh.1.1 deh.2 = 1 ∧ deh.1.2 deh.2 = 1)

def compatiblePairShiftModulus
    (H : Finset ℕ) (W : ℕ)
    (i : (((H → ℕ) × (H → ℕ)) × H)) : ℕ :=
  divisorPairModulus H W i.1.1 i.1.2

def restrictedCompatiblePairShiftInner
    {H : Finset ℕ} {R W v N : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e)
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ h ∈ H.attach,
    if d h = 1 ∧ e h = 1 then
      (shiftedPrimeProgressionCount N (divisorPairModulus H W d e)
        (divisorPairCrtResidue H R W v d e hd he hcross) h.1 : ℝ) *
        (lambda d * lambda e)
    else 0

def restrictedCompatiblePairShiftMainInner
    {H : Finset ℕ} {R W v N : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e)
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ h ∈ H.attach,
    if d h = 1 ∧ e h = 1 then
      shiftedPrimeProgressionIntervalMainTerm N
        (divisorPairModulus H W d e)
        (divisorPairCrtResidue H R W v d e hd he hcross) h.1 *
        (lambda d * lambda e)
    else 0

def restrictedCompatiblePairShiftErrorInner
    {H : Finset ℕ} {R W v N : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e)
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ h ∈ H.attach,
    if d h = 1 ∧ e h = 1 then
      shiftedPrimeProgressionIntervalError N
        (divisorPairModulus H W d e)
        (divisorPairCrtResidue H R W v d e hd he hcross) h.1 *
        (lambda d * lambda e)
    else 0

def compatiblePairRestrictedMainOuter
    (H : Finset ℕ) (D : Finset (H → ℕ)) (R W v N : ℕ)
    (lambda : (H → ℕ) → ℝ)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) : ℝ :=
  ∑ d : D, ∑ e : D.filter
    (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
      restrictedCompatiblePairShiftMainInner
        (v := v) (N := N) (hD d.1 d.2)
        (hD e.1 (Finset.mem_filter.mp e.2).1)
        (show IsCrossCoordinateCoprime H d.1 e.1 from
          (Finset.mem_filter.mp e.2).2) lambda

def compatiblePairRestrictedErrorOuter
    (H : Finset ℕ) (D : Finset (H → ℕ)) (R W v N : ℕ)
    (lambda : (H → ℕ) → ℝ)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) : ℝ :=
  ∑ d : D, ∑ e : D.filter
    (fun e : H → ℕ => IsCrossCoordinateCoprime H d.1 e),
      restrictedCompatiblePairShiftErrorInner
        (v := v) (N := N) (hD d.1 d.2)
        (hD e.1 (Finset.mem_filter.mp e.2).1)
        (show IsCrossCoordinateCoprime H d.1 e.1 from
          (Finset.mem_filter.mp e.2).2) lambda

theorem primeWeightedPairInnerSum_eq_restricted
    {H : Finset ℕ} {R W v N : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e)
    (hRN : R ≤ N) (lambda : (H → ℕ) → ℝ) :
    primeWeightedPairInnerSum H v W N lambda d e =
      restrictedCompatiblePairShiftInner (v := v) (N := N) hd he hcross lambda := by
  classical
  rw [primeWeightedPairInnerSum_eq_shiftedPrimeProgressionCounts
    hd he hcross lambda]
  unfold restrictedCompatiblePairShiftInner
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hde : d h = 1 ∧ e h = 1
  · simp [hde]
  · have hzero := shiftedPrimeProgressionCount_eq_zero_of_coordinate_ne_one
      (v := v) hd he hcross hRN h (not_and_or.mp hde)
    simp [hde, hzero]

theorem primeWeightedPairInnerSum_eq_restrictedMain_addError
    {H : Finset ℕ} {R W v N : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e)
    (hRN : R ≤ N) (lambda : (H → ℕ) → ℝ) :
    primeWeightedPairInnerSum H v W N lambda d e =
      restrictedCompatiblePairShiftMainInner (v := v) (N := N) hd he hcross lambda +
        restrictedCompatiblePairShiftErrorInner (v := v) (N := N) hd he hcross lambda := by
  rw [primeWeightedPairInnerSum_eq_restricted hd he hcross hRN lambda]
  unfold restrictedCompatiblePairShiftInner
    restrictedCompatiblePairShiftMainInner restrictedCompatiblePairShiftErrorInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hred : d h = 1 ∧ e h = 1
  · simp [hred]
    rw [shiftedPrimeProgressionCount_interval_decomposition]
    ring
  · simp only [hred, if_false, zero_add]

theorem compatiblePrimeWeightedPairSum_eq_restrictedOuterMain_addError
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W v N : ℕ}
    {lambda : (H → ℕ) → ℝ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hRN : R ≤ N) :
    compatiblePrimeWeightedPairSum H D v W N lambda =
      compatiblePairRestrictedMainOuter H D R W v N lambda hD +
        compatiblePairRestrictedErrorOuter H D R W v N lambda hD := by
  classical
  unfold compatiblePrimeWeightedPairSum
    compatiblePairRestrictedMainOuter compatiblePairRestrictedErrorOuter
  rw [← Finset.sum_attach]
  rw [Finset.univ_eq_attach]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_filter]
  rw [Finset.univ_eq_attach]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_attach]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have heData : e.1 ∈ D ∧ IsCrossCoordinateCoprime H d.1 e.1 :=
    Finset.mem_filter.mp e.2
  have heD := heData.1
  have hcross : IsCrossCoordinateCoprime H d.1 e.1 := heData.2
  rw [primeWeightedPairInnerSum_eq_restrictedMain_addError
    (hD d.1 d.2) (hD e.1 heD) hcross hRN lambda]

theorem compatiblePairShiftModulus_mem_supported
    {H : Finset ℕ} {D : Finset (H → ℕ)} {W : ℕ}
    {i : (((H → ℕ) × (H → ℕ)) × H)}
    (hi : i ∈ compatiblePairShiftIndex H D) :
    compatiblePairShiftModulus H W i ∈ supportedDivisorPairModuli H D W := by
  classical
  unfold compatiblePairShiftModulus
  obtain ⟨hprod, _⟩ := Finset.mem_filter.mp hi
  obtain ⟨hpairFiltered, _⟩ := Finset.mem_product.mp hprod
  obtain ⟨hpair, _⟩ := Finset.mem_filter.mp hpairFiltered
  obtain ⟨hd, he⟩ := Finset.mem_product.mp hpair
  exact divisorPairModulus_mem_supportedDivisorPairModuli hd he

theorem compatiblePairShiftModulus_image_subset_cutoff
    {H : Finset ℕ} {D : Finset (H → ℕ)} {θ : ℝ} {x R W : ℕ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcut : W * R * R ≤ modulusCutoff θ x) :
    (compatiblePairShiftIndex H D).image
        (compatiblePairShiftModulus H W) ⊆
      Finset.Icc 1 (modulusCutoff θ x) := by
  classical
  intro q hq
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
  exact supportedDivisorPairModuli_subset_cutoff hW hD hcut
    (compatiblePairShiftModulus_mem_supported hi)

end BoundedGaps.Maynard
