import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.NumberTheory.ZetaValues

/-!
# Reciprocal-square packing on the unit circle

This file independently proves the strict packing estimate used on printed
p. 80 of MontgomeryVaughanHilbert1974. Centered representatives split the
off-diagonal points into two half-circles, and an injective binning compares
each side with the Basel series. See SEM-446.
-/

open scoped BigOperators
open Set Metric

noncomputable section

private def centeredRepresentative (z : UnitAddCircle) : ℝ :=
  AddCircle.equivIco 1 (-(1 / 2 : ℝ)) z

private lemma centeredRepresentative_mem (z : UnitAddCircle) :
    centeredRepresentative z ∈ Set.Ico (-(1 / 2 : ℝ)) (1 / 2) := by
  have hz := (AddCircle.equivIco 1 (-(1 / 2 : ℝ)) z).property
  constructor
  · exact hz.1
  · dsimp [centeredRepresentative]
    linarith [hz.2]

private lemma coe_centeredRepresentative (z : UnitAddCircle) :
    (centeredRepresentative z : UnitAddCircle) = z := by
  exact AddCircle.coe_equivIco

private lemma abs_centeredRepresentative_le (z : UnitAddCircle) :
    |centeredRepresentative z| ≤ (1 / 2 : ℝ) := by
  rw [abs_le]
  exact ⟨(centeredRepresentative_mem z).1,
    (centeredRepresentative_mem z).2.le⟩

private lemma norm_eq_abs_centeredRepresentative (z : UnitAddCircle) :
    ‖z‖ = |centeredRepresentative z| := by
  calc
    ‖z‖ = ‖(centeredRepresentative z : UnitAddCircle)‖ := by
      rw [coe_centeredRepresentative]
    _ = |centeredRepresentative z| :=
      (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).2 (by
        simpa using abs_centeredRepresentative_le z)

private lemma dist_eq_abs_centeredRepresentative_sub (a b : UnitAddCircle) :
    dist a b = |centeredRepresentative (b - a)| := by
  rw [dist_comm, dist_eq_norm, norm_eq_abs_centeredRepresentative]

private lemma dist_le_abs_centeredRepresentative_sub_sub
    (a b base : UnitAddCircle) :
    dist a b ≤
      |centeredRepresentative (a - base) - centeredRepresentative (b - base)| := by
  rw [dist_eq_norm]
  have hcoe :
      ((centeredRepresentative (a - base) - centeredRepresentative (b - base) : ℝ) :
          UnitAddCircle) = a - b := by
    change (centeredRepresentative (a - base) : UnitAddCircle) -
      (centeredRepresentative (b - base) : UnitAddCircle) = a - b
    rw [coe_centeredRepresentative, coe_centeredRepresentative]
    abel
  calc
    ‖a - b‖ =
        ‖((centeredRepresentative (a - base) - centeredRepresentative (b - base) : ℝ) :
          UnitAddCircle)‖ := by rw [hcoe]
    _ ≤ |centeredRepresentative (a - base) - centeredRepresentative (b - base)| := by
      change ‖(QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
          (centeredRepresentative (a - base)) -
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
          (centeredRepresentative (b - base))‖ ≤
            |centeredRepresentative (a - base) - centeredRepresentative (b - base)|
      rw [← map_sub]
      exact QuotientAddGroup.norm_mk_le_norm

private def packingBin {ι : Type*} (y : ι → UnitAddCircle) (i j : ι) (δ : ℝ) : ℕ :=
  ⌊|centeredRepresentative (y j - y i)| / δ⌋₊

private def packingKey {ι : Type*} (y : ι → UnitAddCircle) (i : ι) (δ : ℝ)
    (j : {j // j ≠ i}) : ℕ ⊕ ℕ :=
  if 0 ≤ centeredRepresentative (y j - y i) then
    Sum.inl (packingBin y i j δ)
  else
    Sum.inr (packingBin y i j δ)

private lemma packingKey_injective {ι : Type*} [Fintype ι]
    (y : ι → UnitAddCircle) (i : ι) {δ : ℝ} (hδ : 0 < δ)
    (hsep : Pairwise fun j k => δ ≤ dist (y j) (y k)) :
    Function.Injective (packingKey y i δ) := by
  intro a b hab
  by_contra hab'
  have hab_val : (a : ι) ≠ b := fun h => hab' (Subtype.ext h)
  have hsep_ab : δ ≤ dist (y a) (y b) := hsep hab_val
  let ca := centeredRepresentative (y a - y i)
  let cb := centeredRepresentative (y b - y i)
  have hmetric : dist (y a) (y b) ≤ |ca - cb| := by
    simpa [ca, cb] using dist_le_abs_centeredRepresentative_sub_sub (y a) (y b) (y i)
  have hfloor_bounds (c : ℝ) :
      ((⌊|c| / δ⌋₊ : ℕ) : ℝ) * δ ≤ |c| ∧
        |c| < (((⌊|c| / δ⌋₊ : ℕ) : ℝ) + 1) * δ := by
    constructor
    · exact (le_div_iff₀ hδ).mp (Nat.floor_le (div_nonneg (abs_nonneg c) hδ.le))
    · exact (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one (|c| / δ))
  by_cases ha : 0 ≤ ca <;> by_cases hb : 0 ≤ cb
  · have hn : packingBin y i a δ = packingBin y i b δ := by
      simpa [packingKey, ca, cb, ha, hb] using hab
    have hba := hfloor_bounds ca
    have hbb := hfloor_bounds cb
    have hca : |ca| = ca := abs_of_nonneg ha
    have hcb : |cb| = cb := abs_of_nonneg hb
    rw [hca] at hba
    rw [hcb] at hbb
    have hbin : (⌊|ca| / δ⌋₊ : ℝ) = (⌊|cb| / δ⌋₊ : ℝ) := by
      exact_mod_cast (show ⌊|ca| / δ⌋₊ = ⌊|cb| / δ⌋₊ by
        simpa [packingBin, ca, cb] using hn)
    rw [hca, hcb] at hbin
    rw [← hbin] at hbb
    have : |ca - cb| < δ := by rw [abs_lt]; constructor <;> nlinarith
    linarith
  · exfalso
    simp [packingKey, ca, cb, ha, hb] at hab
  · exfalso
    simp [packingKey, ca, cb, ha, hb] at hab
  · have hn : packingBin y i a δ = packingBin y i b δ := by
      simpa [packingKey, ca, cb, ha, hb] using hab
    have hba := hfloor_bounds ca
    have hbb := hfloor_bounds cb
    have hca : |ca| = -ca := abs_of_nonpos (le_of_not_ge ha)
    have hcb : |cb| = -cb := abs_of_nonpos (le_of_not_ge hb)
    rw [hca] at hba
    rw [hcb] at hbb
    have hbin : (⌊|ca| / δ⌋₊ : ℝ) = (⌊|cb| / δ⌋₊ : ℝ) := by
      exact_mod_cast (show ⌊|ca| / δ⌋₊ = ⌊|cb| / δ⌋₊ by
        simpa [packingBin, ca, cb] using hn)
    rw [hca, hcb] at hbin
    rw [← hbin] at hbb
    have : |ca - cb| < δ := by rw [abs_lt]; constructor <;> nlinarith
    linarith

private def packingMajorant (δ : ℝ) : ℕ ⊕ ℕ → ℝ :=
  Sum.elim (fun n => (1 / (n : ℝ) ^ 2) / δ ^ 2)
    (fun n => (1 / (n : ℝ) ^ 2) / δ ^ 2)

private lemma packingMajorant_term_eq (n : ℕ) (δ : ℝ) :
    (((n : ℝ) * δ) ^ 2)⁻¹ = (1 / (n : ℝ) ^ 2) / δ ^ 2 := by
  by_cases hn : (n : ℝ) = 0
  · simp [hn]
  by_cases hδ : δ = 0
  · simp [hδ]
  field_simp

private lemma hasSum_packingMajorant (δ : ℝ) :
    HasSum (packingMajorant δ) (Real.pi ^ 2 / (3 * δ ^ 2)) := by
  have hnat : HasSum (fun n : ℕ => (1 / (n : ℝ) ^ 2) / δ ^ 2)
      ((Real.pi ^ 2 / 6) / δ ^ 2) := hasSum_zeta_two.div_const (δ ^ 2)
  have hsum : HasSum (packingMajorant δ)
      ((Real.pi ^ 2 / 6) / δ ^ 2 + (Real.pi ^ 2 / 6) / δ ^ 2) := by
    apply HasSum.sum
    · change HasSum (fun n : ℕ => (1 / (n : ℝ) ^ 2) / δ ^ 2)
        ((Real.pi ^ 2 / 6) / δ ^ 2)
      exact hnat
    · change HasSum (fun n : ℕ => (1 / (n : ℝ) ^ 2) / δ ^ 2)
        ((Real.pi ^ 2 / 6) / δ ^ 2)
      exact hnat
  convert hsum using 1
  ring

private lemma packingTerm_le_majorant {ι : Type*} [Fintype ι]
    (y : ι → UnitAddCircle) (i : ι) {δ : ℝ} (hδ : 0 < δ)
    (hsep : Pairwise fun j k => δ ≤ dist (y j) (y k)) (j : {j // j ≠ i}) :
    (dist (y i) (y j) ^ 2)⁻¹ ≤ packingMajorant δ (packingKey y i δ j) := by
  let c := centeredRepresentative (y j - y i)
  let n := packingBin y i j δ
  have hsep_ij : δ ≤ dist (y i) (y j) := hsep (Ne.symm j.property)
  have hdist_pos : 0 < dist (y i) (y j) := hδ.trans_le hsep_ij
  have hdist : dist (y i) (y j) = |c| := by
    simpa [c] using dist_eq_abs_centeredRepresentative_sub (y i) (y j)
  have hn_le : (n : ℝ) * δ ≤ dist (y i) (y j) := by
    rw [hdist]
    exact (le_div_iff₀ hδ).mp
      (Nat.floor_le (div_nonneg (abs_nonneg c) hδ.le) :
        (n : ℝ) ≤ |c| / δ)
  have hratio : 1 ≤ |c| / δ := by
    apply (le_div_iff₀ hδ).2
    simpa [← hdist] using hsep_ij
  have hn_pos : 0 < n := by
    exact Nat.floor_pos.mpr hratio
  have hnδ_pos : 0 < (n : ℝ) * δ := mul_pos (by exact_mod_cast hn_pos) hδ
  have hsquare : ((n : ℝ) * δ) ^ 2 ≤ dist (y i) (y j) ^ 2 :=
    (sq_le_sq₀ hnδ_pos.le (dist_nonneg : 0 ≤ dist (y i) (y j))).2 hn_le
  have hinv : (dist (y i) (y j) ^ 2)⁻¹ ≤ (((n : ℝ) * δ) ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_pos hnδ_pos) hsquare
  rw [packingMajorant_term_eq] at hinv
  by_cases hc : 0 ≤ c
  · simpa [packingMajorant, packingKey, packingBin, c, n, hc] using hinv
  · simpa [packingMajorant, packingKey, packingBin, c, n, hc] using hinv

namespace BoundedGaps.Maynard

/-- The strict two-sided Basel packing bound for separated points on `ℝ/ℤ`.
This is the geometric estimate on p. 80 of MontgomeryVaughanHilbert1974. -/
theorem sum_inv_sq_circle_dist_lt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → UnitAddCircle) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ dist (y r) (y s)) (i : ι) :
    (∑ j ∈ Finset.univ.erase i, (dist (y i) (y j) ^ 2)⁻¹) <
      Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  have hpair : Pairwise fun j k => δ ≤ dist (y j) (y k) := fun j k hjk => hsep j k hjk
  let J := {j // j ≠ i}
  let f : J → ℝ := fun j => (dist (y i) (y j) ^ 2)⁻¹
  let e : J → ℕ ⊕ ℕ := packingKey y i δ
  let g : ℕ ⊕ ℕ → ℝ := packingMajorant δ
  let S : Finset (ℕ ⊕ ℕ) := Finset.univ.image e
  let project : ℕ ⊕ ℕ → ℕ := Sum.elim id id
  let T : Finset ℕ := insert 0 (S.image project)
  obtain ⟨m, hm⟩ := Finset.exists_notMem T
  have hm_zero : m ≠ 0 := by
    intro hm0
    apply hm
    simp [T, hm0]
  let missing : ℕ ⊕ ℕ := Sum.inl m
  have hmissing : missing ∉ S := by
    intro hmem
    apply hm
    apply Finset.mem_insert_of_mem
    apply Finset.mem_image.mpr
    exact ⟨missing, hmem, by simp [project, missing]⟩
  have hmissing_pos : 0 < g missing := by
    have hm_pos : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm_zero
    simp only [g, missing, packingMajorant, Sum.elim_inl]
    positivity
  have hsum_le : (∑ j : J, f j) ≤ ∑ j : J, g (e j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact packingTerm_le_majorant y i hδ hpair j
  have hreindex : (∑ j : J, g (e j)) = ∑ k ∈ S, g k := by
    symm
    exact Finset.sum_image (packingKey_injective y i hδ hpair).injOn
  have hfinite_lt : (∑ k ∈ S, g k) < ∑' k, g k := by
    have hproper : (∑ k ∈ S, g k) < ∑ k ∈ insert missing S, g k := by
      rw [Finset.sum_insert hmissing]
      linarith
    exact hproper.trans_le ((hasSum_packingMajorant δ).summable.sum_le_tsum
      (insert missing S) (by
        intro k hk
        cases k <;>
          simp only [g, packingMajorant, Sum.elim_inl, Sum.elim_inr] <;> positivity))
  calc
    (∑ j ∈ Finset.univ.erase i, (dist (y i) (y j) ^ 2)⁻¹) = ∑ j : J, f j := by
      change (∑ j ∈ Finset.univ.erase i, (dist (y i) (y j) ^ 2)⁻¹) =
        ∑ j : {j // j ≠ i}, (dist (y i) (y j) ^ 2)⁻¹
      exact Finset.sum_subtype (p := fun j => j ≠ i)
        (Finset.univ.erase i) (fun j => by simp)
        (fun j => (dist (y i) (y j) ^ 2)⁻¹)
    _ ≤ ∑ j : J, g (e j) := hsum_le
    _ = ∑ k ∈ S, g k := hreindex
    _ < ∑' k, g k := hfinite_lt
    _ = Real.pi ^ 2 / (3 * δ ^ 2) := (hasSum_packingMajorant δ).tsum_eq

/-- The non-strict circle-packing bound consumed by the Hilbert inequality. -/
theorem sum_inv_sq_circle_dist_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → UnitAddCircle) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ dist (y r) (y s)) (i : ι) :
    (∑ j ∈ Finset.univ.erase i, (dist (y i) (y j) ^ 2)⁻¹) ≤
      Real.pi ^ 2 / (3 * δ ^ 2) :=
  (sum_inv_sq_circle_dist_lt y hδ hsep i).le

end BoundedGaps.Maynard
