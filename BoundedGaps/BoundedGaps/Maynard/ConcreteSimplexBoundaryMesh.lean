import BoundedGaps.Maynard.ConcreteSimplexUnitBoundary

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

/-! Finite mesh control for the equality face in the SEM-221 simplex squeeze. -/

def boundaryGridIndexEncoding {H : Finset ℕ} (h0 : H) (j : H → ℕ) :
    ℕ × ({i : H // i ≠ h0} → ℕ) :=
  (∑ i : H, j i, fun i => j i.1)

def boundaryGridEncodingTarget {H : Finset ℕ} (h0 : H) (m : ℕ) :
    Finset (ℕ × ({i : H // i ≠ h0} → ℕ)) :=
  Finset.Icc (m - Fintype.card H) m ×ˢ
    Fintype.piFinset (fun _ : {i : H // i ≠ h0} => Finset.range m)

theorem boundaryGridIndexEncoding_injective {H : Finset ℕ} (h0 : H) :
    Function.Injective (boundaryGridIndexEncoding h0) := by
  intro j k hjk
  funext i
  by_cases hi : i = h0
  · subst i
    have hsum : (∑ x : H, j x) = ∑ x : H, k x :=
      congrArg (fun z => z.1) hjk
    have hrest : (fun x : {i : H // i ≠ h0} => j x.1) =
        fun x => k x.1 := congrArg (fun z => z.2) hjk
    have herase : (∑ x ∈ (Finset.univ : Finset H).erase h0, j x) =
        ∑ x ∈ (Finset.univ : Finset H).erase h0, k x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact congr_fun hrest ⟨x, Finset.ne_of_mem_erase hx⟩
    have hj := Finset.sum_erase_add (Finset.univ : Finset H) j
      (Finset.mem_univ h0)
    have hk := Finset.sum_erase_add (Finset.univ : Finset H) k
      (Finset.mem_univ h0)
    omega
  · have hrest : (fun x : {i : H // i ≠ h0} => j x.1) =
        fun x => k x.1 := congrArg (fun z => z.2) hjk
    exact congr_fun hrest ⟨i, hi⟩

theorem sum_fractionalGridLower_eq {H : Finset ℕ} (m : ℕ) (j : H → ℕ) :
    (∑ h : H, fractionalGridLower m j h) =
      ((∑ h : H, j h : ℕ) : ℝ) / m := by
  unfold fractionalGridLower
  rw [← Finset.sum_div]
  norm_cast

theorem sum_fractionalGridUpper_eq {H : Finset ℕ} (m : ℕ) (j : H → ℕ) :
    (∑ h : H, fractionalGridUpper m j h) =
      (((∑ h : H, j h : ℕ) + Fintype.card H : ℕ) : ℝ) / m := by
  unfold fractionalGridUpper
  rw [← Finset.sum_div]
  congr 1
  push_cast
  simp [Finset.sum_add_distrib, Finset.sum_const]

theorem boundary_encoding_mapsTo {H : Finset ℕ} (h0 : H)
    {m : ℕ} (hm : 0 < m) :
    Set.MapsTo (boundaryGridIndexEncoding h0)
      (fractionalSimplexBoundaryGridIndex H m : Set (H → ℕ))
      (boundaryGridEncodingTarget h0 m : Set
        (ℕ × ({i : H // i ≠ h0} → ℕ))) := by
  intro j hj
  have hjData := Finset.mem_filter.mp hj
  have hsum := hjData.2
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hsumLeReal : (((∑ h : H, j h : ℕ) : ℕ) : ℝ) ≤ m := by
    rw [sum_fractionalGridLower_eq] at hsum
    exact (div_le_one hmReal).mp hsum.1
  have hsumLe : (∑ h : H, j h) ≤ m := by exact_mod_cast hsumLeReal
  have hsumAddGeReal : (m : ℝ) ≤
      ((∑ h : H, j h : ℕ) + Fintype.card H : ℕ) := by
    rw [sum_fractionalGridUpper_eq] at hsum
    have := (le_div_iff₀ hmReal).mp hsum.2
    simpa using this
  have hsumAddGe : m ≤ (∑ h : H, j h) + Fintype.card H := by
    exact_mod_cast hsumAddGeReal
  change boundaryGridIndexEncoding h0 j ∈ boundaryGridEncodingTarget h0 m
  rw [boundaryGridEncodingTarget, Finset.mem_product]
  dsimp [boundaryGridIndexEncoding]
  constructor
  · apply Finset.mem_Icc.mpr
    constructor
    · apply Nat.sub_le_iff_le_add'.mpr
      simpa [Nat.add_comm] using hsumAddGe
    · exact hsumLe
  · rw [Fintype.mem_piFinset]
    intro i
    have hjGrid := hjData.1
    rw [fractionalGridIndex, Fintype.mem_piFinset] at hjGrid
    exact hjGrid i.1

theorem boundary_target_card_le {H : Finset ℕ} (h0 : H) (m : ℕ) :
    (boundaryGridEncodingTarget h0 m).card ≤
      (Fintype.card H + 1) * m ^ (Fintype.card H - 1) := by
  have hrest : Fintype.card {i : H // i ≠ h0} =
      Fintype.card H - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [boundaryGridEncodingTarget, Finset.card_product, Nat.card_Icc,
    Fintype.card_piFinset]
  simp only [Finset.card_range, Finset.prod_const, Finset.card_univ]
  rw [hrest]
  apply Nat.mul_le_mul_right
  omega

theorem fractionalSimplexBoundaryGridIndex_card_le
    {H : Finset ℕ} (h0 : H) {m : ℕ} (hm : 0 < m) :
    (fractionalSimplexBoundaryGridIndex H m).card ≤
      (Fintype.card H + 1) * m ^ (Fintype.card H - 1) := by
  apply le_trans (Finset.card_le_card_of_injOn
    (boundaryGridIndexEncoding h0)
    (boundary_encoding_mapsTo h0 hm)
    (boundaryGridIndexEncoding_injective h0).injOn)
  exact boundary_target_card_le h0 m

theorem fractionalGridCellVolume_eq
    {H : Finset ℕ} {m : ℕ} (hm : 0 < m) (j : H → ℕ) :
    (∏ h : H, (fractionalGridUpper m j h - fractionalGridLower m j h)) =
      ((1 : ℝ) / m) ^ Fintype.card H := by
  calc
    _ = ∏ _h : H, ((1 : ℝ) / m) := by
      apply Finset.prod_congr rfl
      intro h hh
      unfold fractionalGridUpper fractionalGridLower
      have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp [hmReal]
      push_cast
      ring
    _ = _ := by simp

theorem simplexBoundaryGridVolume_eq_card_mul
    {H : Finset ℕ} {m : ℕ} (hm : 0 < m) :
    simplexBoundaryGridVolume H m =
      ((fractionalSimplexBoundaryGridIndex H m).card : ℝ) *
        ((1 : ℝ) / m) ^ Fintype.card H := by
  unfold simplexBoundaryGridVolume
  simp_rw [fractionalGridCellVolume_eq hm]
  simp

theorem simplexBoundaryGridVolume_le_card_div
    {H : Finset ℕ} (h0 : H) {m : ℕ} (hm : 0 < m) :
    simplexBoundaryGridVolume H m ≤
      (Fintype.card H + 1 : ℝ) / m := by
  rw [simplexBoundaryGridVolume_eq_card_mul hm]
  have hcard := fractionalSimplexBoundaryGridIndex_card_le h0 hm
  have hcardReal :
      ((fractionalSimplexBoundaryGridIndex H m).card : ℝ) ≤
        ((Fintype.card H + 1) * m ^ (Fintype.card H - 1) : ℕ) := by
    exact_mod_cast hcard
  calc
    _ ≤ (((Fintype.card H + 1) *
          m ^ (Fintype.card H - 1) : ℕ) : ℝ) *
          ((1 : ℝ) / m) ^ Fintype.card H :=
      mul_le_mul_of_nonneg_right hcardReal (by positivity)
    _ = _ := by
      push_cast
      have hk : Fintype.card H = (Fintype.card H - 1) + 1 := by
        have := Fintype.card_pos_iff.mpr ⟨h0⟩
        omega
      rw [hk, pow_succ]
      have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp [hmReal]
      simp only [Nat.add_sub_cancel]
      rw [← mul_pow]
      field_simp [hmReal]
      simp

theorem tendsto_simplexBoundaryGridVolume_zero
    {H : Finset ℕ} (h0 : H) :
    Tendsto (fun m : ℕ => simplexBoundaryGridVolume H m)
      atTop (nhds 0) := by
  have henvelope : Tendsto (fun m : ℕ =>
      (Fintype.card H + 1 : ℝ) / m) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul
        (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hnonneg : ∀ᶠ m : ℕ in atTop,
      0 ≤ simplexBoundaryGridVolume H m := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    rw [simplexBoundaryGridVolume_eq_card_mul (by omega)]
    positivity
  apply squeeze_zero' hnonneg ?_ henvelope
  filter_upwards [eventually_ge_atTop 1] with m hm
  exact simplexBoundaryGridVolume_le_card_div h0 (by omega)

end BoundedGaps.Maynard
