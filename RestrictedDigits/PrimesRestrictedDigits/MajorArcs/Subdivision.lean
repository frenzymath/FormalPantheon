import PrimesRestrictedDigits.Foundations.Intervals

/-!
# Major-arc short-interval subdivision

This is the exact equal-width, half-open block partition used on published
p. 187. It also records the positive-block `1/j` reparameterization.
-/

namespace PrimesRestrictedDigits

/-- The relative width of a subdivision into `J` equal blocks. -/
noncomputable def majorArcSubdivisionWidth (J : ℕ) : ℝ :=
  (J : ℝ)⁻¹

/-- The absolute block length `X / (J * m)`. -/
noncomputable def majorArcBlockLength (X : ℝ) (J m : ℕ) : ℝ :=
  X / ((J * m : ℕ) : ℝ)

noncomputable def majorArcBlockLower (X : ℝ) (J m j : ℕ) : ℝ :=
  (j : ℝ) * majorArcBlockLength X J m

noncomputable def majorArcBlockUpper (X : ℝ) (J m j : ℕ) : ℝ :=
  ((j + 1 : ℕ) : ℝ) * majorArcBlockLength X J m

/-- Natural points below a strict real cutoff. -/
noncomputable def majorArcStrictCutoff (Y : ℝ) : Finset ℕ :=
  Finset.range (Nat.ceil Y)

/-- The natural points in the `j`th left-closed, right-open block. -/
noncomputable def majorArcBlock (X : ℝ) (J m j : ℕ) : Finset ℕ :=
  naturalLeftClosedRightOpenInterval
    (majorArcBlockLower X J m j) (majorArcBlockUpper X J m j)

theorem majorArcSubdivision_width_mul_count {J : ℕ} (hJ : 0 < J) :
    majorArcSubdivisionWidth J * (J : ℝ) = 1 := by
  rw [majorArcSubdivisionWidth, inv_mul_cancel₀]
  exact_mod_cast hJ.ne'

theorem majorArcBlockLength_eq_width_mul
    (X : ℝ) {J m : ℕ} (hJ : 0 < J) (hm : 0 < m) :
    majorArcBlockLength X J m =
      majorArcSubdivisionWidth J * X / (m : ℝ) := by
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [majorArcBlockLength, majorArcSubdivisionWidth, Nat.cast_mul]
  field_simp

theorem majorArcBlockUpper_eq_nextLower (X : ℝ) (J m j : ℕ) :
    majorArcBlockUpper X J m j = majorArcBlockLower X J m (j + 1) :=
  rfl

theorem majorArcBlock_zero_lower (X : ℝ) (J m : ℕ) :
    majorArcBlockLower X J m 0 = 0 := by
  simp [majorArcBlockLower]

theorem mem_majorArcStrictCutoff {Y : ℝ} {n : ℕ} :
    n ∈ majorArcStrictCutoff Y ↔ (n : ℝ) < Y := by
  simp [majorArcStrictCutoff, Nat.lt_ceil]

private theorem majorArcBlockLength_pos
    {X : ℝ} {J m : ℕ} (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m) :
    0 < majorArcBlockLength X J m := by
  rw [majorArcBlockLength]
  exact div_pos hX (by positivity)

private theorem count_mul_majorArcBlockLength
    (X : ℝ) {J m : ℕ} (hJ : 0 < J) (hm : 0 < m) :
    (J : ℝ) * majorArcBlockLength X J m = X / (m : ℝ) := by
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [majorArcBlockLength, Nat.cast_mul]
  field_simp

theorem majorArcBlockUpper_at_last
    (X : ℝ) {J m : ℕ} (hJ : 0 < J) (hm : 0 < m) :
    majorArcBlockUpper X J m (J - 1) = X / (m : ℝ) := by
  rw [majorArcBlockUpper, Nat.sub_add_cancel hJ]
  exact count_mul_majorArcBlockLength X hJ hm

private theorem exists_mem_majorArcBlock
    {X : ℝ} {J m p : ℕ} (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m)
    (hp : p ∈ majorArcStrictCutoff (X / (m : ℝ))) :
    ∃ j < J, p ∈ majorArcBlock X J m j := by
  let w := majorArcBlockLength X J m
  let j := Nat.floor ((p : ℝ) / w)
  have hw : 0 < w := majorArcBlockLength_pos hX hJ hm
  have hp' : (p : ℝ) < X / (m : ℝ) := mem_majorArcStrictCutoff.mp hp
  have hratioNonneg : 0 ≤ (p : ℝ) / w := div_nonneg (by positivity) hw.le
  have hratio : (p : ℝ) / w < (J : ℝ) := by
    rw [div_lt_iff₀ hw]
    simpa [w, count_mul_majorArcBlockLength X hJ hm] using hp'
  have hj : j < J := (Nat.floor_lt hratioNonneg).mpr hratio
  refine ⟨j, hj, mem_naturalLeftClosedRightOpenInterval.mpr ⟨?_, ?_⟩⟩
  · have hfloor := Nat.floor_le hratioNonneg
    have hmul := mul_le_mul_of_nonneg_right hfloor hw.le
    calc
      majorArcBlockLower X J m j = (j : ℝ) * w := rfl
      _ ≤ ((p : ℝ) / w) * w := hmul
      _ = (p : ℝ) := div_mul_cancel₀ _ hw.ne'
  · have hfloor := Nat.lt_floor_add_one ((p : ℝ) / w)
    have hmul := mul_lt_mul_of_pos_right hfloor hw
    calc
      (p : ℝ) = ((p : ℝ) / w) * w := (div_mul_cancel₀ _ hw.ne').symm
      _ < ((Nat.floor ((p : ℝ) / w) : ℝ) + 1) * w := hmul
      _ = majorArcBlockUpper X J m j := by
        simp [majorArcBlockUpper, j, w]

private theorem majorArcBlock_mem_unique
    {X : ℝ} {J m j k p : ℕ} (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m)
    (hpj : p ∈ majorArcBlock X J m j) (hpk : p ∈ majorArcBlock X J m k) :
    j = k := by
  have hw := majorArcBlockLength_pos hX hJ hm
  have hpj' := mem_naturalLeftClosedRightOpenInterval.mp hpj
  have hpk' := mem_naturalLeftClosedRightOpenInterval.mp hpk
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hindex : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hjk)
    have hendpoint : majorArcBlockUpper X J m j ≤
        majorArcBlockLower X J m k := by
      unfold majorArcBlockUpper majorArcBlockLower
      exact mul_le_mul_of_nonneg_right hindex hw.le
    exact (not_lt_of_ge (hendpoint.trans hpk'.1)) hpj'.2
  · have hindex : ((k + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hkj)
    have hendpoint : majorArcBlockUpper X J m k ≤
        majorArcBlockLower X J m j := by
      unfold majorArcBlockUpper majorArcBlockLower
      exact mul_le_mul_of_nonneg_right hindex hw.le
    exact (not_lt_of_ge (hendpoint.trans hpj'.1)) hpk'.2

theorem mem_majorArcCutoff_iff_existsUnique_mem_block
    {X : ℝ} {J m p : ℕ} (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m) :
    p ∈ majorArcStrictCutoff (X / (m : ℝ)) ↔
      ∃ j, j < J ∧ p ∈ majorArcBlock X J m j ∧
        ∀ k, k < J → p ∈ majorArcBlock X J m k → k = j := by
  constructor
  · intro hp
    rcases exists_mem_majorArcBlock hX hJ hm hp with ⟨j, hj, hpj⟩
    exact ⟨j, hj, hpj, fun k hk hpk => majorArcBlock_mem_unique hX hJ hm hpk hpj⟩
  · rintro ⟨j, hj, hpj, _⟩
    rw [mem_majorArcStrictCutoff]
    have hpj' := mem_naturalLeftClosedRightOpenInterval.mp hpj
    have hw : 0 ≤ majorArcBlockLength X J m :=
      (majorArcBlockLength_pos hX hJ hm).le
    calc
      (p : ℝ) < majorArcBlockUpper X J m j := hpj'.2
      _ ≤ (J : ℝ) * majorArcBlockLength X J m := by
        unfold majorArcBlockUpper
        apply mul_le_mul_of_nonneg_right _ hw
        exact_mod_cast (Nat.succ_le_iff.mpr hj)
      _ = X / (m : ℝ) := count_mul_majorArcBlockLength X hJ hm

theorem majorArcSubdivisionWidth_le_relative
    {J j : ℕ} (hj : 0 < j) (hjJ : j ≤ J) :
    majorArcSubdivisionWidth J ≤ (j : ℝ)⁻¹ := by
  rw [majorArcSubdivisionWidth]
  exact inv_anti₀ (by exact_mod_cast hj) (by exact_mod_cast hjJ)

theorem majorArcBlockUpper_le_cutoff
    {X : ℝ} {J m j : ℕ} (hX : 0 ≤ X) (hJ : 0 < J) (hm : 0 < m)
    (hj : j < J) :
    majorArcBlockUpper X J m j ≤ X / (m : ℝ) := by
  have hw : 0 ≤ majorArcBlockLength X J m := by
    rw [majorArcBlockLength]
    positivity
  calc
    majorArcBlockUpper X J m j ≤
        (J : ℝ) * majorArcBlockLength X J m := by
      unfold majorArcBlockUpper
      apply mul_le_mul_of_nonneg_right _ hw
      exact_mod_cast (Nat.succ_le_iff.mpr hj)
    _ = X / (m : ℝ) := count_mul_majorArcBlockLength X hJ hm

theorem majorArcBlocks_pairwiseDisjoint
    {X : ℝ} {J m : ℕ} (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m) :
    Set.PairwiseDisjoint (Finset.range J : Set ℕ) (majorArcBlock X J m) := by
  intro j hj k hk hne
  change Disjoint (majorArcBlock X J m j) (majorArcBlock X J m k)
  rw [Finset.disjoint_left]
  intro p hpj hpk
  exact hne (majorArcBlock_mem_unique hX hJ hm hpj hpk)

theorem majorArcBlocks_biUnion_eq_strictCutoff
    {X : ℝ} {J m : ℕ} (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m) :
    (Finset.range J).biUnion (majorArcBlock X J m) =
      majorArcStrictCutoff (X / (m : ℝ)) := by
  ext p
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨j, hj, hpj⟩
    rw [mem_majorArcStrictCutoff]
    have hpj' := mem_naturalLeftClosedRightOpenInterval.mp hpj
    exact hpj'.2.trans_le
      (majorArcBlockUpper_le_cutoff hX.le hJ hm (Finset.mem_range.mp hj))
  · intro hp
    rcases exists_mem_majorArcBlock hX hJ hm hp with ⟨j, hj, hpj⟩
    exact ⟨j, Finset.mem_range.mpr hj, hpj⟩

theorem majorArcPositiveBlock_reparameterization
    (X : ℝ) {J m j : ℕ} (_hJ : 0 < J) (_hm : 0 < m) (hj : 0 < j) :
    majorArcBlockUpper X J m j =
      majorArcBlockLower X J m j +
        (j : ℝ)⁻¹ * majorArcBlockLower X J m j := by
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  unfold majorArcBlockUpper majorArcBlockLower
  push_cast
  field_simp

theorem majorArcPositiveBlock_interval_eq_relative
    (X : ℝ) {J m j : ℕ} (hJ : 0 < J) (hm : 0 < m) (hj : 0 < j) :
    majorArcBlock X J m j =
      naturalLeftClosedRightOpenInterval
        (majorArcBlockLower X J m j)
        (majorArcBlockLower X J m j +
          (j : ℝ)⁻¹ * majorArcBlockLower X J m j) := by
  rw [majorArcBlock, majorArcPositiveBlock_reparameterization X hJ hm hj]

theorem majorArcBlock_scaled_sub_left
    {X : ℝ} {J m j p : ℕ} (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m)
    (hp : p ∈ majorArcBlock X J m j) :
    0 ≤ ((m * p : ℕ) : ℝ) / X - (j : ℝ) / (J : ℝ) ∧
      ((m * p : ℕ) : ℝ) / X - (j : ℝ) / (J : ℝ) <
        majorArcSubdivisionWidth J := by
  have hp' := mem_naturalLeftClosedRightOpenInterval.mp hp
  have hJreal : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJmreal : (0 : ℝ) < (J * m : ℕ) := by positivity
  have hlowDiv :
      (j : ℝ) * X / ((J * m : ℕ) : ℝ) ≤ (p : ℝ) := by
    calc
      (j : ℝ) * X / ((J * m : ℕ) : ℝ) =
          (j : ℝ) * (X / ((J * m : ℕ) : ℝ)) := by ring
      _ ≤ (p : ℝ) := by
        simpa [majorArcBlock, majorArcBlockLower, majorArcBlockLength] using hp'.1
  have hlow : (j : ℝ) * X ≤ (p : ℝ) * ((J * m : ℕ) : ℝ) :=
    (div_le_iff₀ hJmreal).mp hlowDiv
  have huppDiv : (p : ℝ) <
      ((j + 1 : ℕ) : ℝ) * X / ((J * m : ℕ) : ℝ) := by
    calc
      (p : ℝ) < ((j + 1 : ℕ) : ℝ) *
          (X / ((J * m : ℕ) : ℝ)) := by
        simpa [majorArcBlock, majorArcBlockUpper, majorArcBlockLength] using hp'.2
      _ = ((j + 1 : ℕ) : ℝ) * X / ((J * m : ℕ) : ℝ) := by ring
  have hupp : (p : ℝ) * ((J * m : ℕ) : ℝ) <
      ((j + 1 : ℕ) : ℝ) * X := (lt_div_iff₀ hJmreal).mp huppDiv
  push_cast at hlow hupp
  have hscaledLower : (j : ℝ) / (J : ℝ) ≤ ((m * p : ℕ) : ℝ) / X := by
    rw [div_le_div_iff₀ hJreal hX]
    push_cast
    nlinarith [hlow]
  have hscaledUpper : ((m * p : ℕ) : ℝ) / X <
      ((j + 1 : ℕ) : ℝ) / (J : ℝ) := by
    rw [div_lt_div_iff₀ hX hJreal]
    push_cast
    nlinarith [hupp]
  constructor
  · linarith
  · rw [majorArcSubdivisionWidth, inv_eq_one_div]
    have hstep : (((j + 1 : ℕ) : ℝ) / (J : ℝ)) - (j : ℝ) / (J : ℝ) =
        1 / (J : ℝ) := by
      push_cast
      field_simp
      ring
    linarith

end PrimesRestrictedDigits
