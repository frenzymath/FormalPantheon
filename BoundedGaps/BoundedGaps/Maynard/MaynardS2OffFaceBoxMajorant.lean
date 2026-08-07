import BoundedGaps.Maynard.MaynardFixedDivisorRoughTail
import BoundedGaps.Maynard.MaynardS1StarredSummandBound
import BoundedGaps.Maynard.MaynardYDiagonalCollisionUnion

noncomputable section

/-!
# Box majorant for Maynard's restricted S2 off-face sum

The exact off-face support is covered by coordinate witnesses and enlarged to
independent boxes. This formalizes the finite majorization in
Maynard2013v3, source lines 431--434, before inserting scalar estimates.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators
local instance s2OffFaceBoxDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def maynardS2OffFaceTupleWeight
    (H : Finset ℕ) (m : H) (r a : H → ℕ) : ℝ :=
  ((1 : ℝ) / Nat.totient (a m)) *
    ∏ h ∈ Finset.univ.erase m,
      (r h : ℝ) / (Nat.totient (a h) : ℝ) ^ 2

noncomputable def maynardS2OffFaceSupport
    (H : Finset ℕ) (R D : ℕ) (m : H) (r : H → ℕ) :
    Finset (H → ℕ) :=
  (maynardDivisorTupleSupport H R (primorial D)).filter fun a =>
    (∀ h : H, r h ∣ a h) ∧ ¬IsMaynardS2MainFace m r a

noncomputable def maynardS2OffFaceWitnessSupport
    (H : Finset ℕ) (R D : ℕ) (r : H → ℕ) (j : H) :
    Finset (H → ℕ) :=
  (maynardDivisorTupleSupport H R (primorial D)).filter fun a =>
    (∀ h : H, r h ∣ a h) ∧ a j ≠ r j

noncomputable def maynardS2OffFaceCoordinateBox
    (H : Finset ℕ) (R D : ℕ) (m : H) (r : H → ℕ) (j : H) :
    Finset (H → ℕ) :=
  Fintype.piFinset fun h =>
    if h = m then preSievedCommonCoordinateSupport (primorial D) R
    else if h = j then
      (preSievedFixedDivisorTotientSquareSupport D (r h) R).erase (r h)
    else preSievedFixedDivisorTotientSquareSupport D (r h) R

noncomputable def maynardS2OffFaceCoordinateBoxMass
    (H : Finset ℕ) (R D : ℕ) (m : H) (r : H → ℕ) (j : H) : ℝ :=
  ∑ a ∈ maynardS2OffFaceCoordinateBox H R D m r j,
    maynardS2OffFaceTupleWeight H m r a

theorem maynardS2OffFaceSupport_eq_witnessUnion
    {H : Finset ℕ} {R D : ℕ} (m : H) (r : H → ℕ) :
    maynardS2OffFaceSupport H R D m r =
      (Finset.univ.erase m).biUnion
        (maynardS2OffFaceWitnessSupport H R D r) := by
  classical
  ext a
  constructor
  · intro ha
    have haData := Finset.mem_filter.mp ha
    have hnot := haData.2.2
    unfold IsMaynardS2MainFace at hnot
    push Not at hnot
    obtain ⟨j, hjm, hja⟩ := hnot
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_erase.mpr ⟨hjm, Finset.mem_univ j⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨haData.1, haData.2.1, hja⟩
  · intro ha
    obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp ha
    have hjm := (Finset.mem_erase.mp hj).1
    have haData := Finset.mem_filter.mp haj
    apply Finset.mem_filter.mpr
    refine ⟨haData.1, haData.2.1, ?_⟩
    intro hface
    exact haData.2.2 (hface j hjm)

theorem maynardS2OffFaceWitnessSupport_subset_box
    {H : Finset ℕ} {R D : ℕ} {m j : H} {r : H → ℕ} :
    maynardS2OffFaceWitnessSupport H R D r j ⊆
      maynardS2OffFaceCoordinateBox H R D m r j := by
  classical
  intro a ha
  have haData := Finset.mem_filter.mp ha
  have haSupport := isMaynardDivisorTuple_of_mem_support haData.1
  have haBox := (mem_maynardDivisorTupleSupport_iff.mp haData.1).1
  rw [maynardS2OffFaceCoordinateBox, Fintype.mem_piFinset]
  intro h
  have haBounds := (mem_maynardDivisorTupleBox_iff.mp haBox) h
  have haSq := haSupport.coordinate_squarefree h
  have haCop := haSupport.coordinate_coprime_W h
  by_cases hhM : h = m
  · subst h
    simp only [eq_self, ↓reduceIte]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr haBounds.2,
      haBounds.1, haSq, haCop⟩
  · rw [if_neg hhM]
    by_cases hhJ : h = j
    · subst h
      rw [if_pos rfl]
      apply Finset.mem_erase.mpr
      refine ⟨haData.2.2, Finset.mem_filter.mpr ?_⟩
      exact ⟨Finset.mem_Icc.mpr ⟨haBounds.1, haBounds.2.le⟩,
        haSq, haCop, haData.2.1 j⟩
    · rw [if_neg hhJ]
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨haBounds.1, haBounds.2.le⟩,
        haSq, haCop, haData.2.1 h⟩

theorem abs_maynardS2WeightedOffFaceTerm_le
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (m : H) {r a : H → ℕ}
    (hr : IsMaynardDivisorTuple H R (primorial D) r)
    (ha : IsMaynardDivisorTuple H R (primorial D) a)
    {B : ℝ} (hyBound : ∀ u, |y u| ≤ B) :
    |(∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
          maynardS2G (r h)) *
        ((y a / divisorTupleTotientProduct H a) *
          maynardS2WeightedFaceFactor H m r a)| ≤
      B * (∏ h : H, (maynardS2G (r h) : ℝ)) *
        maynardS2OffFaceTupleWeight H m r a := by
  classical
  have habsMu {n : ℕ} (hn : Squarefree n) :
      |(ArithmeticFunction.moebius n : ℝ)| = 1 := by
    have hsq : (ArithmeticFunction.moebius n : ℝ) ^ 2 = 1 := by
      exact_mod_cast (squarefree_iff_moebius_sq_eq_one n).mp hn
    rcases (sq_eq_one_iff.mp hsq) with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  have hprefactor :
      |∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
          maynardS2G (r h)| =
        ∏ h : H, (maynardS2G (r h) : ℝ) := by
    rw [Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro h hh
    rw [abs_mul, habsMu (hr.coordinate_squarefree h),
      abs_of_nonneg (Nat.cast_nonneg _), one_mul]
  have hface : |maynardS2WeightedFaceFactor H m r a| =
      ∏ h ∈ Finset.univ.erase m,
        (r h : ℝ) / Nat.totient (a h) := by
    unfold maynardS2WeightedFaceFactor
    rw [Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro h hh
    rw [abs_div, abs_mul, habsMu (ha.coordinate_squarefree h),
      abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_nonneg (Nat.cast_nonneg _), one_mul]
  have htotientNonneg : 0 ≤ divisorTupleTotientProduct H a := by
    unfold divisorTupleTotientProduct
    positivity
  have htotient : divisorTupleTotientProduct H a =
      (Nat.totient (a m) : ℝ) *
        ∏ h ∈ Finset.univ.erase m, (Nat.totient (a h) : ℝ) := by
    unfold divisorTupleTotientProduct
    exact (Finset.mul_prod_erase Finset.univ
      (fun h : H => (Nat.totient (a h) : ℝ))
      (Finset.mem_univ m)).symm
  have hphiM : (Nat.totient (a m) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (ha.coordinate_squarefree m).ne_zero)))
  have hphiOff :
      (∏ h ∈ Finset.univ.erase m, (Nat.totient (a h) : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro h hh
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (ha.coordinate_squarefree h).ne_zero)))
  have hlocal :
      (∏ h ∈ Finset.univ.erase m,
          (r h : ℝ) / Nat.totient (a h)) /
          (∏ h ∈ Finset.univ.erase m,
            (Nat.totient (a h) : ℝ)) =
        ∏ h ∈ Finset.univ.erase m,
          (r h : ℝ) / (Nat.totient (a h) : ℝ) ^ 2 := by
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro h hh
    have hphi : (Nat.totient (a h) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr
        (Nat.pos_of_ne_zero (ha.coordinate_squarefree h).ne_zero)))
    field_simp [hphi]
  have hweight :
      ((1 : ℝ) / divisorTupleTotientProduct H a) *
          (∏ h ∈ Finset.univ.erase m,
            (r h : ℝ) / Nat.totient (a h)) =
        maynardS2OffFaceTupleWeight H m r a := by
    rw [htotient]
    unfold maynardS2OffFaceTupleWeight
    rw [← hlocal]
    field_simp [hphiM, hphiOff]
  rw [abs_mul, hprefactor, abs_mul, abs_div,
    abs_of_nonneg htotientNonneg, hface]
  rw [show |y a| / divisorTupleTotientProduct H a =
      |y a| * ((1 : ℝ) / divisorTupleTotientProduct H a) by ring]
  have hnonneg : 0 ≤
      (∏ h : H, (maynardS2G (r h) : ℝ)) *
        maynardS2OffFaceTupleWeight H m r a := by
    unfold maynardS2OffFaceTupleWeight
    positivity
  calc
    (∏ h : H, (maynardS2G (r h) : ℝ)) *
          ((|y a| * ((1 : ℝ) / divisorTupleTotientProduct H a)) *
            (∏ h ∈ Finset.univ.erase m,
              (r h : ℝ) / Nat.totient (a h))) =
        |y a| * (∏ h : H, (maynardS2G (r h) : ℝ)) *
          (((1 : ℝ) / divisorTupleTotientProduct H a) *
            ∏ h ∈ Finset.univ.erase m,
              (r h : ℝ) / Nat.totient (a h)) := by ring
    _ = |y a| * (∏ h : H, (maynardS2G (r h) : ℝ)) *
          maynardS2OffFaceTupleWeight H m r a := by rw [hweight]
    _ ≤ B * (∏ h : H, (maynardS2G (r h) : ℝ)) *
          maynardS2OffFaceTupleWeight H m r a := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hyBound a) hnonneg

theorem maynardS2WeightedOffFaceSum_eq_supportSum
    (H : Finset ℕ) (R D : ℕ) (y : (H → ℕ) → ℝ)
    (m : H) (r : H → ℕ) :
    maynardS2WeightedOffFaceSum H R (primorial D) y m r =
      ∑ a ∈ maynardS2OffFaceSupport H R D m r,
        (y a / divisorTupleTotientProduct H a) *
          maynardS2WeightedFaceFactor H m r a := by
  classical
  unfold maynardS2WeightedOffFaceSum maynardS2OffFaceSupport
  rw [Finset.sum_filter]

theorem abs_prefactor_mul_maynardS2WeightedOffFaceSum_le_boxMass
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ}
    (m : H) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R (primorial D) r)
    {B : ℝ} (hB : 0 ≤ B) (hyBound : ∀ u, |y u| ≤ B) :
    |(∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
          maynardS2G (r h)) *
        maynardS2WeightedOffFaceSum H R (primorial D) y m r| ≤
      B * (∏ h : H, (maynardS2G (r h) : ℝ)) *
        ∑ j ∈ Finset.univ.erase m,
          maynardS2OffFaceCoordinateBoxMass H R D m r j := by
  classical
  let G : ℝ := ∏ h : H, (maynardS2G (r h) : ℝ)
  have hG : 0 ≤ G := by
    unfold G
    positivity
  have hmass :
      (∑ a ∈ maynardS2OffFaceSupport H R D m r,
          maynardS2OffFaceTupleWeight H m r a) ≤
        ∑ j ∈ Finset.univ.erase m,
          maynardS2OffFaceCoordinateBoxMass H R D m r j := by
    rw [maynardS2OffFaceSupport_eq_witnessUnion m r]
    calc
      (∑ a ∈ (Finset.univ.erase m).biUnion
          (maynardS2OffFaceWitnessSupport H R D r),
          maynardS2OffFaceTupleWeight H m r a) ≤
          ∑ j ∈ Finset.univ.erase m,
            ∑ a ∈ maynardS2OffFaceWitnessSupport H R D r j,
              maynardS2OffFaceTupleWeight H m r a := by
        exact sum_biUnion_le_sum _ _ _ (fun a => by
          unfold maynardS2OffFaceTupleWeight
          positivity)
      _ ≤ ∑ j ∈ Finset.univ.erase m,
            maynardS2OffFaceCoordinateBoxMass H R D m r j := by
        apply Finset.sum_le_sum
        intro j hj
        unfold maynardS2OffFaceCoordinateBoxMass
        apply Finset.sum_le_sum_of_subset_of_nonneg
          maynardS2OffFaceWitnessSupport_subset_box
        intro a ha haNot
        unfold maynardS2OffFaceTupleWeight
        positivity
  rw [maynardS2WeightedOffFaceSum_eq_supportSum]
  rw [Finset.mul_sum]
  calc
    |∑ a ∈ maynardS2OffFaceSupport H R D m r,
        (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
          maynardS2G (r h)) *
          ((y a / divisorTupleTotientProduct H a) *
            maynardS2WeightedFaceFactor H m r a)| ≤
        ∑ a ∈ maynardS2OffFaceSupport H R D m r,
          |(∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
            maynardS2G (r h)) *
            ((y a / divisorTupleTotientProduct H a) *
              maynardS2WeightedFaceFactor H m r a)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ maynardS2OffFaceSupport H R D m r,
          B * G * maynardS2OffFaceTupleWeight H m r a := by
      apply Finset.sum_le_sum
      intro a ha
      have haSupport := isMaynardDivisorTuple_of_mem_support
        (Finset.mem_filter.mp ha).1
      exact abs_maynardS2WeightedOffFaceTerm_le m hr haSupport hyBound
    _ = B * G *
        ∑ a ∈ maynardS2OffFaceSupport H R D m r,
          maynardS2OffFaceTupleWeight H m r a := by
      rw [Finset.mul_sum]
    _ ≤ B * G *
        ∑ j ∈ Finset.univ.erase m,
          maynardS2OffFaceCoordinateBoxMass H R D m r j := by
      exact mul_le_mul_of_nonneg_left hmass (mul_nonneg hB hG)

end BoundedGaps.Maynard
