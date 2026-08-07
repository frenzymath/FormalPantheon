import BoundedGaps.Maynard.MaynardS2GDivisorExpansion
import BoundedGaps.Maynard.MaynardS1UnrestrictedReindex

noncomputable section

/-!
# Restricted S2 quadratic reindexing

This file separates the cross-compatible S2 common-divisor kernel into an
unrestricted quadratic transform and an explicit incompatible correction.
Only finite sums are manipulated.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance s2RestrictedReindexDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def divisorTupleTotientProduct
    (H : Finset ℕ) (d : H → ℕ) : ℝ :=
  ∏ h : H, (Nat.totient (d h) : ℝ)

theorem commonDivisorS2TupleTerm_eq_product_div
    (H : Finset ℕ) (d e u : H → ℕ) :
    commonDivisorS2TupleTerm H d e u =
      (∏ h : H, (maynardS2G (u h) : ℝ)) /
        (divisorTupleTotientProduct H d *
          divisorTupleTotientProduct H e) := by
  unfold commonDivisorS2TupleTerm divisorTupleTotientProduct
  rw [Finset.prod_div_distrib]
  congr 1
  rw [Finset.prod_mul_distrib]

noncomputable def compatibleDivisorPairRestrictedS2CommonDivisorMembershipSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D.filter (fun e => IsCrossCoordinateCoprime H d e),
    if d m = 1 ∧ e m = 1 then
      ∑ u ∈ commonDivisorTupleSupport H d e,
        commonDivisorS2TupleTerm H d e u * (lambda d * lambda e)
    else 0

noncomputable def unrestrictedDivisorPairRestrictedS2CommonDivisorTupleSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D,
    if d m = 1 ∧ e m = 1 then
      ∑ u ∈ commonDivisorTupleSupport H d e,
        commonDivisorS2TupleTerm H d e u * (lambda d * lambda e)
    else 0

noncomputable def incompatibleDivisorPairRestrictedS2CommonDivisorTupleSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ d ∈ D,
    ∑ e ∈ D.filter (fun e => ¬IsCrossCoordinateCoprime H d e),
      if d m = 1 ∧ e m = 1 then
        ∑ u ∈ commonDivisorTupleSupport H d e,
          commonDivisorS2TupleTerm H d e u * (lambda d * lambda e)
      else 0

theorem compatibleRestrictedS2SubtypeSum_eq_membershipSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) :
    compatibleDivisorPairRestrictedS2CommonDivisorTupleSum H D lambda m =
      compatibleDivisorPairRestrictedS2CommonDivisorMembershipSum
        H D lambda m := by
  classical
  unfold compatibleDivisorPairRestrictedS2CommonDivisorTupleSum
    compatibleDivisorPairRestrictedS2CommonDivisorMembershipSum
  let g : (H → ℕ) → (H → ℕ) → ℝ := fun d e =>
    if d m = 1 ∧ e m = 1 then
      ∑ u ∈ commonDivisorTupleSupport H d e,
        commonDivisorS2TupleTerm H d e u * (lambda d * lambda e)
    else 0
  change (∑ d : D, ∑ e : D.filter
      (fun e => IsCrossCoordinateCoprime H d.1 e), g d.1 e.1) =
    ∑ d ∈ D, ∑ e ∈ D.filter
      (fun e => IsCrossCoordinateCoprime H d e), g d e
  symm
  calc
    (∑ d ∈ D, ∑ e ∈ D.filter
        (fun e => IsCrossCoordinateCoprime H d e), g d e) =
        ∑ d ∈ D, ∑ e : D.filter
          (fun e => IsCrossCoordinateCoprime H d e), g d e.1 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact Finset.sum_subtype
        (D.filter (fun e => IsCrossCoordinateCoprime H d e))
        (fun _ => Iff.rfl) (g d)
    _ = ∑ d : D, ∑ e : D.filter
        (fun e => IsCrossCoordinateCoprime H d.1 e), g d.1 e.1 :=
      Finset.sum_subtype D (fun _ => Iff.rfl) _

theorem unrestrictedRestrictedS2_eq_compatible_add_incompatible
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) :
    unrestrictedDivisorPairRestrictedS2CommonDivisorTupleSum H D lambda m =
      compatibleDivisorPairRestrictedS2CommonDivisorMembershipSum H D lambda m +
        incompatibleDivisorPairRestrictedS2CommonDivisorTupleSum H D lambda m := by
  classical
  unfold unrestrictedDivisorPairRestrictedS2CommonDivisorTupleSum
    compatibleDivisorPairRestrictedS2CommonDivisorMembershipSum
    incompatibleDivisorPairRestrictedS2CommonDivisorTupleSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  exact (Finset.sum_filter_add_sum_filter_not D
    (fun e => IsCrossCoordinateCoprime H d e)
    (fun e => if d m = 1 ∧ e m = 1 then
      ∑ u ∈ commonDivisorTupleSupport H d e,
        commonDivisorS2TupleTerm H d e u * (lambda d * lambda e)
      else 0)).symm

theorem compatibleRestrictedS2_eq_unrestricted_sub_incompatible
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) :
    compatibleDivisorPairRestrictedS2CommonDivisorMembershipSum H D lambda m =
      unrestrictedDivisorPairRestrictedS2CommonDivisorTupleSum H D lambda m -
        incompatibleDivisorPairRestrictedS2CommonDivisorTupleSum H D lambda m := by
  have h := unrestrictedRestrictedS2_eq_compatible_add_incompatible
    H D lambda m
  linarith

noncomputable def maynardS2RestrictedQuadraticTransform
    (H : Finset ℕ) (R : ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ u ∈ maynardDivisorTupleBox H R,
    (∏ h : H, (maynardS2G (u h) : ℝ)) *
      (∑ d ∈ D,
        if (∀ h : H, u h ∣ d h) ∧ d m = 1 then
          lambda d / divisorTupleTotientProduct H d
        else 0) ^ 2

theorem restrictedTotientDivisorSum_sq_eq_pair_sum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) (u : H → ℕ) :
    (∑ d ∈ D,
        if (∀ h : H, u h ∣ d h) ∧ d m = 1 then
          lambda d / divisorTupleTotientProduct H d
        else 0) ^ 2 =
      ∑ d ∈ D, ∑ e ∈ D,
        if (∀ h : H, u h ∣ d h ∧ u h ∣ e h) ∧
            d m = 1 ∧ e m = 1 then
          (lambda d / divisorTupleTotientProduct H d) *
            (lambda e / divisorTupleTotientProduct H e)
        else 0 := by
  classical
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hdCond : (∀ h : H, u h ∣ d h) ∧ d m = 1
  · by_cases heCond : (∀ h : H, u h ∣ e h) ∧ e m = 1
    · have hboth : (∀ h : H, u h ∣ d h ∧ u h ∣ e h) ∧
          d m = 1 ∧ e m = 1 :=
        ⟨fun h => ⟨hdCond.1 h, heCond.1 h⟩, hdCond.2, heCond.2⟩
      rw [if_pos hdCond, if_pos heCond, if_pos hboth]
    · have hnot : ¬((∀ h : H, u h ∣ d h ∧ u h ∣ e h) ∧
          d m = 1 ∧ e m = 1) := by
        intro h
        exact heCond ⟨fun i => (h.1 i).2, h.2.2⟩
      rw [if_neg heCond, if_neg hnot]
      simp
  · have hnot : ¬((∀ h : H, u h ∣ d h ∧ u h ∣ e h) ∧
        d m = 1 ∧ e m = 1) := by
      intro h
      exact hdCond ⟨fun i => (h.1 i).1, h.2.1⟩
    rw [if_neg hdCond, if_neg hnot]
    simp

theorem unrestrictedRestrictedS2_eq_quadraticTransform
    {H : Finset ℕ} {R W : ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} (m : H)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    unrestrictedDivisorPairRestrictedS2CommonDivisorTupleSum H D lambda m =
      maynardS2RestrictedQuadraticTransform H R D lambda m := by
  classical
  symm
  unfold maynardS2RestrictedQuadraticTransform
    unrestrictedDivisorPairRestrictedS2CommonDivisorTupleSum
  calc
    (∑ u ∈ maynardDivisorTupleBox H R,
        (∏ h : H, (maynardS2G (u h) : ℝ)) *
          (∑ d ∈ D,
            if (∀ h : H, u h ∣ d h) ∧ d m = 1 then
              lambda d / divisorTupleTotientProduct H d
            else 0) ^ 2) =
        ∑ u ∈ maynardDivisorTupleBox H R,
          (∏ h : H, (maynardS2G (u h) : ℝ)) *
            (∑ d ∈ D, ∑ e ∈ D,
              if (∀ h : H, u h ∣ d h ∧ u h ∣ e h) ∧
                  d m = 1 ∧ e m = 1 then
                (lambda d / divisorTupleTotientProduct H d) *
                  (lambda e / divisorTupleTotientProduct H e)
              else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [restrictedTotientDivisorSum_sq_eq_pair_sum]
    _ = ∑ u ∈ maynardDivisorTupleBox H R,
          ∑ d ∈ D, ∑ e ∈ D,
            if (∀ h : H, u h ∣ d h ∧ u h ∣ e h) ∧
                d m = 1 ∧ e m = 1 then
              commonDivisorS2TupleTerm H d e u * (lambda d * lambda e)
            else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hcond : (∀ h : H, u h ∣ d h ∧ u h ∣ e h) ∧
          d m = 1 ∧ e m = 1
      · rw [if_pos hcond, if_pos hcond,
          commonDivisorS2TupleTerm_eq_product_div]
        simp only [div_eq_mul_inv]
        ring
      · rw [if_neg hcond, if_neg hcond, mul_zero]
    _ = ∑ d ∈ D, ∑ e ∈ D,
          ∑ u ∈ maynardDivisorTupleBox H R,
            if (∀ h : H, u h ∣ d h ∧ u h ∣ e h) ∧
                d m = 1 ∧ e m = 1 then
              commonDivisorS2TupleTerm H d e u * (lambda d * lambda e)
            else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ d ∈ D, ∑ e ∈ D,
          if d m = 1 ∧ e m = 1 then
            ∑ u ∈ commonDivisorTupleSupport H d e,
              commonDivisorS2TupleTerm H d e u * (lambda d * lambda e)
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      by_cases hm : d m = 1 ∧ e m = 1
      · rw [if_pos hm]
        have hsum := sum_commonDivisorTuple_eq_box_indicator
          (e := e) (hD d hd)
          (fun u => commonDivisorS2TupleTerm H d e u *
            (lambda d * lambda e))
        rw [hsum]
        apply Finset.sum_congr rfl
        intro u hu
        by_cases hdiv : ∀ h : H, u h ∣ d h ∧ u h ∣ e h
        · rw [if_pos hdiv, if_pos ⟨hdiv, hm⟩]
        · rw [if_neg hdiv, if_neg (fun h => hdiv h.1)]
      · rw [if_neg hm]
        apply Finset.sum_eq_zero
        intro u hu
        rw [if_neg]
        exact fun h => hm h.2

end BoundedGaps.Maynard
