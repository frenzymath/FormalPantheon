import BoundedGaps.Maynard.MaynardYForwardTransform

noncomputable section

/-!
# Unrestricted S1 common-divisor reindexing

This file isolates the exact diagonal core of the S1 main term. The
cross-coordinate compatibility correction remains separate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def unrestrictedDivisorPairCommonDivisorTupleSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D,
    ∑ u ∈ commonDivisorTupleSupport H d e,
      commonDivisorTupleTerm H d e u * (lambda d * lambda e)

def maynardYQuadraticTransform
    (H : Finset ℕ) (R : ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) : ℝ := by
  classical
  exact
    ∑ u ∈ maynardDivisorTupleBox H R,
      (∏ h : H, (Nat.totient (u h) : ℝ)) *
        (∑ d ∈ D,
          if ∀ h : H, u h ∣ d h then
            lambda d / (divisorTupleProduct H d : ℝ)
          else 0) ^ 2

theorem filter_maynardBox_commonDivisors_eq_support
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) :
    (maynardDivisorTupleBox H R).filter
        (fun u => ∀ h : H, u h ∣ d h ∧ u h ∣ e h) =
      commonDivisorTupleSupport H d e := by
  classical
  ext u
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨huBox, hu⟩
    exact (mem_commonDivisorTupleSupport_iff hd).mpr hu
  · intro huSupport
    have hu := (mem_commonDivisorTupleSupport_iff hd).mp huSupport
    refine ⟨mem_maynardDivisorTupleBox_iff.mpr ?_, hu⟩
    intro h
    have hdCoordPos : 0 < d h :=
      Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero
    have huPos : 0 < u h := Nat.pos_of_dvd_of_pos (hu h).1 hdCoordPos
    have hdProdPos : 0 < divisorTupleProduct H d :=
      Nat.pos_of_ne_zero hd.2.2.ne_zero
    have hdLe : d h ≤ divisorTupleProduct H d :=
      Nat.le_of_dvd hdProdPos (divisorTupleCoordinate_dvd_product d h)
    have huLe : u h ≤ d h := Nat.le_of_dvd hdCoordPos (hu h).1
    exact ⟨huPos, lt_of_le_of_lt (huLe.trans hdLe) hd.1⟩

theorem commonDivisorTupleTerm_eq_product_div
    (H : Finset ℕ) (d e u : H → ℕ) :
    commonDivisorTupleTerm H d e u =
      (∏ h : H, (Nat.totient (u h) : ℝ)) /
        ((divisorTupleProduct H d : ℝ) *
          divisorTupleProduct H e) := by
  unfold commonDivisorTupleTerm
  rw [Finset.prod_div_distrib]
  congr 1
  rw [Finset.prod_mul_distrib]
  simp [divisorTupleProduct]

theorem sum_commonDivisorTuple_eq_box_indicator
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (f : (H → ℕ) → ℝ) :
    (∑ u ∈ commonDivisorTupleSupport H d e, f u) =
      ∑ u ∈ maynardDivisorTupleBox H R,
        if ∀ h : H, u h ∣ d h ∧ u h ∣ e h then f u else 0 := by
  classical
  rw [← Finset.sum_filter]
  rw [filter_maynardBox_commonDivisors_eq_support hd]

theorem square_divisorTupleSum_eq_pair_sum
    {H : Finset ℕ} (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (u : H → ℕ) :
    (∑ d ∈ D,
        if ∀ h : H, u h ∣ d h then
          lambda d / (divisorTupleProduct H d : ℝ)
        else 0) ^ 2 =
      ∑ d ∈ D, ∑ e ∈ D,
        if ∀ h : H, u h ∣ d h ∧ u h ∣ e h then
          (lambda d / (divisorTupleProduct H d : ℝ)) *
            (lambda e / (divisorTupleProduct H e : ℝ))
        else 0 := by
  classical
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hud : ∀ h : H, u h ∣ d h
  · by_cases hue : ∀ h : H, u h ∣ e h
    · have hboth : ∀ h : H, u h ∣ d h ∧ u h ∣ e h :=
        fun h => ⟨hud h, hue h⟩
      rw [if_pos hue, if_pos hud, if_pos hboth]
    · have hboth : ¬(∀ h : H, u h ∣ d h ∧ u h ∣ e h) :=
        fun h => hue (fun i => (h i).2)
      rw [if_neg hue, if_neg hboth]
      simp
  · by_cases hue : ∀ h : H, u h ∣ e h
    · have hboth : ¬(∀ h : H, u h ∣ d h ∧ u h ∣ e h) :=
        fun h => hud (fun i => (h i).1)
      rw [if_pos hue, if_neg hud, if_neg hboth]
      simp
    · have hboth : ¬(∀ h : H, u h ∣ d h ∧ u h ∣ e h) :=
        fun h => hue (fun i => (h i).2)
      rw [if_neg hue, if_neg hboth]
      simp

theorem unrestrictedCommonDivisorTupleSum_eq_maynardYQuadraticTransform
    {H : Finset ℕ} {R W : ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    unrestrictedDivisorPairCommonDivisorTupleSum H D lambda =
      maynardYQuadraticTransform H R D lambda := by
  classical
  symm
  unfold maynardYQuadraticTransform
    unrestrictedDivisorPairCommonDivisorTupleSum
  calc
    (∑ u ∈ maynardDivisorTupleBox H R,
        (∏ h : H, (Nat.totient (u h) : ℝ)) *
          (∑ d ∈ D,
            if ∀ h : H, u h ∣ d h then
              lambda d / (divisorTupleProduct H d : ℝ)
            else 0) ^ 2) =
        ∑ u ∈ maynardDivisorTupleBox H R,
          (∏ h : H, (Nat.totient (u h) : ℝ)) *
            (∑ d ∈ D, ∑ e ∈ D,
              if ∀ h : H, u h ∣ d h ∧ u h ∣ e h then
                (lambda d / (divisorTupleProduct H d : ℝ)) *
                  (lambda e / (divisorTupleProduct H e : ℝ))
              else 0) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [square_divisorTupleSum_eq_pair_sum]
    _ = ∑ u ∈ maynardDivisorTupleBox H R,
          ∑ d ∈ D, ∑ e ∈ D,
            if ∀ h : H, u h ∣ d h ∧ u h ∣ e h then
              commonDivisorTupleTerm H d e u * (lambda d * lambda e)
            else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hdiv : ∀ h : H, u h ∣ d h ∧ u h ∣ e h
      · rw [if_pos hdiv, if_pos hdiv,
          commonDivisorTupleTerm_eq_product_div]
        simp only [div_eq_mul_inv]
        ring
      · rw [if_neg hdiv, if_neg hdiv, mul_zero]
    _ = ∑ d ∈ D, ∑ e ∈ D,
          ∑ u ∈ maynardDivisorTupleBox H R,
            if ∀ h : H, u h ∣ d h ∧ u h ∣ e h then
              commonDivisorTupleTerm H d e u * (lambda d * lambda e)
            else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
    _ = ∑ d ∈ D, ∑ e ∈ D,
          ∑ u ∈ commonDivisorTupleSupport H d e,
            commonDivisorTupleTerm H d e u * (lambda d * lambda e) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      exact (sum_commonDivisorTuple_eq_box_indicator (hD d hd)
        (fun u => commonDivisorTupleTerm H d e u *
          (lambda d * lambda e))).symm

end BoundedGaps.Maynard
