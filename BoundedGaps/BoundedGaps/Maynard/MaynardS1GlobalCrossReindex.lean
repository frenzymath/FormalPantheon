import BoundedGaps.Maynard.MaynardS1CrossBoxes

noncomputable section

/-!
# Global-box reindexing of the nontrivial S1 correction

This is an exact finite interchange and factorization. Starred coprimality
restrictions and estimates are deliberately deferred.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance globalCrossDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def LeftCrossDivides
    (H : Finset ℕ) (u : H → ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ)
    (d : H → ℕ) : Prop :=
  (∀ h : H, u h ∣ d h) ∧
    ∀ (ab : H × H) (hab : ab ∈ offDiagonalPairs H),
      s ab hab ∣ d ab.1

def RightCrossDivides
    (H : Finset ℕ) (u : H → ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ)
    (e : H → ℕ) : Prop :=
  (∀ h : H, u h ∣ e h) ∧
    ∀ (ab : H × H) (hab : ab ∈ offDiagonalPairs H),
      s ab hab ∣ e ab.2

def nontrivialAuxiliaryGlobalQuadrupleSum
    (H : Finset ℕ) (R : ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D, ∑ s ∈ crossMoebiusTupleBox H R,
    ∑ u ∈ maynardDivisorTupleBox H R,
      if s ≠ oneCrossMoebiusTuple H ∧
          LeftCrossDivides H u s d ∧ RightCrossDivides H u s e then
        crossMoebiusTupleTerm H s *
          ((∏ h : H, (Nat.totient (u h) : ℝ)) *
            ((lambda d / (divisorTupleProduct H d : ℝ)) *
              (lambda e / (divisorTupleProduct H e : ℝ))))
      else 0

def nontrivialAuxiliaryFactoredSum
    (H : Finset ℕ) (R : ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ s ∈ crossMoebiusTupleBox H R,
    if s ≠ oneCrossMoebiusTuple H then
      crossMoebiusTupleTerm H s *
        ∑ u ∈ maynardDivisorTupleBox H R,
          (∏ h : H, (Nat.totient (u h) : ℝ)) *
            (∑ d ∈ D, if LeftCrossDivides H u s d then
              lambda d / (divisorTupleProduct H d : ℝ) else 0) *
            (∑ e ∈ D, if RightCrossDivides H u s e then
              lambda e / (divisorTupleProduct H e : ℝ) else 0)
    else 0

theorem cross_and_common_iff_left_right
    {H : Finset ℕ}
    {u d e : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ} :
    CrossTupleDivides H s d e ∧
        (∀ h : H, u h ∣ d h ∧ u h ∣ e h) ↔
      LeftCrossDivides H u s d ∧ RightCrossDivides H u s e := by
  constructor
  · rintro ⟨hs, hu⟩
    exact ⟨⟨fun h => (hu h).1, fun ab hab => (hs ab hab).1⟩,
      ⟨fun h => (hu h).2, fun ab hab => (hs ab hab).2⟩⟩
  · rintro ⟨hl, hr⟩
    exact ⟨fun ab hab => ⟨hl.2 ab hab, hr.2 ab hab⟩,
      fun h => ⟨hl.1 h, hr.1 h⟩⟩

theorem mul_filtered_sums_eq_pair_sum
    (D : Finset ι) (E : Finset κ)
    (P : ι → Prop) (Q : κ → Prop)
    (f : ι → ℝ) (g : κ → ℝ) :
    (∑ d ∈ D, if P d then f d else 0) *
        (∑ e ∈ E, if Q e then g e else 0) =
      ∑ d ∈ D, ∑ e ∈ E,
        if P d ∧ Q e then f d * g e else 0 := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hP : P d <;> by_cases hQ : Q e <;> simp [hP, hQ]

theorem nontrivialAuxiliaryMobiusSum_eq_globalQuadrupleSum
    {H : Finset ℕ} {R W : ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    nontrivialAuxiliaryMobiusSum H D lambda =
      nontrivialAuxiliaryGlobalQuadrupleSum H R D lambda := by
  classical
  unfold nontrivialAuxiliaryMobiusSum
    nontrivialAuxiliaryGlobalQuadrupleSum
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hsFilter := filter_crossMoebiusTupleBox_ne_one_eq_erase_support
    (hD d hd) (e := e)
  rw [← hsFilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hsCond : s ≠ oneCrossMoebiusTuple H ∧
      CrossTupleDivides H s d e
  · rw [if_pos hsCond]
    rw [sum_commonDivisorTuple_eq_box_indicator (hD d hd)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases huCond : ∀ h : H, u h ∣ d h ∧ u h ∣ e h
    · rw [if_pos huCond]
      have hlr := cross_and_common_iff_left_right.mp ⟨hsCond.2, huCond⟩
      rw [if_pos ⟨hsCond.1, hlr.1, hlr.2⟩]
      rw [commonDivisorTupleTerm_eq_product_div]
      simp only [div_eq_mul_inv]
      ring
    · rw [if_neg huCond]
      have hnot : ¬(s ≠ oneCrossMoebiusTuple H ∧
          LeftCrossDivides H u s d ∧ RightCrossDivides H u s e) := by
        rintro ⟨hsNe, hl, hr⟩
        exact huCond (cross_and_common_iff_left_right.mpr ⟨hl, hr⟩).2
      rw [if_neg hnot]
      simp
  · rw [if_neg hsCond]
    symm
    apply Finset.sum_eq_zero
    intro u hu
    rw [if_neg]
    rintro ⟨hsNe, hl, hr⟩
    apply hsCond
    exact ⟨hsNe, (cross_and_common_iff_left_right.mpr ⟨hl, hr⟩).1⟩

theorem globalQuadrupleSum_eq_factoredSum
    (H : Finset ℕ) (R : ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) :
    nontrivialAuxiliaryGlobalQuadrupleSum H R D lambda =
      nontrivialAuxiliaryFactoredSum H R D lambda := by
  classical
  unfold nontrivialAuxiliaryGlobalQuadrupleSum
    nontrivialAuxiliaryFactoredSum
  let S := crossMoebiusTupleBox H R
  let U := maynardDivisorTupleBox H R
  let F := fun
      (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ)
      (u d e : H → ℕ) =>
    if s ≠ oneCrossMoebiusTuple H ∧
        LeftCrossDivides H u s d ∧ RightCrossDivides H u s e then
      crossMoebiusTupleTerm H s *
        ((∏ h : H, (Nat.totient (u h) : ℝ)) *
          ((lambda d / (divisorTupleProduct H d : ℝ)) *
            (lambda e / (divisorTupleProduct H e : ℝ))))
    else 0
  change (∑ d ∈ D, ∑ e ∈ D, ∑ s ∈ S, ∑ u ∈ U, F s u d e) = _
  calc
    (∑ d ∈ D, ∑ e ∈ D, ∑ s ∈ S, ∑ u ∈ U, F s u d e) =
        ∑ s ∈ S, ∑ u ∈ U, ∑ d ∈ D, ∑ e ∈ D, F s u d e := by
      calc
        (∑ d ∈ D, ∑ e ∈ D, ∑ s ∈ S, ∑ u ∈ U, F s u d e) =
            ∑ d ∈ D, ∑ s ∈ S, ∑ e ∈ D, ∑ u ∈ U, F s u d e := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.sum_comm]
        _ = ∑ s ∈ S, ∑ d ∈ D, ∑ e ∈ D, ∑ u ∈ U, F s u d e := by
          rw [Finset.sum_comm]
        _ = ∑ s ∈ S, ∑ d ∈ D, ∑ u ∈ U, ∑ e ∈ D, F s u d e := by
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.sum_comm]
        _ = ∑ s ∈ S, ∑ u ∈ U, ∑ d ∈ D, ∑ e ∈ D, F s u d e := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.sum_comm]
    _ = ∑ s ∈ crossMoebiusTupleBox H R,
        if s ≠ oneCrossMoebiusTuple H then
          crossMoebiusTupleTerm H s *
            ∑ u ∈ maynardDivisorTupleBox H R,
              (∏ h : H, (Nat.totient (u h) : ℝ)) *
                (∑ d ∈ D, if LeftCrossDivides H u s d then
                  lambda d / (divisorTupleProduct H d : ℝ) else 0) *
                (∑ e ∈ D, if RightCrossDivides H u s e then
                  lambda e / (divisorTupleProduct H e : ℝ) else 0)
        else 0 := by
      unfold S U
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hsNe : s ≠ oneCrossMoebiusTuple H
      · rw [if_pos hsNe, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        rw [show
          crossMoebiusTupleTerm H s *
              (((∏ h : H, (Nat.totient (u h) : ℝ)) *
                (∑ d ∈ D, if LeftCrossDivides H u s d then
                  lambda d / (divisorTupleProduct H d : ℝ) else 0)) *
                (∑ e ∈ D, if RightCrossDivides H u s e then
                  lambda e / (divisorTupleProduct H e : ℝ) else 0)) =
            (crossMoebiusTupleTerm H s *
              (∏ h : H, (Nat.totient (u h) : ℝ))) *
              ((∑ d ∈ D, if LeftCrossDivides H u s d then
                lambda d / (divisorTupleProduct H d : ℝ) else 0) *
              (∑ e ∈ D, if RightCrossDivides H u s e then
                lambda e / (divisorTupleProduct H e : ℝ) else 0)) by ring]
        rw [mul_filtered_sums_eq_pair_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        dsimp [F]
        by_cases hl : LeftCrossDivides H u s d
        · by_cases hr : RightCrossDivides H u s e
          · rw [if_pos ⟨hsNe, hl, hr⟩, if_pos ⟨hl, hr⟩]
            ring
          · simp [hr]
        · simp [hl]
      · rw [if_neg hsNe]
        apply Finset.sum_eq_zero
        intro u hu
        apply Finset.sum_eq_zero
        intro d hd
        apply Finset.sum_eq_zero
        intro e he
        dsimp [F]
        rw [if_neg (fun h => hsNe h.1)]

theorem nontrivialAuxiliaryMobiusSum_eq_factoredSum
    {H : Finset ℕ} {R W : ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    nontrivialAuxiliaryMobiusSum H D lambda =
      nontrivialAuxiliaryFactoredSum H R D lambda := by
  rw [nontrivialAuxiliaryMobiusSum_eq_globalQuadrupleSum hD]
  exact globalQuadrupleSum_eq_factoredSum H R D lambda

end BoundedGaps.Maynard
