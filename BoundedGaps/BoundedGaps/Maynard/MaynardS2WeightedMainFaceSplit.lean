import BoundedGaps.Maynard.MaynardS2RestrictedYWeightedFace

noncomputable section

/-!
# Main-face split of Maynard's restricted S2 transform

This is the exact finite partition preceding the error estimate in
Maynard2013v3, source lines 429--438.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators
local instance s2WeightedMainFaceDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def IsMaynardS2MainFace {H : Finset ℕ}
    (m : H) (r a : H → ℕ) : Prop :=
  ∀ h : H, h ≠ m → a h = r h

noncomputable def maynardS2WeightedMainFaceSum
    (H : Finset ℕ) (R W : ℕ) (y : (H → ℕ) → ℝ)
    (m : H) (r : H → ℕ) : ℝ :=
  ∑ a ∈ maynardDivisorTupleSupport H R W,
    if IsMaynardS2MainFace m r a then
      (y a / divisorTupleTotientProduct H a) *
        maynardS2WeightedFaceFactor H m r a
    else 0

noncomputable def maynardS2WeightedOffFaceSum
    (H : Finset ℕ) (R W : ℕ) (y : (H → ℕ) → ℝ)
    (m : H) (r : H → ℕ) : ℝ :=
  ∑ a ∈ maynardDivisorTupleSupport H R W,
    if (∀ h : H, r h ∣ a h) ∧ ¬IsMaynardS2MainFace m r a then
      (y a / divisorTupleTotientProduct H a) *
        maynardS2WeightedFaceFactor H m r a
    else 0

theorem maynardS2WeightedFaceSum_eq_main_add_off
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (m : H) {r : H → ℕ} (hrm : r m = 1) :
    (∑ a ∈ maynardDivisorTupleSupport H R W,
      if ∀ h : H, r h ∣ a h then
        (y a / divisorTupleTotientProduct H a) *
          maynardS2WeightedFaceFactor H m r a
      else 0) =
      maynardS2WeightedMainFaceSum H R W y m r +
        maynardS2WeightedOffFaceSum H R W y m r := by
  classical
  unfold maynardS2WeightedMainFaceSum maynardS2WeightedOffFaceSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hra : ∀ h : H, r h ∣ a h
  · by_cases hface : IsMaynardS2MainFace m r a <;> simp [hra, hface]
  · have hnface : ¬IsMaynardS2MainFace m r a := by
      intro hface
      apply hra
      intro h
      by_cases hh : h = m
      · subst h
        rw [hrm]
        exact one_dvd _
      · rw [hface h hh]
    simp [hnface]

theorem
    maynardS2RestrictedYFromCoefficientFromY_eq_mainFace_add_offFace
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) (m : H) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r) (hrm : r m = 1) :
    maynardS2RestrictedYFromCoefficients H
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) m r =
      (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
        maynardS2G (r h)) *
          maynardS2WeightedMainFaceSum H R W y m r +
      (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
        maynardS2G (r h)) *
          maynardS2WeightedOffFaceSum H R W y m r := by
  rw [maynardS2RestrictedYFromCoefficientFromY_eq_weightedFaceSum
    hy m hr hrm]
  rw [maynardS2WeightedFaceSum_eq_main_add_off m hrm, mul_add]

end BoundedGaps.Maynard
