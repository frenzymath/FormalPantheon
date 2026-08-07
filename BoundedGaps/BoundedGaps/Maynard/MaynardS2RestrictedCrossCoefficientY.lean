import BoundedGaps.Maynard.MaynardS2RestrictedCrossFactorization
import BoundedGaps.Maynard.MaynardS2RestrictedYWeightedFace
import BoundedGaps.Maynard.MaynardS1CrossLowerTuples

noncomputable section

/-!
# Coefficient-to-Y substitution for restricted S2 cross factors

The coordinate-one restriction in each factored cross coefficient sum is
converted exactly to the weighted-face `Y` sum. This is a finite identity;
the later reciprocal-`g` estimate is separate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance restrictedS2CrossCoefficientYDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

theorem restrictedS2CoefficientSum_eq_weightedFaceSum_of_lower
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y)
    (m : H) (lower : H → ℕ) (P : (H → ℕ) → Prop)
    (hlower : IsMaynardDivisorTuple H R W lower)
    (hlower_m : lower m = 1)
    (hP : ∀ d, P d ↔ ((∀ h : H, lower h ∣ d h) ∧ d m = 1)) :
    (∑ d ∈ maynardDivisorTupleSupport H R W,
        if P d then
          maynardCoefficientFromY H R W y d /
            divisorTupleTotientProduct H d
        else 0) =
      ∑ a ∈ maynardDivisorTupleSupport H R W,
        if ∀ h : H, lower h ∣ a h then
          (y a / divisorTupleTotientProduct H a) *
            maynardS2WeightedFaceFactor H m lower a
        else 0 := by
  classical
  let weight : (H → ℕ) → ℝ := fun d =>
    ∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * (d h : ℝ) /
      Nat.totient (d h)
  let yWeight : (H → ℕ) → ℝ := fun a =>
    y a / divisorTupleTotientProduct H a
  have hinner :
      (∑ d ∈ maynardDivisorTupleSupport H R W,
        if (∀ h : H, lower h ∣ d h) ∧ d m = 1 then
          maynardCoefficientFromY H R W y d /
            divisorTupleTotientProduct H d
        else 0) =
      ∑ a ∈ maynardDivisorTupleSupport H R W,
        if ∀ h : H, lower h ∣ a h then
          yWeight a * maynardS2WeightedFaceFactor H m lower a
        else 0 := by
    calc
      (∑ d ∈ maynardDivisorTupleSupport H R W,
          if (∀ h : H, lower h ∣ d h) ∧ d m = 1 then
            maynardCoefficientFromY H R W y d /
              divisorTupleTotientProduct H d
          else 0) =
          ∑ d ∈ maynardDivisorTupleSupport H R W,
            ∑ a ∈ maynardDivisorTupleSupport H R W,
              if ((∀ h : H, lower h ∣ d h) ∧ d m = 1 ∧
                  (∀ h : H, d h ∣ a h)) then
                weight d * yWeight a
              else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdSupport := isMaynardDivisorTuple_of_mem_support hd
        by_cases hrd : (∀ h : H, lower h ∣ d h) ∧ d m = 1
        · rw [if_pos hrd,
            maynardCoefficientFromY_div_totientProduct_eq_sum hy hdSupport]
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hda : ∀ h : H, d h ∣ a h
          · simp [hrd, hda, weight, yWeight]
          · rw [if_neg hda, if_neg]
            intro hcond
            exact hda hcond.2.2
        · rw [if_neg hrd]
          symm
          apply Finset.sum_eq_zero
          intro a ha
          rw [if_neg]
          intro hcond
          exact hrd ⟨hcond.1, hcond.2.1⟩
      _ = ∑ a ∈ maynardDivisorTupleSupport H R W,
            ∑ d ∈ maynardDivisorTupleSupport H R W,
              if ((∀ h : H, lower h ∣ d h) ∧ d m = 1 ∧
                  (∀ h : H, d h ∣ a h)) then
                weight d * yWeight a
              else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ a ∈ maynardDivisorTupleSupport H R W,
            if ∀ h : H, lower h ∣ a h then
              yWeight a * maynardS2WeightedFaceFactor H m lower a
            else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        have haSupport := isMaynardDivisorTuple_of_mem_support ha
        by_cases hra : ∀ h : H, lower h ∣ a h
        · rw [if_pos hra]
          calc
            (∑ d ∈ maynardDivisorTupleSupport H R W,
                if ((∀ h : H, lower h ∣ d h) ∧ d m = 1 ∧
                    (∀ h : H, d h ∣ a h)) then
                  weight d * yWeight a
                else 0) =
                (∑ d ∈ maynardDivisorTupleSupport H R W,
                  if ((∀ h : H, lower h ∣ d h) ∧ d m = 1 ∧
                      (∀ h : H, d h ∣ a h)) then
                    weight d
                  else 0) * yWeight a := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hcond : (∀ h : H, lower h ∣ d h) ∧ d m = 1 ∧
                  (∀ h : H, d h ∣ a h) <;> simp [hcond]
            _ = maynardS2WeightedFaceFactor H m lower a * yWeight a := by
              rw [sum_maynardSupport_restricted_weighted_between
                m hlower haSupport hlower_m hra]
            _ = yWeight a * maynardS2WeightedFaceFactor H m lower a := by
              rw [mul_comm]
        · rw [if_neg hra]
          apply Finset.sum_eq_zero
          intro d hd
          rw [if_neg]
          intro hcond
          apply hra
          intro h
          exact dvd_trans (hcond.1 h) (hcond.2.2 h)
  calc
    (∑ d ∈ maynardDivisorTupleSupport H R W,
        if P d then
          maynardCoefficientFromY H R W y d /
            divisorTupleTotientProduct H d
        else 0) =
        ∑ d ∈ maynardDivisorTupleSupport H R W,
          if (∀ h : H, lower h ∣ d h) ∧ d m = 1 then
            maynardCoefficientFromY H R W y d /
              divisorTupleTotientProduct H d
          else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hp : P d
      · have hcond := (hP d).mp hp
        rw [if_pos hp, if_pos hcond]
      · have hcond : ¬((∀ h : H, lower h ∣ d h) ∧ d m = 1) := by
          intro h
          exact hp ((hP d).mpr h)
        rw [if_neg hp, if_neg hcond]
    _ = ∑ a ∈ maynardDivisorTupleSupport H R W,
          if ∀ h : H, lower h ∣ a h then
            (y a / divisorTupleTotientProduct H a) *
              maynardS2WeightedFaceFactor H m lower a
          else 0 := by
      simpa [yWeight] using hinner

theorem restrictedS2LeftCoefficientSum_eq_weightedFaceSum
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) (m : H)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hlower : IsMaynardDivisorTuple H R W (leftCrossLowerTuple H u s))
    (hlower_m : leftCrossLowerTuple H u s m = 1) :
    (∑ d ∈ maynardDivisorTupleSupport H R W,
        if restrictedS2LeftCrossDivides H m u s d then
          maynardCoefficientFromY H R W y d /
            divisorTupleTotientProduct H d
        else 0) =
      ∑ a ∈ maynardDivisorTupleSupport H R W,
        if ∀ h : H, leftCrossLowerTuple H u s h ∣ a h then
          (y a / divisorTupleTotientProduct H a) *
            maynardS2WeightedFaceFactor H m (leftCrossLowerTuple H u s) a
        else 0 := by
  apply restrictedS2CoefficientSum_eq_weightedFaceSum_of_lower hy m
    (leftCrossLowerTuple H u s) (restrictedS2LeftCrossDivides H m u s)
    hlower hlower_m
  intro d
  rw [restrictedS2LeftCrossDivides, leftCrossLowerTuple_dvd_iff]

theorem restrictedS2RightCoefficientSum_eq_weightedFaceSum
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) (m : H)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hlower : IsMaynardDivisorTuple H R W (rightCrossLowerTuple H u s))
    (hlower_m : rightCrossLowerTuple H u s m = 1) :
    (∑ e ∈ maynardDivisorTupleSupport H R W,
        if restrictedS2RightCrossDivides H m u s e then
          maynardCoefficientFromY H R W y e /
            divisorTupleTotientProduct H e
        else 0) =
      ∑ a ∈ maynardDivisorTupleSupport H R W,
        if ∀ h : H, rightCrossLowerTuple H u s h ∣ a h then
          (y a / divisorTupleTotientProduct H a) *
            maynardS2WeightedFaceFactor H m (rightCrossLowerTuple H u s) a
        else 0 := by
  apply restrictedS2CoefficientSum_eq_weightedFaceSum_of_lower hy m
    (rightCrossLowerTuple H u s) (restrictedS2RightCrossDivides H m u s)
    hlower hlower_m
  intro e
  rw [restrictedS2RightCrossDivides, rightCrossLowerTuple_dvd_iff]

end BoundedGaps.Maynard
