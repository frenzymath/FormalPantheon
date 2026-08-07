import BoundedGaps.Maynard.MaynardS2YFaceSupport
import BoundedGaps.Maynard.MaynardS2WeightedDivisorInterval

noncomputable section

/-!
# Exact weighted-face formula for Maynard's restricted S2 transform

This file substitutes the inverse Y coefficient, swaps the two finite divisor
sums, and evaluates the inner weighted divisor interval. It formalizes the
exact identities in Maynard2013v3, source lines 417--430, before the later
error estimate.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators
local instance s2RestrictedYWeightedFaceDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

noncomputable def maynardS2WeightedFaceFactor
    (H : Finset ℕ) (m : H) (r a : H → ℕ) : ℝ :=
  ∏ h ∈ Finset.univ.erase m,
    (ArithmeticFunction.moebius (a h) : ℝ) * (r h : ℝ) /
      Nat.totient (a h)

theorem maynardCoefficientFromY_div_totientProduct_eq_sum
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y)
    {d : H → ℕ} (hd : IsMaynardDivisorTuple H R W d) :
    maynardCoefficientFromY H R W y d /
        divisorTupleTotientProduct H d =
      ∑ a ∈ maynardDivisorTupleSupport H R W,
        if ∀ h : H, d h ∣ a h then
          (∏ h : H,
            (ArithmeticFunction.moebius (d h) : ℝ) * (d h : ℝ) /
              Nat.totient (d h)) *
            (y a / divisorTupleTotientProduct H a)
        else 0 := by
  classical
  have hdCop : Nat.Coprime (divisorTupleProduct H d) W := hd.2.1
  have hsum :
      (∑ a ∈ maynardDivisorTupleBox H R,
        if divisorTupleProduct H a < R ∧ (∀ h : H, d h ∣ a h) then
          y a / ∏ h : H, (Nat.totient (a h) : ℝ)
        else 0) =
      ∑ a ∈ maynardDivisorTupleSupport H R W,
        if ∀ h : H, d h ∣ a h then
          y a / divisorTupleTotientProduct H a
        else 0 := by
    calc
      (∑ a ∈ maynardDivisorTupleBox H R,
          if divisorTupleProduct H a < R ∧ (∀ h : H, d h ∣ a h) then
            y a / ∏ h : H, (Nat.totient (a h) : ℝ)
          else 0) =
          ∑ a ∈ maynardDivisorTupleSupport H R W,
            if divisorTupleProduct H a < R ∧ (∀ h : H, d h ∣ a h) then
              y a / ∏ h : H, (Nat.totient (a h) : ℝ)
            else 0 := by
        symm
        apply Finset.sum_subset
        · intro a ha
          exact (mem_maynardDivisorTupleSupport_iff.mp ha).1
        · intro a haBox haNot
          have haNotMaynard : ¬IsMaynardDivisorTuple H R W a := by
            intro ha
            exact haNot (mem_maynardDivisorTupleSupport_iff.mpr ⟨haBox, ha⟩)
          have hya : y a = 0 := by
            by_contra hya
            exact haNotMaynard (hy a hya)
          simp [hya]
      _ = ∑ a ∈ maynardDivisorTupleSupport H R W,
            if ∀ h : H, d h ∣ a h then
              y a / divisorTupleTotientProduct H a
            else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        have haSupport := isMaynardDivisorTuple_of_mem_support ha
        simp [haSupport.1, divisorTupleTotientProduct]
  unfold maynardCoefficientFromY
  rw [if_pos hdCop, hsum]
  calc
    ((∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * (d h : ℝ)) *
          ∑ a ∈ maynardDivisorTupleSupport H R W,
            if ∀ h : H, d h ∣ a h then
              y a / divisorTupleTotientProduct H a
            else 0) /
        divisorTupleTotientProduct H d =
      (∏ h : H,
          (ArithmeticFunction.moebius (d h) : ℝ) * (d h : ℝ) /
            Nat.totient (d h)) *
        ∑ a ∈ maynardDivisorTupleSupport H R W,
          if ∀ h : H, d h ∣ a h then
            y a / divisorTupleTotientProduct H a
          else 0 := by
      unfold divisorTupleTotientProduct
      rw [Finset.prod_div_distrib]
      ring
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hda : ∀ h : H, d h ∣ a h
      · rw [if_pos hda, if_pos hda]
      · rw [if_neg hda, if_neg hda]
        simp

theorem sum_maynardSupport_restricted_weighted_between
    {H : Finset ℕ} {R W : ℕ} (m : H) {r a : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r)
    (ha : IsMaynardDivisorTuple H R W a)
    (hrm : r m = 1) (hra : ∀ h : H, r h ∣ a h) :
    (∑ d ∈ maynardDivisorTupleSupport H R W,
      if ((∀ h : H, r h ∣ d h) ∧ d m = 1 ∧
          (∀ h : H, d h ∣ a h)) then
        ∏ h : H,
          (ArithmeticFunction.moebius (d h) : ℝ) * (d h : ℝ) /
            Nat.totient (d h)
      else 0) =
      maynardS2WeightedFaceFactor H m r a := by
  classical
  let weight : ℕ → ℝ := fun n =>
    (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) / Nat.totient n
  have hfilter :
      (maynardDivisorTupleSupport H R W).filter
          (fun d => (∀ h : H, r h ∣ d h) ∧ d m = 1 ∧
            (∀ h : H, d h ∣ a h)) =
        (upperDivisorTupleInterval H r a).filter (fun d => d m = 1) := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hdSupport, hrd, hdm, hda⟩
      refine ⟨?_, hdm⟩
      simp only [upperDivisorTupleInterval, Fintype.mem_piFinset]
      intro h
      apply Finset.mem_filter.mpr
      exact ⟨Nat.mem_divisors.mpr
        ⟨hda h, (ha.coordinate_squarefree h).ne_zero⟩, hrd h⟩
    · rintro ⟨hdInterval, hdm⟩
      have hdFiltered :
          d ∈ (maynardDivisorTupleBox H R).filter
            (fun d => (∀ h : H, r h ∣ d h) ∧
              (∀ h : H, d h ∣ a h)) := by
        rw [filter_maynardBox_between_eq_upperDivisorTupleInterval ha]
        exact hdInterval
      have hdData := Finset.mem_filter.mp hdFiltered
      have hdMaynard :=
        isMaynardDivisorTuple_of_mem_box_of_dvd hdData.1 ha hdData.2.2
      exact ⟨mem_maynardDivisorTupleSupport_iff.mpr
        ⟨hdData.1, hdMaynard⟩, hdData.2.1, hdm, hdData.2.2⟩
  let localInterval : H → Finset ℕ := fun h =>
    if h = m then {1} else upperDivisorInterval (r h) (a h)
  have hrestricted :
      (upperDivisorTupleInterval H r a).filter (fun d => d m = 1) =
        Fintype.piFinset localInterval := by
    ext d
    simp only [Finset.mem_filter, upperDivisorTupleInterval,
      Fintype.mem_piFinset]
    constructor
    · rintro ⟨hdInterval, hdm⟩ h
      by_cases hh : h = m
      · subst h
        simp [localInterval, hdm]
      · simpa [localInterval, hh] using hdInterval h
    · intro hdLocal
      constructor
      · intro h
        by_cases hh : h = m
        · subst h
          have hdm : d m = 1 := by
            simpa [localInterval] using hdLocal m
          rw [hdm]
          apply Finset.mem_filter.mpr
          exact ⟨Nat.mem_divisors.mpr
            ⟨one_dvd _, (ha.coordinate_squarefree m).ne_zero⟩, by
              rw [hrm]⟩
        · simpa [localInterval, hh] using hdLocal h
      · simpa [localInterval] using hdLocal m
  rw [← Finset.sum_filter, hfilter, hrestricted]
  change (∑ d ∈ Fintype.piFinset localInterval,
      ∏ h : H, weight (d h)) = maynardS2WeightedFaceFactor H m r a
  rw [← Finset.prod_univ_sum localInterval (fun _ n => weight n)]
  calc
    (∏ h : H, ∑ n ∈ localInterval h, weight n) =
        ∏ h : H, if h = m then 1 else
          (ArithmeticFunction.moebius (a h) : ℝ) * (r h : ℝ) /
            Nat.totient (a h) := by
      apply Finset.prod_congr rfl
      intro h hhMem
      by_cases hh : h = m
      · subst h
        simp [localInterval, weight]
      · rw [if_neg hh]
        simpa [localInterval, hh, weight] using
          (sum_moebius_mul_div_totient_upperDivisorInterval
            (ha.coordinate_squarefree h)
            (Nat.pos_of_ne_zero (hr.coordinate_squarefree h).ne_zero)
            (hra h))
    _ = maynardS2WeightedFaceFactor H m r a := by
      unfold maynardS2WeightedFaceFactor
      have herase : (Finset.univ.erase m : Finset H) =
          Finset.univ.filter (fun h => h ≠ m) := by
        ext h
        simp
      rw [herase, Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro h hhMem
      by_cases hh : h = m <;> simp [hh]

theorem maynardS2RestrictedYFromCoefficientFromY_eq_weightedFaceSum
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) (m : H) {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r) (hrm : r m = 1) :
    maynardS2RestrictedYFromCoefficients H
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) m r =
      (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
        maynardS2G (r h)) *
        ∑ a ∈ maynardDivisorTupleSupport H R W,
          if ∀ h : H, r h ∣ a h then
            (y a / divisorTupleTotientProduct H a) *
              maynardS2WeightedFaceFactor H m r a
          else 0 := by
  classical
  let weight : (H → ℕ) → ℝ := fun d =>
    ∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * (d h : ℝ) /
      Nat.totient (d h)
  let yWeight : (H → ℕ) → ℝ := fun a =>
    y a / divisorTupleTotientProduct H a
  have hinner :
      (∑ d ∈ maynardDivisorTupleSupport H R W,
        if (∀ h : H, r h ∣ d h) ∧ d m = 1 then
          maynardCoefficientFromY H R W y d /
            divisorTupleTotientProduct H d
        else 0) =
      ∑ a ∈ maynardDivisorTupleSupport H R W,
        if ∀ h : H, r h ∣ a h then
          yWeight a * maynardS2WeightedFaceFactor H m r a
        else 0 := by
    calc
      (∑ d ∈ maynardDivisorTupleSupport H R W,
          if (∀ h : H, r h ∣ d h) ∧ d m = 1 then
            maynardCoefficientFromY H R W y d /
              divisorTupleTotientProduct H d
          else 0) =
          ∑ d ∈ maynardDivisorTupleSupport H R W,
            ∑ a ∈ maynardDivisorTupleSupport H R W,
              if ((∀ h : H, r h ∣ d h) ∧ d m = 1 ∧
                  (∀ h : H, d h ∣ a h)) then
                weight d * yWeight a
              else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdSupport := isMaynardDivisorTuple_of_mem_support hd
        by_cases hrd : (∀ h : H, r h ∣ d h) ∧ d m = 1
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
              if ((∀ h : H, r h ∣ d h) ∧ d m = 1 ∧
                  (∀ h : H, d h ∣ a h)) then
                weight d * yWeight a
              else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ a ∈ maynardDivisorTupleSupport H R W,
            if ∀ h : H, r h ∣ a h then
              yWeight a * maynardS2WeightedFaceFactor H m r a
            else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        have haSupport := isMaynardDivisorTuple_of_mem_support ha
        by_cases hra : ∀ h : H, r h ∣ a h
        · rw [if_pos hra]
          calc
            (∑ d ∈ maynardDivisorTupleSupport H R W,
                if ((∀ h : H, r h ∣ d h) ∧ d m = 1 ∧
                    (∀ h : H, d h ∣ a h)) then
                  weight d * yWeight a
                else 0) =
                (∑ d ∈ maynardDivisorTupleSupport H R W,
                  if ((∀ h : H, r h ∣ d h) ∧ d m = 1 ∧
                      (∀ h : H, d h ∣ a h)) then
                    weight d
                  else 0) * yWeight a := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hcond : (∀ h : H, r h ∣ d h) ∧ d m = 1 ∧
                  (∀ h : H, d h ∣ a h) <;> simp [hcond]
            _ = maynardS2WeightedFaceFactor H m r a * yWeight a := by
              rw [sum_maynardSupport_restricted_weighted_between
                m hr haSupport hrm hra]
            _ = yWeight a * maynardS2WeightedFaceFactor H m r a :=
              mul_comm _ _
        · rw [if_neg hra]
          apply Finset.sum_eq_zero
          intro d hd
          rw [if_neg]
          intro hcond
          apply hra
          intro h
          exact dvd_trans (hcond.1 h) (hcond.2.2 h)
  unfold maynardS2RestrictedYFromCoefficients
  apply congrArg (fun S : ℝ =>
    (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
      maynardS2G (r h)) * S)
  simpa [yWeight] using hinner

end BoundedGaps.Maynard
