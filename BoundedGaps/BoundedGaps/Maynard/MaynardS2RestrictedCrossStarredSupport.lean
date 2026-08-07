import BoundedGaps.Maynard.MaynardS2RestrictedCrossCoefficientY
import BoundedGaps.Maynard.MaynardS1StarredRoughSupport

noncomputable section

/-!
# Starred support of restricted S2 cross factors

Nonzero restricted coefficient factors force both cross lower tuples onto the
supported coordinate-one face. Their support gives the usual starred
coprimality conditions and the rough primorial support of the cross tuple.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance restrictedS2StarredSupportDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def restrictedS2LeftCoefficientFactor
    (H : Finset ℕ) (R W : ℕ) (y : (H → ℕ) → ℝ) (m : H)
    (u : H → ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) : ℝ :=
  ∑ d ∈ maynardDivisorTupleSupport H R W,
    if restrictedS2LeftCrossDivides H m u s d then
      maynardCoefficientFromY H R W y d /
        divisorTupleTotientProduct H d
    else 0

def restrictedS2RightCoefficientFactor
    (H : Finset ℕ) (R W : ℕ) (y : (H → ℕ) → ℝ) (m : H)
    (u : H → ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) : ℝ :=
  ∑ e ∈ maynardDivisorTupleSupport H R W,
    if restrictedS2RightCrossDivides H m u s e then
      maynardCoefficientFromY H R W y e /
        divisorTupleTotientProduct H e
    else 0

def IsRestrictedS2StarredCrossTuple
    (H : Finset ℕ) (R W : ℕ) (m : H) (u : H → ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) : Prop :=
  IsStarredCrossTuple H u s ∧
    (IsMaynardDivisorTuple H R W (leftCrossLowerTuple H u s) ∧
      leftCrossLowerTuple H u s m = 1) ∧
    (IsMaynardDivisorTuple H R W (rightCrossLowerTuple H u s) ∧
      rightCrossLowerTuple H u s m = 1)

theorem lowerFaceSupport_of_sum_ne_zero
    {H : Finset ℕ} {R W : ℕ} (m : H) (lower : H → ℕ)
    (hlowerPos : ∀ h : H, 0 < lower h)
    (P : (H → ℕ) → Prop) (value : (H → ℕ) → ℝ)
    (hP : ∀ d, P d ↔ ((∀ h : H, lower h ∣ d h) ∧ d m = 1))
    (hne : (∑ d ∈ maynardDivisorTupleSupport H R W,
      if P d then value d else 0) ≠ 0) :
    IsMaynardDivisorTuple H R W lower ∧ lower m = 1 := by
  classical
  obtain ⟨d, hd, hdne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hp : P d := by
    by_contra hp
    simp [hp] at hdne
  have hcond := (hP d).mp hp
  have hdSupport := isMaynardDivisorTuple_of_mem_support hd
  have hlowerBox : lower ∈ maynardDivisorTupleBox H R := by
    apply mem_maynardDivisorTupleBox_iff.mpr
    intro h
    have hdPos : 0 < d h :=
      Nat.pos_of_ne_zero (hdSupport.coordinate_squarefree h).ne_zero
    have hlowerLe : lower h ≤ d h := Nat.le_of_dvd hdPos (hcond.1 h)
    have hdProdPos : 0 < divisorTupleProduct H d :=
      Nat.pos_of_ne_zero hdSupport.2.2.ne_zero
    have hdLe : d h ≤ divisorTupleProduct H d :=
      Nat.le_of_dvd hdProdPos (divisorTupleCoordinate_dvd_product d h)
    exact ⟨hlowerPos h,
      lt_of_le_of_lt (hlowerLe.trans hdLe) hdSupport.1⟩
  have hlowerSupport :=
    isMaynardDivisorTuple_of_mem_box_of_dvd hlowerBox hdSupport hcond.1
  have hlowerOne : lower m = 1 := by
    apply Nat.dvd_one.mp
    simpa [hcond.2] using hcond.1 m
  exact ⟨hlowerSupport, hlowerOne⟩

theorem restrictedS2LeftCoefficientFactor_ne_zero_lower_face
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ} (m : H)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hu : u ∈ maynardDivisorTupleBox H R)
    (hs : s ∈ crossMoebiusTupleBox H R)
    (hne : restrictedS2LeftCoefficientFactor H R W y m u s ≠ 0) :
    IsMaynardDivisorTuple H R W (leftCrossLowerTuple H u s) ∧
      leftCrossLowerTuple H u s m = 1 := by
  unfold restrictedS2LeftCoefficientFactor at hne
  apply lowerFaceSupport_of_sum_ne_zero m (leftCrossLowerTuple H u s)
    (leftCrossLowerTuple_pos hu hs) (restrictedS2LeftCrossDivides H m u s)
    (fun d => maynardCoefficientFromY H R W y d /
      divisorTupleTotientProduct H d) _ hne
  intro d
  unfold restrictedS2LeftCrossDivides
  constructor
  · rintro ⟨hcross, hm⟩
    exact ⟨leftCrossLowerTuple_dvd_iff.mpr hcross, hm⟩
  · rintro ⟨hdiv, hm⟩
    exact ⟨leftCrossLowerTuple_dvd_iff.mp hdiv, hm⟩

theorem restrictedS2RightCoefficientFactor_ne_zero_lower_face
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ} (m : H)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hu : u ∈ maynardDivisorTupleBox H R)
    (hs : s ∈ crossMoebiusTupleBox H R)
    (hne : restrictedS2RightCoefficientFactor H R W y m u s ≠ 0) :
    IsMaynardDivisorTuple H R W (rightCrossLowerTuple H u s) ∧
      rightCrossLowerTuple H u s m = 1 := by
  unfold restrictedS2RightCoefficientFactor at hne
  apply lowerFaceSupport_of_sum_ne_zero m (rightCrossLowerTuple H u s)
    (rightCrossLowerTuple_pos hu hs) (restrictedS2RightCrossDivides H m u s)
    (fun e => maynardCoefficientFromY H R W y e /
      divisorTupleTotientProduct H e) _ hne
  intro e
  unfold restrictedS2RightCrossDivides
  constructor
  · rintro ⟨hcross, hm⟩
    exact ⟨rightCrossLowerTuple_dvd_iff.mpr hcross, hm⟩
  · rintro ⟨hdiv, hm⟩
    exact ⟨rightCrossLowerTuple_dvd_iff.mp hdiv, hm⟩

theorem isStarredCrossTuple_of_lower_support
    {H : Finset ℕ} {R W : ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hlSupport : IsMaynardDivisorTuple H R W (leftCrossLowerTuple H u s))
    (hrSupport : IsMaynardDivisorTuple H R W (rightCrossLowerTuple H u s)) :
    IsStarredCrossTuple H u s := by
  constructor
  · intro ab hab
    have habNe : ab.1 ≠ ab.2 := (Finset.mem_filter.mp hab).2
    have hright := hrSupport.coordinates_coprime habNe
    have hleft := hlSupport.coordinates_coprime habNe
    exact ⟨
      Nat.Coprime.of_dvd
        (cross_dvd_rightCrossLowerTuple u s ab hab)
        (u_dvd_rightCrossLowerTuple H u s ab.1) hright.symm,
      Nat.Coprime.of_dvd
        (cross_dvd_leftCrossLowerTuple u s ab hab)
        (u_dvd_leftCrossLowerTuple H u s ab.2) hleft⟩
  · intro ab cd hab hcd habcd hshared
    rcases hshared with hfirst | hsecond
    · have hne : ab.2 ≠ cd.2 := by
        intro h
        apply habcd
        exact Prod.ext hfirst h
      have hcop := hrSupport.coordinates_coprime hne
      exact Nat.Coprime.of_dvd
        (cross_dvd_rightCrossLowerTuple u s ab hab)
        (cross_dvd_rightCrossLowerTuple u s cd hcd) hcop
    · have hne : ab.1 ≠ cd.1 := by
        intro h
        apply habcd
        exact Prod.ext h hsecond
      have hcop := hlSupport.coordinates_coprime hne
      exact Nat.Coprime.of_dvd
        (cross_dvd_leftCrossLowerTuple u s ab hab)
        (cross_dvd_leftCrossLowerTuple u s cd hcd) hcop

theorem isRestrictedS2StarredCrossTuple_of_factors_ne_zero
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ} (m : H)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hu : u ∈ maynardDivisorTupleBox H R)
    (hs : s ∈ crossMoebiusTupleBox H R)
    (hl : restrictedS2LeftCoefficientFactor H R W y m u s ≠ 0)
    (hr : restrictedS2RightCoefficientFactor H R W y m u s ≠ 0) :
    IsRestrictedS2StarredCrossTuple H R W m u s := by
  have hlFace :=
    restrictedS2LeftCoefficientFactor_ne_zero_lower_face m hu hs hl
  have hrFace :=
    restrictedS2RightCoefficientFactor_ne_zero_lower_face m hu hs hr
  exact ⟨isStarredCrossTuple_of_lower_support hlFace.1 hrFace.1,
    hlFace, hrFace⟩

theorem roughCrossCoordinate_of_restrictedS2LeftFactor_ne_zero
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ} (m : H)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hu : u ∈ maynardDivisorTupleBox H R)
    (hs : s ∈ crossMoebiusTupleBox H R)
    (hl : restrictedS2LeftCoefficientFactor H R (primorial D) y m u s ≠ 0)
    (ab : H × H) (hab : ab ∈ offDiagonalPairs H) :
    s ab hab ∈ squarefreeRoughUnitSupport D R := by
  have hlSupport :=
    (restrictedS2LeftCoefficientFactor_ne_zero_lower_face m hu hs hl).1
  have hsMem := (Finset.mem_pi.mp hs) ab hab
  have hsBounds := Finset.mem_Icc.mp hsMem
  let n := s ab hab
  have hnDvd : n ∣ leftCrossLowerTuple H u s ab.1 :=
    cross_dvd_leftCrossLowerTuple u s ab hab
  have hnSquarefree : Squarefree n :=
    (hlSupport.coordinate_squarefree ab.1).squarefree_of_dvd hnDvd
  have hnCoprime : Nat.Coprime n (primorial D) :=
    Nat.Coprime.of_dvd_left hnDvd
      (hlSupport.coordinate_coprime_W ab.1)
  rw [squarefreeRoughUnitSupport, Finset.mem_insert]
  by_cases hnOne : n = 1
  · exact Or.inl hnOne
  · apply Or.inr
    rw [squarefreeRoughSupport, Finset.mem_filter]
    refine ⟨Finset.mem_Icc.mpr ⟨?_, hsBounds.2⟩,
      hnSquarefree, ?_⟩
    · have hnPos : 0 < n := hsBounds.1
      omega
    · intro p hpMem
      have hpPrime := Nat.prime_of_mem_primeFactors hpMem
      have hpDvd := Nat.dvd_of_mem_primeFactors hpMem
      have hpGt : D < p :=
        prime_gt_of_dvd_coprime_primorial hpPrime hpDvd hnCoprime
      have hpLeN : p ≤ n := Nat.le_of_dvd hsBounds.1 hpDvd
      rw [roughPrimeSupport, Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, hpLeN.trans hsBounds.2⟩,
        hpPrime⟩

theorem roughCrossTupleSupport_of_restrictedS2LeftFactor_ne_zero
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ} (m : H)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hu : u ∈ maynardDivisorTupleBox H R)
    (hs : s ∈ crossMoebiusTupleBox H R)
    (hl : restrictedS2LeftCoefficientFactor H R (primorial D) y m u s ≠ 0) :
    s ∈ roughCrossTupleSupport H D R := by
  rw [roughCrossTupleSupport, Finset.mem_pi]
  intro ab hab
  exact roughCrossCoordinate_of_restrictedS2LeftFactor_ne_zero
    m hu hs hl ab hab

end BoundedGaps.Maynard
