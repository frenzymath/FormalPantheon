import BoundedGaps.Maynard.MaynardS2RestrictedStarredSummandBound
import BoundedGaps.Maynard.MaynardS1StarredSummandBound
import BoundedGaps.Maynard.ConcreteS2ReciprocalGShellLimit

noncomputable section

/-!
# Summed restricted S2 starred cross correction

The pointwise common reciprocal-`g` factor is summed over the exact
coordinate-one pre-sieved box. The resulting finite bound is then transferred
to the named incompatible restricted correction. This is the finite
summation at Maynard2013v3, proof of Lemma `lmm:S2Expression1`, source lines
384--393.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance restrictedS2CorrectionBoundDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def restrictedS2CommonCoordinateOneBox
    (H : Finset ℕ) (W R : ℕ) (m : H) : Finset (H → ℕ) :=
  Fintype.piFinset fun h =>
    if h = m then {1} else preSievedCommonCoordinateSupport W R

def restrictedS2CommonReciprocalGMass
    (H : Finset ℕ) (W R : ℕ) (m : H) : ℝ :=
  ∑ u ∈ restrictedS2CommonCoordinateOneBox H W R m,
    (1 : ℝ) / commonS2GProduct H u

theorem restrictedS2CommonCoordinateOneBox_subset_maynardDivisorTupleBox
    {H : Finset ℕ} {W R : ℕ} {m : H} (hR : 1 < R) :
    restrictedS2CommonCoordinateOneBox H W R m ⊆
      maynardDivisorTupleBox H R := by
  intro u hu
  rw [restrictedS2CommonCoordinateOneBox, Fintype.mem_piFinset] at hu
  rw [mem_maynardDivisorTupleBox_iff]
  intro h
  by_cases hm : h = m
  · subst h
    have hmem := hu m
    simp at hmem
    have hone : u m = 1 := by simpa using hmem
    simp [hone, hR]
  · have hmem := hu h
    rw [if_neg hm] at hmem
    have hdata := Finset.mem_filter.mp hmem
    exact ⟨hdata.2.1, Finset.mem_range.mp hdata.1⟩

theorem restrictedS2CommonBox_mem_of_starred
    {H : Finset ℕ} {R : ℕ} {D : ℕ} {m : H}
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hu : u ∈ maynardDivisorTupleBox H R)
    (hstar : IsRestrictedS2StarredCrossTuple H R (primorial D) m u s) :
    u ∈ restrictedS2CommonCoordinateOneBox H (primorial D) R m := by
  rw [restrictedS2CommonCoordinateOneBox, Fintype.mem_piFinset]
  intro h
  by_cases hm : h = m
  · subst h
    have hdiv := u_dvd_leftCrossLowerTuple H u s m
    have hone : u m = 1 := by
      apply Nat.dvd_one.mp
      simpa [hstar.2.1.2] using hdiv
    simp [hone]
  · rw [if_neg hm]
    rw [preSievedCommonCoordinateSupport, Finset.mem_filter]
    have hub := (mem_maynardDivisorTupleBox_iff.mp hu) h
    have hlow := hstar.2.1.1
    have hdiv := u_dvd_leftCrossLowerTuple H u s h
    exact ⟨Finset.mem_range.mpr hub.2, hub.1,
      (hlow.coordinate_squarefree h).squarefree_of_dvd hdiv,
      Nat.Coprime.of_dvd_left hdiv (hlow.coordinate_coprime_W h)⟩

theorem preSievedReciprocalGCoordinateSum_le_mean
    {W R : ℕ} :
    (∑ n ∈ preSievedCommonCoordinateSupport W R,
      (1 : ℝ) / (maynardS2G n : ℝ)) ≤
      maynardS2ReciprocalGSquarefreeMean W R := by
  classical
  let support := squarefreeCoprimeCoordinateSupport W R
  have hsubset : preSievedCommonCoordinateSupport W R ⊆ support := by
    intro n hn
    have hdata := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr
      ⟨hdata.2.1, Nat.le_of_lt (Finset.mem_range.mp hdata.1)⟩,
      hdata.2.2.1, hdata.2.2.2⟩
  calc
    (∑ n ∈ preSievedCommonCoordinateSupport W R,
        (1 : ℝ) / (maynardS2G n : ℝ)) =
        ∑ n ∈ preSievedCommonCoordinateSupport W R,
          maynardS2ReciprocalGSquarefreeAF W n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hdata := Finset.mem_filter.mp hn
      rw [maynardS2ReciprocalGSquarefreeAF_apply_squarefree_of_coprime
        hdata.2.2.1 hdata.2.2.2]
    _ ≤ ∑ n ∈ support, maynardS2ReciprocalGSquarefreeAF W n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n hn hnNot
      exact maynardS2ReciprocalGSquarefreeAF_nonneg W n
    _ = maynardS2ReciprocalGSquarefreeMean W R := by
      exact maynardS2ReciprocalGSquarefreeCoordinateSupport_sum_eq_mean W R

theorem restrictedS2CommonReciprocalGMass_le
    {H : Finset ℕ} {W R : ℕ} {m : H} :
    restrictedS2CommonReciprocalGMass H W R m ≤
      (maynardS2ReciprocalGSquarefreeMean W R) ^
        (Finset.univ.erase m).card := by
  classical
  let localSupport : H → Finset ℕ := fun h =>
    if h = m then {1} else preSievedCommonCoordinateSupport W R
  have hmass :
      restrictedS2CommonReciprocalGMass H W R m =
        ∏ h : H, ∑ n ∈ localSupport h,
          (1 : ℝ) / (maynardS2G n : ℝ) := by
    unfold restrictedS2CommonReciprocalGMass
      restrictedS2CommonCoordinateOneBox commonS2GProduct
    calc
      (∑ u ∈ Fintype.piFinset localSupport,
          (1 : ℝ) / (∏ h : H, (maynardS2G (u h) : ℝ))) =
          ∑ u ∈ Fintype.piFinset localSupport,
            ∏ h : H, (1 : ℝ) / (maynardS2G (u h) : ℝ) := by
        apply Finset.sum_congr rfl
        intro u hu
        simp only [one_div, ← Finset.prod_inv_distrib]
      _ = ∏ h : H, ∑ n ∈ localSupport h,
            (1 : ℝ) / (maynardS2G n : ℝ) := by
        exact (Finset.prod_univ_sum localSupport
          (fun _ n => (1 : ℝ) / (maynardS2G n : ℝ))).symm
  have hlocal : ∀ h : H,
      (∑ n ∈ localSupport h, (1 : ℝ) / (maynardS2G n : ℝ)) ≤
        if h = m then 1 else maynardS2ReciprocalGSquarefreeMean W R := by
    intro h
    by_cases hm : h = m
    · subst h
      simp [localSupport, maynardS2G]
    · rw [if_neg hm]
      simpa [localSupport, hm] using
        (preSievedReciprocalGCoordinateSum_le_mean (W := W) (R := R))
  have hprod :
      (∏ h : H, ∑ n ∈ localSupport h,
        (1 : ℝ) / (maynardS2G n : ℝ)) ≤
        ∏ h : H, if h = m then 1 else
          maynardS2ReciprocalGSquarefreeMean W R := by
    apply Finset.prod_le_prod
    · intro h hh
      positivity
    · intro h hh
      exact hlocal h
  calc
    restrictedS2CommonReciprocalGMass H W R m =
        ∏ h : H, ∑ n ∈ localSupport h,
          (1 : ℝ) / (maynardS2G n : ℝ) := hmass
    _ ≤
        ∏ h : H, if h = m then 1 else
          maynardS2ReciprocalGSquarefreeMean W R := hprod
    _ = (maynardS2ReciprocalGSquarefreeMean W R) ^
        (Finset.univ.erase m).card := by
      have herase : (Finset.univ.erase m : Finset H) =
          Finset.univ.filter (fun h => h ≠ m) := by
        ext h
        simp
      have hprodEq :
          (∏ h ∈ Finset.univ.erase m,
            maynardS2ReciprocalGSquarefreeMean W R) =
            ∏ h : H, if h = m then 1 else
              maynardS2ReciprocalGSquarefreeMean W R := by
        rw [herase, Finset.prod_filter]
        simp
      rw [← hprodEq, Finset.prod_const]

theorem nontrivialRestrictedS2StarredRoughFactoredSum_eq_erase
    (H : Finset ℕ) (R D : ℕ) (y : (H → ℕ) → ℝ) (m : H) :
    nontrivialRestrictedS2StarredRoughFactoredSum H R D y m =
      ∑ s ∈ (roughCrossTupleSupport H D R).erase
          (oneCrossMoebiusTuple H),
        crossMoebiusTupleTerm H s *
          ∑ u ∈ maynardDivisorTupleBox H R,
            if IsRestrictedS2StarredCrossTuple H R (primorial D) m u s then
              commonS2GProduct H u *
                restrictedS2LeftCoefficientFactor H R (primorial D) y m u s *
                restrictedS2RightCoefficientFactor H R (primorial D) y m u s
            else 0 := by
  classical
  let f := fun s =>
    if s ≠ oneCrossMoebiusTuple H then
      crossMoebiusTupleTerm H s *
        ∑ u ∈ maynardDivisorTupleBox H R,
          if IsRestrictedS2StarredCrossTuple H R (primorial D) m u s then
            commonS2GProduct H u *
              restrictedS2LeftCoefficientFactor H R (primorial D) y m u s *
              restrictedS2RightCoefficientFactor H R (primorial D) y m u s
          else 0
    else 0
  have hone := oneCrossMoebiusTuple_mem_roughCrossTupleSupport H D R
  have hsplit := Finset.sum_erase_add (s := roughCrossTupleSupport H D R)
    (f := f) hone
  have hfone : f (oneCrossMoebiusTuple H) = 0 := by
    simp [f]
  unfold nontrivialRestrictedS2StarredRoughFactoredSum
  change (∑ s ∈ roughCrossTupleSupport H D R, f s) = _
  rw [hfone, add_zero] at hsplit
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro s hs
  have hsNe := (Finset.mem_erase.mp hs).1
  simp [f, hsNe, commonS2GProduct]

theorem abs_fixedRestrictedS2RoughCrossInnerSum_le
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ} {m : H} {B : ℝ}
    (hR : 1 < R) (hD : 2 ≤ D) (hB : 0 ≤ B)
    (hyBound : ∀ r,
      IsMaynardDivisorTuple H R (primorial D) r → r m = 1 →
      |maynardS2RestrictedYFromCoefficients H
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m r| ≤ B)
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hs : s ∈ roughCrossTupleSupport H D R) :
    |crossMoebiusTupleTerm H s *
        ∑ u ∈ maynardDivisorTupleBox H R,
          if IsRestrictedS2StarredCrossTuple H R (primorial D) m u s then
            commonS2GProduct H u *
              restrictedS2LeftCoefficientFactor H R (primorial D) y m u s *
              restrictedS2RightCoefficientFactor H R (primorial D) y m u s
          else 0| ≤
      B ^ 2 * roughS2CrossTupleReciprocalGSquareWeight H s *
        restrictedS2CommonReciprocalGMass H (primorial D) R m := by
  rw [Finset.mul_sum]
  calc
    |∑ u ∈ maynardDivisorTupleBox H R,
        crossMoebiusTupleTerm H s *
          (if IsRestrictedS2StarredCrossTuple H R (primorial D) m u s then
            commonS2GProduct H u *
              restrictedS2LeftCoefficientFactor H R (primorial D) y m u s *
              restrictedS2RightCoefficientFactor H R (primorial D) y m u s
          else 0)| ≤
        ∑ u ∈ maynardDivisorTupleBox H R,
          |crossMoebiusTupleTerm H s *
            (if IsRestrictedS2StarredCrossTuple H R (primorial D) m u s then
              commonS2GProduct H u *
                restrictedS2LeftCoefficientFactor H R (primorial D) y m u s *
                restrictedS2RightCoefficientFactor H R (primorial D) y m u s
            else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ maynardDivisorTupleBox H R,
          if IsRestrictedS2StarredCrossTuple H R (primorial D) m u s then
            B ^ 2 * roughS2CrossTupleReciprocalGSquareWeight H s *
              ((1 : ℝ) / commonS2GProduct H u)
          else 0 := by
      apply Finset.sum_le_sum
      intro u hu
      by_cases hstar :
          IsRestrictedS2StarredCrossTuple H R (primorial D) m u s
      · rw [if_pos hstar, if_pos hstar]
        simpa [mul_assoc] using
          abs_restrictedS2StarredCrossSummand_le_separated
            m hB hyBound hD hs hstar
      · rw [if_neg hstar, if_neg hstar, mul_zero, abs_zero]
    _ = ∑ u ∈ restrictedS2CommonCoordinateOneBox H (primorial D) R m,
          if IsRestrictedS2StarredCrossTuple H R (primorial D) m u s then
            B ^ 2 * roughS2CrossTupleReciprocalGSquareWeight H s *
              ((1 : ℝ) / commonS2GProduct H u)
          else 0 := by
      apply (Finset.sum_subset
        (restrictedS2CommonCoordinateOneBox_subset_maynardDivisorTupleBox hR)
        ?_).symm
      intro u huBox huNotCommon
      rw [if_neg]
      intro hstar
      exact huNotCommon
        (restrictedS2CommonBox_mem_of_starred huBox hstar)
    _ ≤ ∑ u ∈ restrictedS2CommonCoordinateOneBox H (primorial D) R m,
          B ^ 2 * roughS2CrossTupleReciprocalGSquareWeight H s *
            ((1 : ℝ) / commonS2GProduct H u) := by
      apply Finset.sum_le_sum
      intro u hu
      by_cases hstar :
          IsRestrictedS2StarredCrossTuple H R (primorial D) m u s
      · rw [if_pos hstar]
      · rw [if_neg hstar]
        have hU : 0 < commonS2GProduct H u := by
          unfold commonS2GProduct
          rw [restrictedS2CommonCoordinateOneBox,
            Fintype.mem_piFinset] at hu
          apply Finset.prod_pos
          intro h hh
          by_cases hm : h = m
          · subst h
            have hmem := hu m
            simp at hmem
            have hone : u m = 1 := by simpa using hmem
            rw [hone]
            simp [maynardS2G]
          · have hmem := hu h
            rw [if_neg hm] at hmem
            have hdata := Finset.mem_filter.mp hmem
            exact_mod_cast maynardS2G_pos_of_squarefree_coprime_primorial hD
              hdata.2.2.1 hdata.2.2.2
        have hweight : 0 ≤
            roughS2CrossTupleReciprocalGSquareWeight H s := by
          unfold roughS2CrossTupleReciprocalGSquareWeight
          apply Finset.prod_nonneg
          intro x hx
          apply Finset.prod_nonneg
          intro p hp
          exact maynardS2CrossPrimeSquareWeight_nonneg p
        have hInv : 0 ≤ (1 : ℝ) / commonS2GProduct H u := by
          positivity
        exact mul_nonneg (mul_nonneg (sq_nonneg B) hweight) hInv
    _ = B ^ 2 * roughS2CrossTupleReciprocalGSquareWeight H s *
        restrictedS2CommonReciprocalGMass H (primorial D) R m := by
      unfold restrictedS2CommonReciprocalGMass
      rw [Finset.mul_sum]

theorem abs_nontrivialRestrictedS2StarredRoughFactoredSum_le
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ} {m : H} {B : ℝ}
    (hR : 1 < R) (hD : 2 ≤ D) (hB : 0 ≤ B)
    (hyBound : ∀ r,
      IsMaynardDivisorTuple H R (primorial D) r → r m = 1 →
      |maynardS2RestrictedYFromCoefficients H
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m r| ≤ B) :
    |nontrivialRestrictedS2StarredRoughFactoredSum H R D y m| ≤
      B ^ 2 * roughS2CrossTupleReciprocalGSquareTail H D R *
        restrictedS2CommonReciprocalGMass H (primorial D) R m := by
  rw [nontrivialRestrictedS2StarredRoughFactoredSum_eq_erase]
  calc
    |∑ s ∈ (roughCrossTupleSupport H D R).erase
        (oneCrossMoebiusTuple H),
        crossMoebiusTupleTerm H s *
          ∑ u ∈ maynardDivisorTupleBox H R,
            if IsRestrictedS2StarredCrossTuple H R (primorial D) m u s then
              commonS2GProduct H u *
                restrictedS2LeftCoefficientFactor H R (primorial D) y m u s *
                restrictedS2RightCoefficientFactor H R (primorial D) y m u s
            else 0| ≤
        ∑ s ∈ (roughCrossTupleSupport H D R).erase
          (oneCrossMoebiusTuple H),
          |crossMoebiusTupleTerm H s *
            ∑ u ∈ maynardDivisorTupleBox H R,
              if IsRestrictedS2StarredCrossTuple H R (primorial D) m u s then
                commonS2GProduct H u *
                  restrictedS2LeftCoefficientFactor H R (primorial D) y m u s *
                  restrictedS2RightCoefficientFactor H R (primorial D) y m u s
              else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ (roughCrossTupleSupport H D R).erase
          (oneCrossMoebiusTuple H),
          B ^ 2 * roughS2CrossTupleReciprocalGSquareWeight H s *
            restrictedS2CommonReciprocalGMass H (primorial D) R m := by
      apply Finset.sum_le_sum
      intro s hs
      exact abs_fixedRestrictedS2RoughCrossInnerSum_le
        hR hD hB hyBound (Finset.mem_of_mem_erase hs)
    _ = B ^ 2 * roughS2CrossTupleReciprocalGSquareTail H D R *
        restrictedS2CommonReciprocalGMass H (primorial D) R m := by
      unfold roughS2CrossTupleReciprocalGSquareTail
      nth_rw 1 [← Finset.sum_mul]
      rw [Finset.mul_sum]

theorem abs_incompatibleRestrictedS2_le_crossTail_mul_commonMass
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ} {m : H} {B : ℝ}
    (hR : 1 < R) (hD : 2 ≤ D) (hB : 0 ≤ B)
    (hyBound : ∀ r,
      IsMaynardDivisorTuple H R (primorial D) r → r m = 1 →
      |maynardS2RestrictedYFromCoefficients H
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m r| ≤ B) :
    |incompatibleDivisorPairRestrictedS2CommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R (primorial D))
        (maynardCoefficientFromY H R (primorial D) y) m| ≤
      B ^ 2 * roughS2CrossTupleReciprocalGSquareTail H D R *
        restrictedS2CommonReciprocalGMass H (primorial D) R m := by
  rw [incompatibleRestrictedS2_eq_neg_starredRoughFactoredSum m
    (Nat.zero_lt_of_lt hR), abs_neg]
  exact abs_nontrivialRestrictedS2StarredRoughFactoredSum_le
    hR hD hB hyBound

end BoundedGaps.Maynard
