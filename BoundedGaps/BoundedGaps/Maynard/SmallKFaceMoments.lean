import BoundedGaps.Maynard.VariationalNumeratorBridge
import BoundedGaps.Maynard.FaceMonomialMoments

/-!
# Exact small-k face moments

The generic inner face formula is composed with the 42-term certificate. The
support reduction, 104-dimensional moment, and finite ordered pair sum close
the numerator moment hypothesis left by `VariationalNumeratorBridge`.
-/

namespace BoundedGaps.Maynard

open MeasureTheory Set
open scoped BigOperators

noncomputable section

def smallKFaceInnerCoefficient (i : Fin 42) (cp : ℕ) : ℚ :=
  (Nat.choose (smallKExponentC i) cp : ℚ) *
      Nat.factorial (smallKExponentB i) *
      Nat.factorial (2 * smallKExponentC i - 2 * cp) /
    Nat.factorial (smallKExponentB i + 2 * smallKExponentC i - 2 * cp + 1)

def smallKFaceInnerExponent (i : Fin 42) (cp : ℕ) : ℕ :=
  smallKExponentB i + 2 * smallKExponentC i - 2 * cp + 1

theorem supportedTerm_eq_faceSupportedMonomial (m : Fin 105) (i : Fin 42)
    (t : maynardFaceIndex 105 m → ℝ) (x : ℝ) :
    smallKRealSupportedTerm m i t x =
      smallKRealCoefficient i * faceSupportedMonomial m
        (smallKExponentB i) (smallKExponentC i) t x := by
  classical
  by_cases hs : maynardInsertCoordinate m x t ∈ maynardSimplex 105
  · simp [smallKRealSupportedTerm, faceSupportedMonomial, hs,
      smallKRealTerm, smallKRealMonomial, smallKRealP1, smallKRealP2]
  · simp [smallKRealSupportedTerm, faceSupportedMonomial, hs]

theorem smallKRealFaceInnerTerm_formula (m : Fin 105) (i : Fin 42)
    (t : maynardFaceIndex 105 m → ℝ) (ht : t ∈ maynardFaceSimplex m) :
    smallKRealFaceInnerTerm m i t =
      ∑ cp ∈ Finset.range (smallKExponentC i + 1),
        ((smallKCoefficient i * smallKFaceInnerCoefficient i cp : ℚ) : ℝ) *
          (1 - ∑ j, t j) ^ smallKFaceInnerExponent i cp *
          (∑ j, (t j) ^ 2) ^ cp := by
  unfold smallKRealFaceInnerTerm
  rw [show (fun x => smallKRealSupportedTerm m i t x) =
      (fun x => smallKRealCoefficient i * faceSupportedMonomial m
        (smallKExponentB i) (smallKExponentC i) t x) by
    funext x
    exact supportedTerm_eq_faceSupportedMonomial m i t x]
  rw [integral_const_mul]
  rw [faceSupportedMonomial_inner_formula m _ _ t ht]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro cp hcp
  simp only [smallKFaceInnerCoefficient, smallKFaceInnerExponent]
  simp only [smallKRealCoefficient]
  push_cast
  ring_nf

theorem smallKRealFacePairTerm_formula (m : Fin 105) (i j : Fin 42)
    (t : maynardFaceIndex 105 m → ℝ) (ht : t ∈ maynardFaceSimplex m) :
    smallKRealFacePairTerm m i j t =
      ∑ cp ∈ Finset.range (smallKExponentC i + 1),
        ∑ dp ∈ Finset.range (smallKExponentC j + 1),
          ((smallKCoefficient i * smallKCoefficient j *
            smallKFaceInnerCoefficient i cp *
            smallKFaceInnerCoefficient j dp : ℚ) : ℝ) *
            faceQuadraticIntegrand m
              (smallKFaceInnerExponent i cp + smallKFaceInnerExponent j dp)
              (cp + dp) t := by
  unfold smallKRealFacePairTerm
  rw [smallKRealFaceInnerTerm_formula m i t ht,
    smallKRealFaceInnerTerm_formula m j t ht]
  simp only [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro cp hcp
  apply Finset.sum_congr rfl
  intro dp hdp
  unfold faceQuadraticIntegrand
  rw [pow_add, pow_add]
  push_cast
  ring

theorem smallKFacePairTerm_eq_inner (i j : Fin 42) (cp dp : ℕ)
    (hcp : cp ≤ smallKExponentC i) (hdp : dp ≤ smallKExponentC j) :
    smallKFacePairTerm i j cp dp =
      smallKFaceInnerCoefficient i cp * smallKFaceInnerCoefficient j dp *
        ((Nat.factorial
            (smallKFaceInnerExponent i cp + smallKFaceInnerExponent j dp) : ℚ) /
          Nat.factorial
            (104 + smallKFaceInnerExponent i cp +
              smallKFaceInnerExponent j dp + 2 * (cp + dp)) *
          smallKG104 (cp + dp)) := by
  have hnum :
      smallKFaceInnerExponent i cp + smallKFaceInnerExponent j dp =
        smallKExponentB i + 2 * smallKExponentC i - 2 * cp + 1 +
          smallKExponentB j + 2 * smallKExponentC j - 2 * dp + 1 := by
    unfold smallKFaceInnerExponent
    omega
  have hden :
      104 + smallKFaceInnerExponent i cp + smallKFaceInnerExponent j dp +
          2 * (cp + dp) =
        104 + smallKExponentB i + 2 * smallKExponentC i - 2 * cp + 1 +
          smallKExponentB j + 2 * smallKExponentC j - 2 * dp + 1 +
          2 * (cp + dp) := by
    unfold smallKFaceInnerExponent
    omega
  rw [hnum, hden]
  unfold smallKFacePairTerm smallKFaceInnerCoefficient
  ring

theorem smallKRealSupportedTerm_eq_zero_of_not_face
    (m : Fin 105) (i : Fin 42)
    (t : maynardFaceIndex 105 m → ℝ) (ht : t ∉ maynardFaceSimplex m)
    (x : ℝ) : smallKRealSupportedTerm m i t x = 0 := by
  have hs : maynardInsertCoordinate m x t ∉ maynardSimplex 105 := by
    intro hs
    exact ht (face_mem_of_insert_mem_simplex m x t hs)
  simp [smallKRealSupportedTerm, hs]

theorem smallKRealFacePairTerm_eq_zero_of_not_face
    (m : Fin 105) (i j : Fin 42)
    (t : maynardFaceIndex 105 m → ℝ) (ht : t ∉ maynardFaceSimplex m) :
    smallKRealFacePairTerm m i j t = 0 := by
  have hi : smallKRealFaceInnerTerm m i t = 0 := by
    unfold smallKRealFaceInnerTerm
    simp_rw [smallKRealSupportedTerm_eq_zero_of_not_face m i t ht]
    simp
  have hj : smallKRealFaceInnerTerm m j t = 0 := by
    unfold smallKRealFaceInnerTerm
    simp_rw [smallKRealSupportedTerm_eq_zero_of_not_face m j t ht]
    simp
  simp [smallKRealFacePairTerm, hi, hj]

theorem smallKRealFacePairTerm_cube_eq_faceSimplex
    (m : Fin 105) (i j : Fin 42) :
    (∫ t in maynardCubeOf (maynardFaceIndex 105 m),
      smallKRealFacePairTerm m i j t) =
      ∫ t in maynardFaceSimplex m, smallKRealFacePairTerm m i j t := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc))
    (faceSimplex_subset_cube m)
  intro t ht
  exact smallKRealFacePairTerm_eq_zero_of_not_face m i j t ht.2

theorem smallKRealFacePairTerm_moment (m : Fin 105) (i j : Fin 42) :
    (∫ t in maynardCubeOf (maynardFaceIndex 105 m),
      smallKRealFacePairTerm m i j t) =
      ((smallKCoefficient i * smallKCoefficient j *
        smallKSourceFaceMoment i j : ℚ) : ℝ) := by
  rw [smallKRealFacePairTerm_cube_eq_faceSimplex]
  calc
    (∫ t in maynardFaceSimplex m, smallKRealFacePairTerm m i j t) =
        ∫ t in maynardFaceSimplex m,
          ∑ cp ∈ Finset.range (smallKExponentC i + 1),
            ∑ dp ∈ Finset.range (smallKExponentC j + 1),
              ((smallKCoefficient i * smallKCoefficient j *
                smallKFaceInnerCoefficient i cp *
                smallKFaceInnerCoefficient j dp : ℚ) : ℝ) *
                faceQuadraticIntegrand m
                  (smallKFaceInnerExponent i cp + smallKFaceInnerExponent j dp)
                  (cp + dp) t := by
      apply setIntegral_congr_fun (maynardFaceSimplex_measurable m)
      intro t ht
      exact smallKRealFacePairTerm_formula m i j t ht
    _ = ∑ cp ∈ Finset.range (smallKExponentC i + 1),
          ∑ dp ∈ Finset.range (smallKExponentC j + 1),
            ((smallKCoefficient i * smallKCoefficient j *
              smallKFacePairTerm i j cp dp : ℚ) : ℝ) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro cp hcp
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro dp hdp
          rw [integral_const_mul]
          have hci := smallK_exponent_bound i
          have hcj := smallK_exponent_bound j
          have hcpC : cp ≤ smallKExponentC i := by
            have := Finset.mem_range.mp hcp
            omega
          have hdpC : dp ≤ smallKExponentC j := by
            have := Finset.mem_range.mp hdp
            omega
          have hc : cp + dp < 11 := by omega
          rw [faceQuadratic_moment_104_smallKG m
            (smallKFaceInnerExponent i cp + smallKFaceInnerExponent j dp)
            ⟨cp + dp, hc⟩]
          rw [smallKFacePairTerm_eq_inner i j cp dp hcpC hdpC]
          push_cast
          ring_nf
        · intro dp hdp
          exact (faceQuadratic_integrableOn m
            (smallKFaceInnerExponent i cp + smallKFaceInnerExponent j dp)
            (cp + dp)).const_mul _
      · intro cp hcp
        exact integrable_finsetSum _ (fun dp hdp =>
          (faceQuadratic_integrableOn m
            (smallKFaceInnerExponent i cp + smallKFaceInnerExponent j dp)
            (cp + dp)).const_mul _)
    _ = ((smallKCoefficient i * smallKCoefficient j *
          smallKSourceFaceMoment i j : ℚ) : ℝ) := by
      unfold smallKSourceFaceMoment
      push_cast
      simp_rw [Finset.mul_sum]

theorem smallKRealFacePairTerm_moment_sum (i j : Fin 42) :
    (∑ m : Fin 105,
      ∫ t in maynardCubeOf (maynardFaceIndex 105 m),
        smallKRealFacePairTerm m i j t) =
      ((105 * smallKCoefficient i * smallKCoefficient j *
        smallKSourceFaceMoment i j : ℚ) : ℝ) := by
  simp_rw [smallKRealFacePairTerm_moment]
  push_cast
  simp
  ring_nf

theorem maynardM_gt_four_of_bddAbove
    (hbound : BddAbove (maynardRatioSet 105)) :
    (4 : ℝ) < maynardM 105 := by
  exact maynardM_gt_four_of_face_moment_hypothesis hbound
    (fun i j => smallKRealFacePairTerm_moment_sum i j)

end
end BoundedGaps.Maynard
