import BoundedGaps.Maynard.EngelsmaCandidate
import BoundedGaps.Maynard.SmallKFaceMoments

noncomputable section

namespace BoundedGaps.Maynard

open MeasureTheory
open scoped BigOperators

/-!
# Concrete S2 face functional

The finite face limit common to the concrete S2 main-term paths is identified
exactly with Maynard's `J_105` functional. See SEM-403 and Maynard2013v3,
Sections 3, 7, and 8.
-/

noncomputable def engelsmaS2GoodOuterFaceLimit
    (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ i : Fin 42, ∑ j : Fin 42,
    ∑ cp ∈ Finset.range (smallKExponentC i + 1),
      ∑ dp ∈ Finset.range (smallKExponentC j + 1),
        ((smallKCoefficient i * smallKCoefficient j *
          smallKFaceInnerCoefficient i cp *
          smallKFaceInnerCoefficient j dp : ℚ) : ℝ) *
          (∫ t in maynardFaceSimplex (engelsmaIndexEquiv m),
            faceQuadraticIntegrand (engelsmaIndexEquiv m)
              (smallKFaceInnerExponent i cp + smallKFaceInnerExponent j dp)
              (cp + dp) t)

theorem engelsmaS2GoodOuterFaceLimit_eq_maynardJ
    (m : BoundedGaps.engelsmaTuple) :
    engelsmaS2GoodOuterFaceLimit m =
      maynardJ 105 (engelsmaIndexEquiv m) smallKCandidate := by
  unfold engelsmaS2GoodOuterFaceLimit
  rw [maynardJ_eq_face_pair_integral_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [smallKRealFacePairTerm_cube_eq_faceSimplex]
  symm
  calc
    (∫ t in maynardFaceSimplex (engelsmaIndexEquiv m),
        smallKRealFacePairTerm (engelsmaIndexEquiv m) i j t) =
      ∫ t in maynardFaceSimplex (engelsmaIndexEquiv m),
        ∑ cp ∈ Finset.range (smallKExponentC i + 1),
          ∑ dp ∈ Finset.range (smallKExponentC j + 1),
            ((smallKCoefficient i * smallKCoefficient j *
              smallKFaceInnerCoefficient i cp *
              smallKFaceInnerCoefficient j dp : ℚ) : ℝ) *
              faceQuadraticIntegrand (engelsmaIndexEquiv m)
                (smallKFaceInnerExponent i cp +
                  smallKFaceInnerExponent j dp) (cp + dp) t := by
      apply setIntegral_congr_fun
        (maynardFaceSimplex_measurable (engelsmaIndexEquiv m))
      intro t ht
      exact smallKRealFacePairTerm_formula
        (engelsmaIndexEquiv m) i j t ht
    _ = ∑ cp ∈ Finset.range (smallKExponentC i + 1),
          ∑ dp ∈ Finset.range (smallKExponentC j + 1),
            ((smallKCoefficient i * smallKCoefficient j *
              smallKFaceInnerCoefficient i cp *
              smallKFaceInnerCoefficient j dp : ℚ) : ℝ) *
              (∫ t in maynardFaceSimplex (engelsmaIndexEquiv m),
                faceQuadraticIntegrand (engelsmaIndexEquiv m)
                  (smallKFaceInnerExponent i cp +
                    smallKFaceInnerExponent j dp) (cp + dp) t) := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro cp hcp
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro dp hdp
          rw [integral_const_mul]
        · intro dp hdp
          exact (faceQuadratic_integrableOn (engelsmaIndexEquiv m)
            (smallKFaceInnerExponent i cp + smallKFaceInnerExponent j dp)
            (cp + dp)).const_mul _
      · intro cp hcp
        exact integrable_finsetSum _ (fun dp hdp =>
          (faceQuadratic_integrableOn (engelsmaIndexEquiv m)
            (smallKFaceInnerExponent i cp + smallKFaceInnerExponent j dp)
            (cp + dp)).const_mul _)

theorem sum_engelsmaS2GoodOuterFaceLimit_eq_maynardNumerator :
    (∑ m ∈ BoundedGaps.engelsmaTuple.attach,
      engelsmaS2GoodOuterFaceLimit m) =
      ∑ m : Fin 105, maynardJ 105 m smallKCandidate := by
  rw [Finset.attach_eq_univ]
  calc
    (∑ m : BoundedGaps.engelsmaTuple,
      engelsmaS2GoodOuterFaceLimit m) =
        ∑ m : BoundedGaps.engelsmaTuple,
          maynardJ 105 (engelsmaIndexEquiv m) smallKCandidate := by
      apply Finset.sum_congr rfl
      intro m hm
      exact engelsmaS2GoodOuterFaceLimit_eq_maynardJ m
    _ = ∑ m : Fin 105, maynardJ 105 m smallKCandidate :=
      engelsmaIndexEquiv.sum_comp
        (fun m => maynardJ 105 m smallKCandidate)

end BoundedGaps.Maynard
