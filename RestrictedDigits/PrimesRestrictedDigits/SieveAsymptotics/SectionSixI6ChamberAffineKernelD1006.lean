import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ClosedAffineChamberCoverD1005
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP0AffineKernelsD968
import PrimesRestrictedDigits.BasicEstimates.RationalAffineReciprocalCapCastsD969

/-!
# Five-denominator I6 chamber kernels

Positive-part extension controls whole leaves that may cross chamber walls. The stored
rational ceiling excludes the single physical volume factor. Source: `MAYNARD-PRD-PUBLISHED`,
Section 6, p.144, Eq. (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

def i6D1006BranchCap : Fin 3 -> Rat := ![1, 70893 / 125000, 564383 / 1000000]

def i6D1006Numerator (b : Fin 3) (l h : Fin 7) : RationalAffine 3 :=
  ⟨i6D1006BranchCap b *
      ((i6D1004UpperAffine b h).constant - (i6D1004LowerAffine b l).constant),
    fun j => i6D1006BranchCap b *
      ((i6D1004UpperAffine b h).coefficient j - (i6D1004LowerAffine b l).coefficient j)⟩

def i6D1006Denominators (b : Fin 3) (l h : Fin 7) : Fin 5 -> RationalAffine 3 :=
  ![sectionSixP0CoordinateD968 0, sectionSixP0CoordinateD968 1,
    sectionSixP0CoordinateD968 2, i6D1004LowerAffine b l, i6D1004UpperAffine b h]

def i6D1006LeafValid (b : Fin 3) (l h : Fin 7) (T : RationalTetrahedron) (q : Rat) : Bool :=
  decide ((∀ k i, 0 < rationalAffineEval_D969 (i6D1006Denominators b l h k) (T.vertex i)) ∧
    positivePartAffineReciprocalWeightRat_D969 T (i6D1006Numerator b l h)
      (i6D1006Denominators b l h) ≤ q)

theorem i6D1006Numerator_eval (b : Fin 3) (l h : Fin 7) (x : Fin 3 -> Real) :
    (i6D1006Numerator b l h).evalReal x = (i6D1006BranchCap b : Real) *
      ((i6D1004UpperAffine b h).evalReal x - (i6D1004LowerAffine b l).evalReal x) := by
  simp [i6D1006Numerator, RationalAffine.evalReal, Fin.sum_univ_succ]
  ring

theorem i6D1006Denominators_eval (b : Fin 3) (l h : Fin 7) (x : Fin 3 -> Real) :
    (fun k => (i6D1006Denominators b l h k).evalReal x) =
      ![x 0, x 1, x 2, (i6D1004LowerAffine b l).evalReal x,
        (i6D1004UpperAffine b h).evalReal x] := by
  funext k
  fin_cases k <;> simp [i6D1006Denominators, sectionSixP0CoordinateD968_eval]

theorem i6D1006Leaf_denominators_positive (b : Fin 3) (l h : Fin 7)
    (T : RationalTetrahedron) (q : Rat) (hv : i6D1006LeafValid b l h T q = true) :
    ∀ k i, 0 < (i6D1006Denominators b l h k).evalReal (T.vertexReal i) := by
  have hguard := (of_decide_eq_true hv).1
  intro k i
  have hpos := (Rat.cast_pos (K := Real)).2 (hguard k i)
  rw [rationalAffineEval_cast_D969] at hpos
  exact hpos

theorem i6D1006Leaf_integrable (b : Fin 3) (l h : Fin 7)
    (T : RationalTetrahedron) (q : Rat) (hv : i6D1006LeafValid b l h T q = true) :
    IntegrableOn (positivePartAffineReciprocalKernel_D967
      (i6D1006Numerator b l h) (i6D1006Denominators b l h)) T.region volume :=
  T.positivePartAffineReciprocal_integrableOn_D967 _ _
    (i6D1006Leaf_denominators_positive b l h T q hv)

theorem i6D1006Leaf_nonneg (b : Fin 3) (l h : Fin 7)
    (T : RationalTetrahedron) (q : Rat) (hv : i6D1006LeafValid b l h T q = true)
    {x : Fin 3 -> Real} (hx : x ∈ T.region) :
    0 ≤ positivePartAffineReciprocalKernel_D967
      (i6D1006Numerator b l h) (i6D1006Denominators b l h) x :=
  T.positivePartAffineReciprocal_nonneg_D967 _ _
    (i6D1006Leaf_denominators_positive b l h T q hv) hx

theorem i6D1006Leaf_integral_le (b : Fin 3) (l h : Fin 7)
    (T : RationalTetrahedron) (q : Rat) (hv : i6D1006LeafValid b l h T q = true) :
    (∫ x in T.region, positivePartAffineReciprocalKernel_D967
      (i6D1006Numerator b l h) (i6D1006Denominators b l h) x) ≤
      ((T.volumeRat * q : Rat) : Real) := by
  have hguard := of_decide_eq_true hv
  exact (T.positivePartAffineReciprocal_setIntegral_le_rat_D969 _ _ hguard.1).trans
    ((Rat.cast_le (K := Real)).2 (mul_le_mul_of_nonneg_left hguard.2 T.volumeRat_nonneg))

end PrimesRestrictedDigits
