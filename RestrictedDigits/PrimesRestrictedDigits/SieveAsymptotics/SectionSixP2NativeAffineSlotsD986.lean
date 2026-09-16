import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2RefinedProfileFlatteningD984
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2NativeAffineDataD983
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ConstantIntegralCapD981
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2InverseIntegralCapD982

/-!
# Native affine slots of the original P2 profile

Exact rational data reproduce the 2+8+8 profile flattening. Source: `MAYNARD-PRD-PUBLISHED`,
Section 6, Eq. (6.12). No numerical budget is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace PrimesRestrictedDigits

def sectionSixP2MiddleLowerD986 (i : Fin 8) : RationalAffine 3 :=
  sectionSixP2BudgetMultipleD983 (8 / (25 + ((i : Nat) : Rat)))

def sectionSixP2MiddleUpperD986 (i : Fin 8) : RationalAffine 3 :=
  sectionSixP2BudgetMultipleD983 (8 / (24 + ((i : Nat) : Rat)))

def sectionSixP2InverseLowerD986 (i : Fin 8) : RationalAffine 3 :=
  sectionSixP2BudgetMultipleD983 (8 / (17 + ((i : Nat) : Rat)))

def sectionSixP2InverseUpperD986 (i : Fin 8) : RationalAffine 3 :=
  sectionSixP2BudgetMultipleD983 (8 / (16 + ((i : Nat) : Rat)))

def sectionSixP2InverseArgumentLowerD986 (i : Fin 8) : Rat :=
  1 + ((i : Nat) : Rat) / 8

def sectionSixP2InverseArgumentUpperD986 (i : Fin 8) : Rat :=
  1 + (((i : Nat) : Rat) + 1) / 8

def sectionSixP2MiddleCapRatD986 (i : Fin 8) : Rat :=
  ![1315039 / 2500000, 2718097 / 5000000, 1110277 / 2000000,
    5621861 / 10000000, 2829539 / 5000000, 5671331 / 10000000,
    70893 / 125000, 2832363 / 5000000] i

theorem sectionSixP2MiddleLowerD986_eval (i : Fin 8) (x : Fin 3 -> Real) :
    (sectionSixP2MiddleLowerD986 i).evalReal x =
      8 * sectionSixP2AffineBD983.evalReal x / (25 + (i : Nat)) := by
  norm_num [sectionSixP2MiddleLowerD986, sectionSixP2BudgetMultipleD983_eval]
  ring

theorem sectionSixP2MiddleUpperD986_eval (i : Fin 8) (x : Fin 3 -> Real) :
    (sectionSixP2MiddleUpperD986 i).evalReal x =
      8 * sectionSixP2AffineBD983.evalReal x / (24 + (i : Nat)) := by
  norm_num [sectionSixP2MiddleUpperD986, sectionSixP2BudgetMultipleD983_eval]
  ring

theorem sectionSixP2InverseLowerD986_eval (i : Fin 8) (x : Fin 3 -> Real) :
    (sectionSixP2InverseLowerD986 i).evalReal x =
      8 * sectionSixP2AffineBD983.evalReal x / (17 + (i : Nat)) := by
  norm_num [sectionSixP2InverseLowerD986, sectionSixP2BudgetMultipleD983_eval]
  ring

theorem sectionSixP2InverseUpperD986_eval (i : Fin 8) (x : Fin 3 -> Real) :
    (sectionSixP2InverseUpperD986 i).evalReal x =
      8 * sectionSixP2AffineBD983.evalReal x / (16 + (i : Nat)) := by
  norm_num [sectionSixP2InverseUpperD986, sectionSixP2BudgetMultipleD983_eval]
  ring

theorem sectionSixP2InverseArgumentLowerD986_cast (i : Fin 8) :
    (sectionSixP2InverseArgumentLowerD986 i : Real) =
      uniformRealGridLower (1 : Real) 2 i := by
  norm_num [sectionSixP2InverseArgumentLowerD986, uniformRealGridLower]

theorem sectionSixP2InverseArgumentUpperD986_cast (i : Fin 8) :
    (sectionSixP2InverseArgumentUpperD986 i : Real) =
      uniformRealGridUpper (1 : Real) 2 i := by
  norm_num [sectionSixP2InverseArgumentUpperD986, uniformRealGridUpper]

theorem sectionSixP2MiddleCapRatD986_cast (i : Fin 8) :
    (sectionSixP2MiddleCapRatD986 i : Real) = sectionSixBuchstabMiddleEightCellCap i := by
  fin_cases i <;> norm_num [sectionSixP2MiddleCapRatD986, sectionSixBuchstabMiddleEightCellCap]

private theorem clamp_self_D986 (d W : Real) : max d (min W d) = d :=
  max_eq_left (min_le_right _ _)

theorem sectionSixP2RefinedProfile_eq_affineSlots_D986 (x : Fin 3 -> Real)
    (hB : 0 ≤ sectionSixP2AffineBD983.evalReal x) :
    let u := sectionSixP2AffineUD983
    let v := sectionSixP2AffineVD983
    let d := sectionSixP2AffineDD983
    let W := sectionSixP2AffineWD983
    let B := sectionSixP2AffineBD983
    sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound ((x 0, x 1), x 2) =
      sectionSixP2ClampedConstantAffinePayloadD981 u v d W d
        (sectionSixP2BudgetMultipleD983 (4 / 17)) (281 / 500) x +
      sectionSixP2ClampedConstantAffinePayloadD981 u v d W
        (sectionSixP2BudgetMultipleD983 (4 / 17))
        (sectionSixP2BudgetMultipleD983 (1 / 4)) (564383 / 1000000) x +
      (∑ i : Fin 8, sectionSixP2ClampedConstantAffinePayloadD981 u v d W
        (sectionSixP2MiddleLowerD986 i) (sectionSixP2MiddleUpperD986 i)
        (sectionSixP2MiddleCapRatD986 i : Real) x) +
      ∑ i : Fin 8, sectionSixP2ClampedInverseAffinePayloadD982 u v d W
        (sectionSixP2InverseLowerD986 i) (sectionSixP2InverseUpperD986 i) B
        (sectionSixP2InverseArgumentLowerD986 i : Real)
        (sectionSixP2InverseArgumentUpperD986 i : Real) x := by
  dsimp only
  have hleft :
      sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound ((x 0, x 1), x 2) =
        sectionSixBuchstabRefinedFiberBound (sectionSixP2AffineUD983.evalReal x)
          (sectionSixP2AffineVD983.evalReal x) (sectionSixP2AffineWD983.evalReal x)
          (sectionSixP2AffineBD983.evalReal x) (sectionSixP2AffineDD983.evalReal x)
          (min (sectionSixP2AffineWD983.evalReal x) (sectionSixP2AffineBD983.evalReal x / 2)) := by
    simp only [sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound]
    rw [sectionSixFirstLowCentralSmallI5P2_shiftedUpper_eq_D976 ((x 0, x 1), x 2)]
    norm_num [sectionSixP2AffineUD983_eval, sectionSixP2AffineVD983_eval,
      sectionSixP2AffineWD983_eval, sectionSixP2AffineBD983_eval,
      sectionSixP2AffineDD983_eval, sectionSixThetaTwo]
  rw [hleft]
  have h := sectionSixBuchstabRefinedFiberBound_eq_flat_D984
    (sectionSixP2AffineUD983.evalReal x) (sectionSixP2AffineVD983.evalReal x)
    (sectionSixP2AffineDD983.evalReal x) (sectionSixP2AffineWD983.evalReal x)
    (sectionSixP2AffineBD983.evalReal x) hB
  simpa only [sectionSixP2ClampedConstantAffinePayloadD981,
    sectionSixP2ClampedInverseAffinePayloadD982, sectionSixP2MiddleLowerD986_eval,
    sectionSixP2MiddleUpperD986_eval, sectionSixP2InverseLowerD986_eval,
    sectionSixP2InverseUpperD986_eval, sectionSixP2InverseArgumentLowerD986_cast,
    sectionSixP2InverseArgumentUpperD986_cast, sectionSixP2MiddleCapRatD986_cast,
    sectionSixP2BudgetMultipleD983_eval, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
    div_mul_eq_mul_div, one_mul, sectionSixBuchstabClamp, clamp_self_D986] using h

end PrimesRestrictedDigits
