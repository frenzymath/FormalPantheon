import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import PrimesRestrictedDigits.BasicEstimates.FiniteRationalGeometry

/-!
# Native rational affine fields for P2

These forms retain the (d,r,s) coordinates of the cover. Source: `MAYNARD-PRD-PUBLISHED`,
Section 6, Eq. (6.12).
-/

set_option autoImplicit false
set_option warningAsError true

open Set
open scoped BigOperators

namespace PrimesRestrictedDigits

def sectionSixP2AffineDD983 : RationalAffine 3 := ⟨0, ![1, 0, 0]⟩
def sectionSixP2AffineUD983 : RationalAffine 3 := ⟨212499 / 500000, ![-1, 0, 0]⟩
def sectionSixP2AffineVD983 : RationalAffine 3 := ⟨0, ![1, 1, 0]⟩
def sectionSixP2AffineWD983 : RationalAffine 3 := ⟨0, ![1, 0, 1]⟩
def sectionSixP2AffineBD983 : RationalAffine 3 := ⟨287501 / 500000, fun _ => -1⟩

def sectionSixP2BudgetMultipleD983 (q : Rat) : RationalAffine 3 :=
  ⟨q * (287501 / 500000), fun _ => -q⟩

theorem sectionSixP2AffineDD983_eval (x : Fin 3 -> Real) :
    sectionSixP2AffineDD983.evalReal x = x 0 := by
  norm_num [sectionSixP2AffineDD983, RationalAffine.evalReal, Fin.sum_univ_succ]

theorem sectionSixP2AffineUD983_eval (x : Fin 3 -> Real) :
    sectionSixP2AffineUD983.evalReal x = 212499 / 500000 - x 0 := by
  norm_num [sectionSixP2AffineUD983, RationalAffine.evalReal, Fin.sum_univ_succ]
  ring

theorem sectionSixP2AffineVD983_eval (x : Fin 3 -> Real) :
    sectionSixP2AffineVD983.evalReal x = x 0 + x 1 := by
  norm_num [sectionSixP2AffineVD983, RationalAffine.evalReal, Fin.sum_univ_succ]

theorem sectionSixP2AffineWD983_eval (x : Fin 3 -> Real) :
    sectionSixP2AffineWD983.evalReal x = x 0 + x 2 := by
  norm_num [sectionSixP2AffineWD983, RationalAffine.evalReal, Fin.sum_univ_succ]

theorem sectionSixP2AffineBD983_eval (x : Fin 3 -> Real) :
    sectionSixP2AffineBD983.evalReal x = 1 - 212499 / 500000 - x 0 - x 1 - x 2 := by
  norm_num [sectionSixP2AffineBD983, RationalAffine.evalReal, Fin.sum_univ_succ]
  ring

theorem sectionSixP2BudgetMultipleD983_eval (q : Rat) (x : Fin 3 -> Real) :
    (sectionSixP2BudgetMultipleD983 q).evalReal x =
      (q : Real) * sectionSixP2AffineBD983.evalReal x := by
  norm_num [sectionSixP2BudgetMultipleD983, sectionSixP2AffineBD983,
    RationalAffine.evalReal, Fin.sum_univ_succ]
  ring

theorem sectionSixP2ClosedOuter_affine_bounds_D983
    {x : Fin 3 -> Real} (hx : x ∈ sectionSixP2ClosedOuterD974) :
    0 < sectionSixP2AffineUD983.evalReal x ∧
    0 < sectionSixP2AffineVD983.evalReal x ∧
    0 < sectionSixP2AffineDD983.evalReal x ∧
    0 < sectionSixP2AffineWD983.evalReal x ∧
    0 < sectionSixP2AffineBD983.evalReal x ∧
    sectionSixP2AffineDD983.evalReal x ≤ sectionSixP2AffineWD983.evalReal x ∧
    2 * sectionSixP2AffineDD983.evalReal x ≤ sectionSixP2AffineBD983.evalReal x := by
  rcases hx with ⟨hd, hs, hsr, hsum, _⟩
  rw [sectionSixP2AffineUD983_eval, sectionSixP2AffineVD983_eval,
    sectionSixP2AffineDD983_eval, sectionSixP2AffineWD983_eval,
    sectionSixP2AffineBD983_eval]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem sectionSixP2ClosedOuter_budgetMultiple_pos_D983 (q : Rat) (hq : 0 < q)
    {x : Fin 3 -> Real} (hx : x ∈ sectionSixP2ClosedOuterD974) :
    0 < (sectionSixP2BudgetMultipleD983 q).evalReal x := by
  rw [sectionSixP2BudgetMultipleD983_eval]
  exact mul_pos (by exact_mod_cast hq)
    (sectionSixP2ClosedOuter_affine_bounds_D983 hx).2.2.2.2.1

end PrimesRestrictedDigits
