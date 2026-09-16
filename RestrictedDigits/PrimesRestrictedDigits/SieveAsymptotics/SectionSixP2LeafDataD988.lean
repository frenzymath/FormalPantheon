import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2RationalSlotWeightsD985
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2NativeAffineSlotsD986

/-!
# Exact finite payloads for native P2 leaves

Codes select one of the already-proved caps for each original slot. The density excludes
physical volume; validation recomputes it in Rat. Source context: `MAYNARD-PRD-PUBLISHED`,
Section 6, Eq. (6.12).
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace PrimesRestrictedDigits

structure SectionSixP2LeafPayloadD988 where
  baseline : Fin 16
  legacy : Fin 16
  middle : Fin 8 -> Fin 16
  inverse : Fin 8 -> Fin 32
  upper : Rat

def sectionSixP2ConstantChoiceWeightD988 (T : RationalTetrahedron)
    (rhoL rhoH : RationalAffine 3) (C : Rat) (code : Fin 16) : Rat :=
  sectionSixP2ConstantWeightRatD985 T sectionSixP2AffineUD983 sectionSixP2AffineVD983
    sectionSixP2AffineDD983 sectionSixP2AffineWD983 rhoL rhoH C
    (Fin.ofNat 4 code.val) (code.val / 4 % 2 == 1) (code.val / 8 % 2 == 1)

def sectionSixP2InverseChoiceWeightD988 (T : RationalTetrahedron)
    (i : Fin 8) (code : Fin 32) : Rat :=
  sectionSixP2InverseWeightRatD985 T sectionSixP2AffineUD983 sectionSixP2AffineVD983
    sectionSixP2AffineDD983 sectionSixP2AffineWD983
    (sectionSixP2InverseLowerD986 i) (sectionSixP2InverseUpperD986 i) sectionSixP2AffineBD983
    (sectionSixP2InverseArgumentLowerD986 i) (sectionSixP2InverseArgumentUpperD986 i)
    (Fin.ofNat 4 code.val) (code.val / 4 % 2 == 1) (code.val / 8 % 2 == 1)
    (code.val / 16 % 2 == 1)

def sectionSixP2LeafWeightD988 (T : RationalTetrahedron)
    (p : SectionSixP2LeafPayloadD988) : Rat :=
  sectionSixP2ConstantChoiceWeightD988 T sectionSixP2AffineDD983
    (sectionSixP2BudgetMultipleD983 (4 / 17)) (281 / 500) p.baseline +
  sectionSixP2ConstantChoiceWeightD988 T (sectionSixP2BudgetMultipleD983 (4 / 17))
    (sectionSixP2BudgetMultipleD983 (1 / 4)) (564383 / 1000000) p.legacy +
  (∑ i : Fin 8, sectionSixP2ConstantChoiceWeightD988 T
    (sectionSixP2MiddleLowerD986 i) (sectionSixP2MiddleUpperD986 i)
    (sectionSixP2MiddleCapRatD986 i) (p.middle i)) +
  ∑ i : Fin 8, sectionSixP2InverseChoiceWeightD988 T i (p.inverse i)

def sectionSixP2LeafValidD988 (T : RationalTetrahedron)
    (p : SectionSixP2LeafPayloadD988) : Bool :=
  decide ((∀ i : Fin 4,
    0 < rationalAffineEval_D969 sectionSixP2AffineUD983 (T.vertex i) ∧
    0 < rationalAffineEval_D969 sectionSixP2AffineVD983 (T.vertex i) ∧
    0 < rationalAffineEval_D969 sectionSixP2AffineDD983 (T.vertex i) ∧
    0 < rationalAffineEval_D969 sectionSixP2AffineWD983 (T.vertex i) ∧
    0 < rationalAffineEval_D969 sectionSixP2AffineBD983 (T.vertex i)) ∧
    sectionSixP2LeafWeightD988 T p ≤ p.upper)

end PrimesRestrictedDigits
