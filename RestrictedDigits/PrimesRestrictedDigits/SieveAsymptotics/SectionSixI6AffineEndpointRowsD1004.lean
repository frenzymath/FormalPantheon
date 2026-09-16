import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6SevenTailRationalEndpointsD997

/-!
# Active rational affine rows for every I6 fiber

The duplicate branch-2 lower floor is inactive; the original zero/one sentinels are not
additional endpoint selectors. Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p.144, Eq. (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits

def i6D1004LowerActive (label : i6D691Label) : Fin 7 -> Bool :=
  ![true, decide (label.2.1 ≠ 2), label.2.2 0, label.2.2 1,
    label.2.2 2, label.2.2 3, label.2.2 4]

def i6D1004UpperActive (label : i6D691Label) : Fin 7 -> Bool :=
  ![true, true, !(label.2.2 0), !(label.2.2 1),
    !(label.2.2 2), !(label.2.2 3), !(label.2.2 4)]

def i6D1004LowerAffine (b : Fin 3) : Fin 7 -> RationalAffine 3 := ![
  ⟨16249 / 250000, ![0, 0, 0]⟩,
  ![⟨1 / 3, ![-1 / 3, -1 / 3, -1 / 3]⟩,
    i6D997TailBranchUpperAffine, ⟨16249 / 250000, ![0, 0, 0]⟩] b,
  i6D997TailBandUpperAffine 0, i6D997TailBandUpperAffine 1,
  i6D997TailBandUpperAffine 2, i6D997TailBandUpperAffine 3,
  i6D997TailBandUpperAffine 4]

def i6D1004UpperAffine (b : Fin 3) : Fin 7 -> RationalAffine 3 := ![
  ⟨0, ![0, 0, 1]⟩,
  ![⟨1 / 2, ![-1 / 2, -1 / 2, -1 / 2]⟩,
    ⟨1 / 3, ![-1 / 3, -1 / 3, -1 / 3]⟩, i6D997TailBranchUpperAffine] b,
  i6D997TailBandLowerAffine 0, i6D997TailBandLowerAffine 1,
  i6D997TailBandLowerAffine 2, i6D997TailBandLowerAffine 3,
  i6D997TailBandLowerAffine 4]

theorem i6D1004LowerAffine_eval (b : Fin 3) (z : (Real × Real) × Real) :
    (fun i => (i6D1004LowerAffine b i).evalReal
      (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 z)) =
    ![sectionSixThetaGap (1 / 1000000),
      sectionSixFirstLowBelowI6BranchLower z.1.1 z.1.2 z.2 b,
      sectionSixFirstLowBelowI6BandUpper z.1.1 z.1.2 z.2 0,
      sectionSixFirstLowBelowI6BandUpper z.1.1 z.1.2 z.2 1,
      sectionSixFirstLowBelowI6BandUpper z.1.1 z.1.2 z.2 2,
      sectionSixFirstLowBelowI6BandUpper z.1.1 z.1.2 z.2 3,
      sectionSixFirstLowBelowI6BandUpper z.1.1 z.1.2 z.2 4] := by
  funext i
  fin_cases i
  · norm_num [i6D1004LowerAffine, RationalAffine.evalReal, Fin.sum_univ_succ,
      sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  · fin_cases b <;>
      norm_num [i6D1004LowerAffine, RationalAffine.evalReal, Fin.sum_univ_succ,
        i6D997TailBranchUpperAffine, sectionSixFirstLowBelowI6BranchLower,
        sectionSixFirstLowCentralSmallI5P0RationalCoordinates3,
        sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo] <;> ring
  · exact (i6D997TailBandAffines_eval 0 z).2
  · exact (i6D997TailBandAffines_eval 1 z).2
  · exact (i6D997TailBandAffines_eval 2 z).2
  · exact (i6D997TailBandAffines_eval 3 z).2
  · exact (i6D997TailBandAffines_eval 4 z).2

theorem i6D1004UpperAffine_eval (b : Fin 3) (z : (Real × Real) × Real) :
    (fun i => (i6D1004UpperAffine b i).evalReal
      (sectionSixFirstLowCentralSmallI5P0RationalCoordinates3 z)) =
    ![z.2, sectionSixFirstLowBelowI6BranchUpper z.1.1 z.1.2 z.2 b,
      sectionSixFirstLowBelowI6BandLower z.1.1 z.1.2 z.2 0,
      sectionSixFirstLowBelowI6BandLower z.1.1 z.1.2 z.2 1,
      sectionSixFirstLowBelowI6BandLower z.1.1 z.1.2 z.2 2,
      sectionSixFirstLowBelowI6BandLower z.1.1 z.1.2 z.2 3,
      sectionSixFirstLowBelowI6BandLower z.1.1 z.1.2 z.2 4] := by
  funext i
  fin_cases i
  · norm_num [i6D1004UpperAffine, RationalAffine.evalReal, Fin.sum_univ_succ,
      sectionSixFirstLowCentralSmallI5P0RationalCoordinates3]
  · fin_cases b <;>
      norm_num [i6D1004UpperAffine, RationalAffine.evalReal, Fin.sum_univ_succ,
        i6D997TailBranchUpperAffine, sectionSixFirstLowBelowI6BranchUpper,
        sectionSixFirstLowCentralSmallI5P0RationalCoordinates3] <;> ring
  · exact (i6D997TailBandAffines_eval 0 z).1
  · exact (i6D997TailBandAffines_eval 1 z).1
  · exact (i6D997TailBandAffines_eval 2 z).1
  · exact (i6D997TailBandAffines_eval 3 z).1
  · exact (i6D997TailBandAffines_eval 4 z).1

end PrimesRestrictedDigits
