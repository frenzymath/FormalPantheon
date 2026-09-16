import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0AmbientBoxOrderedOuter

/-!
# P0 fiber inclusion in the ambient cell union

This pointwise adapter transports the exact P0 fiber into the three ambient closed cells. It
is deliberately one-way: no converse, disjointness, source containment, measure, or integral
claim is made here.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowCentralSmallI5P0Fiber_mem_ambientCell_iUnion
    {u v w t : Real}
    (ht : t ∈ sectionSixFirstLowCentralSmallI5P0Fiber u v w) :
    (((u, v), w), t) ∈
      ⋃ b : Fin 3,
        sectionSixFirstLowCentralSmallI5P0AmbientCell b := by
  change (((u, v), w), t) ∈
      sectionSixFirstLowCentralSmallUniformOuterRegion
        (1 / 1000000 : Real) ∧
    (((u, v), w), t) ∈
      sectionSixFirstLowCentralSmallI5PairPattern 0 at ht
  rcases ht with ⟨houter, hpattern⟩
  have hbox : (((u, v), w) : ((Real × Real) × Real)) ∈
      sectionSixFirstLowCentralSmallI5P0AmbientBaseBox := by
    change (((u, v) : Real × Real) ∈
        Set.Icc (sectionSixThetaGap (1 / 1000000 : Real))
          (sectionSixThetaOne (1 / 1000000 : Real)) ×ˢ
      Set.Icc (sectionSixThetaGap (1 / 1000000 : Real))
        (sectionSixThetaOne (1 / 1000000 : Real))) ∧
      w ∈ Set.Icc (sectionSixThetaGap (1 / 1000000 : Real))
        (sectionSixThetaOne (1 / 1000000 : Real))
    simp only [Set.mem_prod, Set.mem_Icc]
    rcases houter with ⟨hwall, htw, hwv, hvu, hu, hsum, hcap,
      hpair1, hpair2, hpair3, hpair4, hpair5⟩
    constructor
    · constructor
      · exact ⟨(hwall.trans_le (htw.trans (hwv.trans hvu))).le, hu⟩
      · exact ⟨(hwall.trans_le (htw.trans hwv)).le,
          hvu.trans hu⟩
    · exact ⟨(hwall.trans_le htw).le,
        hwv.trans (hvu.trans hu)⟩
  have hcell := sectionSixFirstLowCentralSmallI5P0Fiber_mem_branchCell
    (u := u) (v := v) (w := w) (t := t)
    ⟨houter, hpattern⟩
  rcases hcell with ⟨b, htb⟩
  refine Set.mem_iUnion.2 ⟨b, ?_⟩
  change (((u, v), w) : ((Real × Real) × Real)) ∈
      sectionSixFirstLowCentralSmallI5P0AmbientBaseBox ∧
    t ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P0AmbientLower b ((u, v), w))
      (sectionSixFirstLowCentralSmallI5P0AmbientUpper b ((u, v), w))
  exact ⟨hbox, htb⟩

end

end PrimesRestrictedDigits
