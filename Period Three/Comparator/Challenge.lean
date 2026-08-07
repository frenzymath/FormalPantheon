module

public import PeriodThree.Statement

/-!
# Comparator challenge

This answer-free module exposes the two public propositions from
`PeriodThree.Statement`. The proof terms are intentionally left open for a
candidate solution; the upstream comparator checks that the solution has the
same theorem statements and an allowed axiom closure.
-/

public section

theorem liYorkeTheorem : PeriodThree.LiYorkeTheorem := by
  sorry

theorem periodThreeImpliesChaos : PeriodThree.PeriodThreeImpliesChaos := by
  sorry

end
