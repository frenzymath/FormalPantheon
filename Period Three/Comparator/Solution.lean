module

public import PeriodThree.Main

/-!
# Comparator solution

These declarations have exactly the statements exposed by `Challenge.lean`
and use the closed proofs from `PeriodThree.Main`.
-/

public section

theorem liYorkeTheorem : PeriodThree.LiYorkeTheorem :=
  PeriodThree.liYorkeTheorem

theorem periodThreeImpliesChaos : PeriodThree.PeriodThreeImpliesChaos :=
  PeriodThree.periodThreeImpliesChaos

end
