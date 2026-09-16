module

public import PeriodThree.Statement

import PeriodThree.Assembly
import PeriodThree.Configuration

/-!
# Li-Yorke Theorem I and period-three corollary [LY75]

This file exposes only the two closed proofs of the public propositions from
[LY75, Theorem I and its corollary, p. 987]. The orientation assembly remains
in the privately imported proof-support layer.
-/

public section

open Set

namespace PeriodThree

/-- Formal proof of the complete proposition `LiYorkeTheorem`, corresponding to
[LY75, Theorem I, p. 987]. -/
theorem liYorkeTheorem : LiYorkeTheorem := by
  intro J F a hJ hF hFJ haJ horder
  exact theoremIConclusionOfOrbitOrder hJ hF hFJ haJ horder

/-- Formal proof of the advertised period-three-implies-chaos corollary
[LY75, remark following Theorem I, p. 987]. -/
theorem periodThreeImpliesChaos : PeriodThreeImpliesChaos :=
  periodThreeImpliesChaosOfLiYorkeTheorem liYorkeTheorem

end PeriodThree
