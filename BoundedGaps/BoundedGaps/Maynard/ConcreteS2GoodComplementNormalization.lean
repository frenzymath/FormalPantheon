import BoundedGaps.Maynard.ConcreteS2GoodComplementOuterMoment

noncomputable section

namespace BoundedGaps.Maynard

/-!
# Neutral normalization for the complementary S2 moment

This definition is the exact exponent-104 outer-face normalization used by
the complementary coordinate-one path. It is separated from the legacy
endpoint-comparison module so downstream scale bridges can depend only on the
raw full-face moment. See Maynard2013v3, Section 6, equations (6.10)--(6.16).
-/
noncomputable def normalizedEngelsmaS2CoordinateFiberGoodComplementOuterMoment
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  engelsmaS2CoordinateFiberGoodComplementOuterMoment
      (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m /
    ((preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N)) ^
        ((Finset.univ : Finset BoundedGaps.engelsmaTuple).erase m).card *
      Real.log (engelsmaMaynardRadius alpha N) ^ 2)

end BoundedGaps.Maynard
