import BoundedGaps.BombieriVinogradov.Proof.WeightedComposition

/-!
# Unconditional Bombieri--Vinogradov theorem

This is the proof export for the exact Mathlib-only proposition frozen in
`BombieriVinogradov/Statement.lean`. Semantic review: `SEM-577`.
-/

namespace BoundedGaps.Maynard

/-- Bombieri--Vinogradov supplies every fixed positive prime level strictly
below one half. -/
theorem unconditional_bombieriVinogradov : bombieriVinogradov := by
  exact BoundedGaps.BombieriVinogradov.unconditional_bombieriVinogradov_via_weighted

end BoundedGaps.Maynard
