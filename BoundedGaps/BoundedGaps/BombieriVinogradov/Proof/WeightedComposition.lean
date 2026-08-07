import BoundedGaps.BombieriVinogradov.Proof.WeightedMainTheorem
import BoundedGaps.BombieriVinogradov.Proof.StandardToNatural

/-!
# Unconditional standard-to-natural composition

The only edge that joins the closed weighted theorem to the conditional
normalization branch is this file.  Keeping that edge explicit makes the
conditional closure auditable on its own.
-/

namespace BoundedGaps.BombieriVinogradov

/-- The unconditional weighted theorem yields Maynard's natural
Bombieri--Vinogradov proposition through the reviewed conditional adapter. -/
theorem unconditional_bombieriVinogradov_via_weighted :
    BoundedGaps.Maynard.bombieriVinogradov := by
  exact bombieriVinogradov_of_weightedBombieriVinogradov
    unconditional_weightedBombieriVinogradov

end BoundedGaps.BombieriVinogradov
