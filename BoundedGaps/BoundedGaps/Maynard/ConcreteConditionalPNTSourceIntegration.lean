import BoundedGaps.Maynard.ConcreteConditionalPNTIntegration
import BoundedGaps.Maynard.ConcretePrimeCountPNTSequenceBridge

/-!
# Conditional real-PNT source integration

This is a source-facing corollary of SEM-407. SEM-408 supplies the conversion
from the real-variable prime-counting asymptotic; both that input and
Bombieri--Vinogradov remain explicit hypotheses. See SEM-409.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Filter
open scoped Asymptotics

/-- A real-variable prime-counting PNT and Bombieri--Vinogradov imply the
conditional frozen bounded-gaps statement. -/
theorem boundedGapsStatement_of_bombieriVinogradov_and_realPrimeCountingPNT
    (hBV : bombieriVinogradov)
    (hpi : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
      (fun x => x / Real.log x)) :
    BoundedGaps.boundedGapsStatement := by
  apply boundedGapsStatement_of_bombieriVinogradov_and_pnt hBV
  exact tendsto_primeCountTotal_mul_log_div_of_isEquivalent hpi

end BoundedGaps.Maynard
