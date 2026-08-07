import BoundedGaps.BombieriVinogradov.Analytic.CosecantHilbert.AnalyticEstimate

/-!
# Montgomery--Vaughan's coefficient-one cosecant Hilbert inequality

This file exposes Theorem 1, equation (1.2), from
MontgomeryVaughanHilbert1974, printed p. 73 and proved on pp. 79--80. The
kernel uses chosen real lifts; circle points occur only in the spacing
hypothesis. See SEM-447.
-/

open scoped BigOperators
open Metric

noncomputable section

namespace BoundedGaps.Maynard

/-- The exact coefficient-one cosecant Hilbert inequality for a finite
family of real frequency lifts separated modulo one. -/
theorem norm_cosecantBilinearForm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s →
      δ ≤ dist (x r : UnitAddCircle) (x s : UnitAddCircle))
    (u : ι → ℂ) :
    ‖cosecantBilinearForm x u‖ ≤ δ⁻¹ * ∑ r, ‖u r‖ ^ 2 :=
  CosecantHilbert.norm_cosecantBilinearForm_le_of_separated x hδ hsep u

end BoundedGaps.Maynard
