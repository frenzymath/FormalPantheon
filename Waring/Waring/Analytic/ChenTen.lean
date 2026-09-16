import Waring.Analytic.ChenTenMajorArcPositive

/-!
# Reconstructed Chen Lemma 10

This module packages the corrected major-arc statement used downstream.  It
uses the English `Gamma(4)` normalization and `10^25` major-arc error, the
checked `6*q` residue approximation, and the weakened singular-integral
coefficient `2999/1000` documented in decision D-015.
-/

set_option autoImplicit false

namespace Waring.Analytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The reconstructed, downstream-sufficient form of Chen's Lemma 10. -/
theorem chen_lemma_ten_reconstructed
    {P N : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P)
    (hNlower : (P : Real) ^ 5 / 2 ≤ (N : Real))
    (hNupper : N ≤ (P + 1) ^ 5) :
    ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
        chenTenSingularIntegral P N * chenTenSingularSeries N‖ ≤
        (10 : Real) ^ 25 * (P : Real) ^ (93 / 10 : Real) +
          (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) *
            ‖chenTenSingularIntegral P N‖ ∧
      (2999 / 1000 : Real) * chenTenT15 * (N : Real) ^ 2 ≤
        (chenTenSingularIntegral P N).re ∧
      (9 / 80 : Real) ≤ (chenTenSingularSeries N).re ∧
      (1 / 2000 : Real) * (P : Real) ^ 10 <
        (∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha).re := by
  have hPcast : (10 : Real) ^ 100 ≤ (P : Real) := by
    exact_mod_cast hPbig
  have hPbridge : (10 : Real) ^ 30 ≤ (P : Real) :=
    (by norm_num : (10 : Real) ^ 30 ≤ 10 ^ 100).trans hPcast
  exact ⟨
    norm_sum_chenTenMajorArcs_sub_singularIntegral_mul_series_le_source
      (P := P) (N := N) hPbridge,
    chenTen_singularIntegral_re_lower_source hPbig hNlower hNupper,
    nine_eightieths_le_chenTenSingularSeries_re N,
    one_2000_mul_P_pow_ten_lt_chenTenMajorArc_re_source
      hPbig hNlower hNupper⟩

end

end Waring.Analytic
