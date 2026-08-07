import BoundedGaps.Maynard.MaynardS2CoordinateFiberShortEndpoint
import BoundedGaps.Maynard.MaynardS2GPositivity
import BoundedGaps.Maynard.MaynardSupportBounds

noncomputable section

/-!
# Cardinality majorant for the S2 short tail

Supported `g` positivity gives a simple finite majorant for the reciprocal
short-tail mass. This is deliberately only a cardinality bound; decay of the
short region still requires a sharper argument.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

set_option maxRecDepth 4000 in
theorem engelsmaS2CoordinateFiberShortReciprocalGMass_le_support_card
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple) (hD : 2 ≤ D) :
    engelsmaS2CoordinateFiberShortReciprocalGMass R D m ≤
      (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple R
        (primorial D)).card := by
  unfold engelsmaS2CoordinateFiberShortReciprocalGMass
  let S := engelsmaS2CoordinateFiberShortSupport R D m
  let f := fun r : BoundedGaps.engelsmaTuple → ℕ =>
    1 / |∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ)|
  have hterm : ∀ r ∈ S, f r ≤ 1 := by
    intro r hrMem
    have hrData := Finset.mem_filter.mp hrMem
    have hr := isMaynardDivisorTuple_of_mem_support hrData.1
    have hprod : 1 ≤
        ∏ h : BoundedGaps.engelsmaTuple, (maynardS2G (r h) : ℝ) := by
      have hNat : 0 < ∏ h : BoundedGaps.engelsmaTuple,
          maynardS2G (r h) := by
        apply Finset.prod_pos
        intro h hh
        have hreal := maynardS2G_pos_of_squarefree_coprime_primorial hD
          (hr.coordinate_squarefree h) (hr.coordinate_coprime_W h)
        exact_mod_cast hreal
      have hNatOne : 1 ≤ ∏ h : BoundedGaps.engelsmaTuple,
          maynardS2G (r h) := Nat.one_le_iff_ne_zero.mpr hNat.ne'
      exact_mod_cast hNatOne
    have hprodPos := maynardS2G_product_pos_of_supported hD hr
    have hprodAttach : 0 <
        ∏ h ∈ BoundedGaps.engelsmaTuple.attach,
          (maynardS2G (r h) : ℝ) := by
      simpa only [← Finset.univ_eq_attach] using hprodPos
    have hprodOneAttach : 1 ≤
        ∏ h ∈ BoundedGaps.engelsmaTuple.attach,
          (maynardS2G (r h) : ℝ) := by
      simpa only [← Finset.univ_eq_attach] using hprod
    dsimp [f]
    rw [abs_of_pos hprodAttach]
    exact (div_le_iff₀ hprodAttach).2 (by linarith)
  have hsum := Finset.sum_le_card_nsmul S f 1 hterm
  have hsum' : ∑ r ∈ S, f r ≤ (S.card : ℝ) := by
    simpa [nsmul_eq_mul] using hsum
  have hsubset : S ⊆ maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
      R (primorial D) := by
    intro r hrMem
    exact (Finset.mem_filter.mp hrMem).1
  have hcard := Finset.card_le_card hsubset
  simpa [S, f] using hsum'.trans (by exact_mod_cast hcard)

theorem abs_engelsmaS2CoordinateFiberShortSquareDiagonal_le_support_card
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple) (hD : 2 ≤ D) :
    |engelsmaS2CoordinateFiberShortSquareDiagonal R D m| ≤
      smallKCandidateBound ^ 2 *
        (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple R
          (primorial D)).card := by
  have hmass :=
    engelsmaS2CoordinateFiberShortReciprocalGMass_le_support_card
      (R := R) m hD
  calc
    |engelsmaS2CoordinateFiberShortSquareDiagonal R D m| ≤
        smallKCandidateBound ^ 2 *
          engelsmaS2CoordinateFiberShortReciprocalGMass R D m :=
      abs_engelsmaS2CoordinateFiberShortSquareDiagonal_le_reciprocalGMass
        R D m
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left hmass (sq_nonneg _)

end BoundedGaps.Maynard
