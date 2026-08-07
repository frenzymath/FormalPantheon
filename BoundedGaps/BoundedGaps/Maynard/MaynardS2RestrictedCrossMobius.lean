import BoundedGaps.Maynard.ConcreteS2RestrictedReindex
import BoundedGaps.Maynard.ImprovedGPY.Mobius
import BoundedGaps.Maynard.MaynardS1NontrivialMobius

noncomputable section

/-!
# Möbius split of the restricted S2 cross correction

The compatibility indicator is expanded by the ordered cross-coordinate
Möbius tuple. The all-one tuple is the unrestricted restricted S2 transform;
the remaining signed finite sum is retained as the exact cross correction.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance s2RestrictedCrossMobiusDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def compatibleDivisorPairRestrictedS2CommonDivisorTupleMobiusSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D,
    crossCoordinateMoebiusIndicator H d e *
      (if d m = 1 ∧ e m = 1 then
        ∑ u ∈ commonDivisorTupleSupport H d e,
          commonDivisorS2TupleTerm H d e u * (lambda d * lambda e)
      else 0)

def nontrivialRestrictedS2AuxiliaryMobiusSum
    (H : Finset ℕ) (_R : ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D,
    ∑ s ∈ (crossMoebiusTupleSupport H d e).erase
        (oneCrossMoebiusTuple H),
      crossMoebiusTupleTerm H s *
        (if d m = 1 ∧ e m = 1 then
          ∑ u ∈ commonDivisorTupleSupport H d e,
            commonDivisorS2TupleTerm H d e u * (lambda d * lambda e)
        else 0)

theorem compatibleRestrictedS2MembershipSum_eq_mobiusSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) :
    compatibleDivisorPairRestrictedS2CommonDivisorMembershipSum H D lambda m =
      compatibleDivisorPairRestrictedS2CommonDivisorTupleMobiusSum
        H D lambda m := by
  classical
  unfold compatibleDivisorPairRestrictedS2CommonDivisorMembershipSum
    compatibleDivisorPairRestrictedS2CommonDivisorTupleMobiusSum
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  rw [crossCoordinateMoebiusIndicator_eq_compatibility_indicator]
  by_cases hcross : IsCrossCoordinateCoprime H d e
  · simp [hcross]
  · simp [hcross]

theorem restrictedS2AuxiliaryMobiusSum_eq_unrestricted_add_nontrivial
    {H : Finset ℕ} {R W : ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} (m : H)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    compatibleDivisorPairRestrictedS2CommonDivisorTupleMobiusSum
        H D lambda m =
      unrestrictedDivisorPairRestrictedS2CommonDivisorTupleSum H D lambda m +
        nontrivialRestrictedS2AuxiliaryMobiusSum H R D lambda m := by
  classical
  unfold compatibleDivisorPairRestrictedS2CommonDivisorTupleMobiusSum
    unrestrictedDivisorPairRestrictedS2CommonDivisorTupleSum
    nontrivialRestrictedS2AuxiliaryMobiusSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hone := oneCrossMoebiusTuple_mem_support (hD d hd) (e := e)
  rw [crossCoordinateMoebiusIndicator_eq_auxiliaryTupleSum]
  rw [Finset.sum_mul]
  rw [← Finset.sum_erase_add _ _ hone]
  rw [crossMoebiusTupleTerm_one]
  ring

theorem incompatibleRestrictedS2_eq_neg_nontrivial
    {H : Finset ℕ} {R W : ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} (m : H)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    incompatibleDivisorPairRestrictedS2CommonDivisorTupleSum H D lambda m =
      -nontrivialRestrictedS2AuxiliaryMobiusSum H R D lambda m := by
  have hsplit := unrestrictedRestrictedS2_eq_compatible_add_incompatible
    H D lambda m
  have haux := restrictedS2AuxiliaryMobiusSum_eq_unrestricted_add_nontrivial
    (lambda := lambda) m hD
  have hcompat := compatibleRestrictedS2MembershipSum_eq_mobiusSum
    H D lambda m
  linarith

end BoundedGaps.Maynard
