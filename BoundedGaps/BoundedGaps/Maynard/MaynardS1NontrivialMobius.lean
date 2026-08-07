import BoundedGaps.Maynard.MaynardS1CrossCorrection

noncomputable section

/-!
# The nontrivial auxiliary-Moebius part of S1

The all-ones cross tuple gives the unrestricted diagonal. Every other cross
tuple forms the signed correction.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def oneCrossMoebiusTuple (H : Finset ℕ) :
    ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ :=
  fun _ _ => 1

def nontrivialAuxiliaryMobiusSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D,
    ∑ s ∈ (crossMoebiusTupleSupport H d e).erase (oneCrossMoebiusTuple H),
      crossMoebiusTupleTerm H s *
        (∑ u ∈ commonDivisorTupleSupport H d e,
          commonDivisorTupleTerm H d e u * (lambda d * lambda e))

theorem oneCrossMoebiusTuple_mem_support
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) :
    oneCrossMoebiusTuple H ∈ crossMoebiusTupleSupport H d e := by
  rw [mem_crossMoebiusTupleSupport_iff hd]
  intro ab hab
  exact ⟨one_dvd _, one_dvd _⟩

theorem crossMoebiusTupleTerm_one (H : Finset ℕ) :
    crossMoebiusTupleTerm H (oneCrossMoebiusTuple H) = 1 := by
  unfold crossMoebiusTupleTerm oneCrossMoebiusTuple
  simp

theorem auxiliaryMobiusSum_eq_unrestricted_add_nontrivial
    {H : Finset ℕ} {R W : ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    compatibleDivisorPairCommonDivisorTupleAuxiliaryMobiusSum H D lambda =
      unrestrictedDivisorPairCommonDivisorTupleSum H D lambda +
        nontrivialAuxiliaryMobiusSum H D lambda := by
  classical
  unfold compatibleDivisorPairCommonDivisorTupleAuxiliaryMobiusSum
    unrestrictedDivisorPairCommonDivisorTupleSum nontrivialAuxiliaryMobiusSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hone := oneCrossMoebiusTuple_mem_support (hD d hd) (e := e)
  rw [← Finset.sum_erase_add _ _ hone]
  rw [crossMoebiusTupleTerm_one, one_mul]
  ring

theorem incompatibleSum_eq_neg_nontrivialAuxiliaryMobiusSum
    {H : Finset ℕ} {R W : ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    incompatibleDivisorPairCommonDivisorTupleSum H D lambda =
      -nontrivialAuxiliaryMobiusSum H D lambda := by
  have hsplit := unrestrictedCommonDivisorTupleSum_eq_compatible_add_incompatible
    H D lambda
  have haux := auxiliaryMobiusSum_eq_unrestricted_add_nontrivial
    (lambda := lambda) hD
  have hcompat1 := compatibleDivisorPairCommonDivisorTupleSum_eq_mobiusSum
    H D lambda
  have hcompat2 :=
    compatibleDivisorPairCommonDivisorTupleMobiusSum_eq_auxiliaryMobiusSum
      H D lambda
  linarith

end BoundedGaps.Maynard
