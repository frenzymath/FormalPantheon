import PrimesRestrictedDigits.ExceptionalMinorArcs.ExceptionalPropositionScalars
import PrimesRestrictedDigits.GenericMinorArcs.GenericMinorArc

/-!
# Ordinary and high exceptional-frequency partition

This gives the exact finite partition used to join Propositions 9.2 and 9.3.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Frequencies in an arbitrary source set which lie outside the raw major
arcs at a natural logarithmic cutoff. -/
def exceptionalMinorArcFrequencies
    (length D : Nat) (E : Finset (Fin (10 ^ length))) :
    Finset (Fin (10 ^ length)) :=
  E.filter fun h =>
    h.val ∉ majorArcRawFrequencies (10 ^ length)
      (Real.log (((10 ^ length : Nat) : Real)) ^ D)

/-- The part of an arbitrary exceptional-minor carrier lying in the canonical
generic exceptional set. -/
def exceptionalMinorArcHighFrequencies
    (digit : Fin 10) (length D : Nat)
    (E : Finset (Fin (10 ^ length))) : Finset (Fin (10 ^ length)) :=
  (exceptionalMinorArcFrequencies length D E).filter fun h =>
    h ∈ genericExceptionalFrequencies digit length

/-- The complementary ordinary part of an arbitrary exceptional-minor
carrier. -/
def exceptionalMinorArcOrdinaryFrequencies
    (digit : Fin 10) (length D : Nat)
    (E : Finset (Fin (10 ^ length))) : Finset (Fin (10 ^ length)) :=
  (exceptionalMinorArcFrequencies length D E).filter fun h =>
    h ∉ genericExceptionalFrequencies digit length

theorem exceptionalMinorArcHighFrequencies_subset_genericExceptional
    (digit : Fin 10) (length D : Nat)
    (E : Finset (Fin (10 ^ length))) :
    exceptionalMinorArcHighFrequencies digit length D E ⊆
      genericExceptionalFrequencies digit length := by
  intro h hh
  exact (Finset.mem_filter.mp hh).2

theorem exceptionalMinorArcOrdinaryFrequencies_subset_genericOrdinary
    (digit : Fin 10) (length D : Nat)
    (E : Finset (Fin (10 ^ length))) :
    exceptionalMinorArcOrdinaryFrequencies digit length D E ⊆
      genericOrdinaryFrequencies digit length := by
  intro h hh
  have hnot : h ∉ genericExceptionalFrequencies digit length :=
    (Finset.mem_filter.mp hh).2
  simpa only [genericOrdinaryFrequencies, Finset.mem_sdiff,
    Finset.mem_univ, true_and] using hnot

theorem mem_exceptionalMinorArcHighFrequencies_not_major
    {digit : Fin 10} {length D : Nat}
    {E : Finset (Fin (10 ^ length))} {h : Fin (10 ^ length)}
    (hh : h ∈ exceptionalMinorArcHighFrequencies digit length D E) :
    h.val ∉ majorArcRawFrequencies (10 ^ length)
      (Real.log (((10 ^ length : Nat) : Real)) ^ D) := by
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hh).1).2

/-- The ordinary and high filters recover the literal exceptional-minor
carrier exactly. -/
theorem sum_exceptionalMinorArcHigh_add_ordinary
    {M : Type*} [AddCommMonoid M]
    (digit : Fin 10) (length D : Nat)
    (E : Finset (Fin (10 ^ length))) (f : Fin (10 ^ length) → M) :
    (∑ h ∈ exceptionalMinorArcHighFrequencies digit length D E, f h) +
        ∑ h ∈ exceptionalMinorArcOrdinaryFrequencies digit length D E, f h =
      ∑ h ∈ exceptionalMinorArcFrequencies length D E, f h := by
  simpa only [exceptionalMinorArcHighFrequencies,
    exceptionalMinorArcOrdinaryFrequencies] using
      (exceptionalMinorArcFrequencies length D E).sum_filter_add_sum_filter_not
        (fun h => h ∈ genericExceptionalFrequencies digit length) f

/-- The norm of the ordinary restricted sum is bounded by the full canonical
ordinary norm sum. -/
theorem norm_sum_exceptionalMinorArcOrdinary_le
    (digit : Fin 10) (length D : Nat)
    (E : Finset (Fin (10 ^ length)))
    (f : Fin (10 ^ length) → Complex) :
    ‖∑ h ∈ exceptionalMinorArcOrdinaryFrequencies digit length D E, f h‖ ≤
      ∑ h ∈ genericOrdinaryFrequencies digit length, ‖f h‖ := by
  calc
    ‖∑ h ∈ exceptionalMinorArcOrdinaryFrequencies digit length D E, f h‖ ≤
        ∑ h ∈ exceptionalMinorArcOrdinaryFrequencies digit length D E,
          ‖f h‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ genericOrdinaryFrequencies digit length, ‖f h‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (exceptionalMinorArcOrdinaryFrequencies_subset_genericOrdinary
          digit length D E)
        (fun h _ _ => norm_nonneg (f h))

end

end PrimesRestrictedDigits
