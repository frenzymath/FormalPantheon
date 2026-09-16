import PrimesRestrictedDigits.Fourier.DecimalGridInversion
import PrimesRestrictedDigits.MajorArcs.MajorArcContribution
import PrimesRestrictedDigits.ExceptionalMinorArcs.ExceptionalFrequencyPartition

/-!
# Decimal-grid Type II frequency partition

This file records the exact finite partition used after the full-grid Fourier
expansion in the proof of Proposition 7.2 of `MAYNARD-PRD-PUBLISHED`, p. 168.
The typed major carrier has priority over both minor carriers; in particular,
no inclusion between the major and generic exceptional sets is assumed.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The natural raw major carrier lifted to the complete typed decimal grid. -/
def typeIIFrequencyMajorFrequencies
    (length D : Nat) : Finset (Fin (10 ^ length)) :=
  (Finset.univ : Finset (Fin (10 ^ length))).filter fun h =>
    h.val ∈ majorArcRawFrequencies (10 ^ length)
      (Real.log (((10 ^ length : Nat) : Real)) ^ D)

/-- The generic exceptional frequencies outside the typed major carrier. -/
def typeIIFrequencyHighFrequencies
    (digit : Fin 10) (length D : Nat) : Finset (Fin (10 ^ length)) :=
  exceptionalMinorArcHighFrequencies digit length D (Finset.univ)

/-- The generic ordinary frequencies outside the typed major carrier. -/
def typeIIFrequencyOrdinaryFrequencies
    (digit : Fin 10) (length D : Nat) : Finset (Fin (10 ^ length)) :=
  exceptionalMinorArcOrdinaryFrequencies digit length D (Finset.univ)

@[simp]
theorem mem_typeIIFrequencyMajorFrequencies
    {length D : Nat} {h : Fin (10 ^ length)} :
    h ∈ typeIIFrequencyMajorFrequencies length D ↔
      h.val ∈ majorArcRawFrequencies (10 ^ length)
        (Real.log (((10 ^ length : Nat) : Real)) ^ D) := by
  simp [typeIIFrequencyMajorFrequencies]

@[simp]
theorem mem_typeIIFrequencyHighFrequencies
    {digit : Fin 10} {length D : Nat} {h : Fin (10 ^ length)} :
    h ∈ typeIIFrequencyHighFrequencies digit length D ↔
      h.val ∉ majorArcRawFrequencies (10 ^ length)
          (Real.log (((10 ^ length : Nat) : Real)) ^ D) ∧
        h ∈ genericExceptionalFrequencies digit length := by
  simp only [typeIIFrequencyHighFrequencies,
    exceptionalMinorArcHighFrequencies, exceptionalMinorArcFrequencies,
    Finset.mem_filter, Finset.mem_univ, true_and]

@[simp]
theorem mem_typeIIFrequencyOrdinaryFrequencies
    {digit : Fin 10} {length D : Nat} {h : Fin (10 ^ length)} :
    h ∈ typeIIFrequencyOrdinaryFrequencies digit length D ↔
      h.val ∉ majorArcRawFrequencies (10 ^ length)
          (Real.log (((10 ^ length : Nat) : Real)) ^ D) ∧
        h ∉ genericExceptionalFrequencies digit length := by
  simp only [typeIIFrequencyOrdinaryFrequencies,
    exceptionalMinorArcOrdinaryFrequencies, exceptionalMinorArcFrequencies,
    Finset.mem_filter, Finset.mem_univ, true_and]

/-- The high carrier is the canonical exceptional carrier with the major
filter applied once, in the source's `E \ M` order. -/
theorem typeIIFrequencyHighFrequencies_eq_exceptionalMinorArcFrequencies
    (digit : Fin 10) (length D : Nat) :
    typeIIFrequencyHighFrequencies digit length D =
      exceptionalMinorArcFrequencies length D
        (genericExceptionalFrequencies digit length) := by
  classical
  ext h
  simp only [mem_typeIIFrequencyHighFrequencies,
    exceptionalMinorArcFrequencies, Finset.mem_filter]
  tauto

/-- The ordinary carrier is contained in the canonical generic ordinary set. -/
theorem typeIIFrequencyOrdinaryFrequencies_subset_genericOrdinary
    (digit : Fin 10) (length D : Nat) :
    typeIIFrequencyOrdinaryFrequencies digit length D ⊆
      genericOrdinaryFrequencies digit length := by
  intro h hh
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
    (mem_typeIIFrequencyOrdinaryFrequencies.mp hh).2⟩

theorem typeIIFrequencyHighFrequencies_subset_genericExceptional
    (digit : Fin 10) (length D : Nat) :
    typeIIFrequencyHighFrequencies digit length D ⊆
      genericExceptionalFrequencies digit length := by
  intro h hh
  exact (mem_typeIIFrequencyHighFrequencies.mp hh).2

theorem typeIIFrequencyMajorFrequencies_disjoint_high
    (digit : Fin 10) (length D : Nat) :
    Disjoint (typeIIFrequencyMajorFrequencies length D)
      (typeIIFrequencyHighFrequencies digit length D) := by
  classical
  rw [Finset.disjoint_left]
  intro h hM hH
  exact (mem_typeIIFrequencyHighFrequencies.mp hH).1
    (mem_typeIIFrequencyMajorFrequencies.mp hM)

theorem typeIIFrequencyMajorFrequencies_disjoint_ordinary
    (digit : Fin 10) (length D : Nat) :
    Disjoint (typeIIFrequencyMajorFrequencies length D)
      (typeIIFrequencyOrdinaryFrequencies digit length D) := by
  classical
  rw [Finset.disjoint_left]
  intro h hM hO
  exact (mem_typeIIFrequencyOrdinaryFrequencies.mp hO).1
    (mem_typeIIFrequencyMajorFrequencies.mp hM)

theorem typeIIFrequencyHighFrequencies_disjoint_ordinary
    (digit : Fin 10) (length D : Nat) :
    Disjoint (typeIIFrequencyHighFrequencies digit length D)
      (typeIIFrequencyOrdinaryFrequencies digit length D) := by
  classical
  rw [Finset.disjoint_left]
  intro h hH hO
  exact (mem_typeIIFrequencyOrdinaryFrequencies.mp hO).2
    (mem_typeIIFrequencyHighFrequencies.mp hH).2

/-- The priority carriers exhaust the typed complete frequency grid. -/
theorem typeIIFrequencyMajorFrequencies_union_high_union_ordinary
    (digit : Fin 10) (length D : Nat) :
    typeIIFrequencyMajorFrequencies length D ∪
        typeIIFrequencyHighFrequencies digit length D ∪
        typeIIFrequencyOrdinaryFrequencies digit length D =
      (Finset.univ : Finset (Fin (10 ^ length))) := by
  classical
  ext h
  by_cases hM : h ∈ typeIIFrequencyMajorFrequencies length D
  · simp [hM]
  · have hnotM : h.val ∉ majorArcRawFrequencies (10 ^ length)
        (Real.log (((10 ^ length : Nat) : Real)) ^ D) := by
      intro hraw
      exact hM (mem_typeIIFrequencyMajorFrequencies.mpr hraw)
    by_cases hE : h ∈ genericExceptionalFrequencies digit length
    · have hH : h ∈ typeIIFrequencyHighFrequencies digit length D :=
        mem_typeIIFrequencyHighFrequencies.mpr ⟨hnotM, hE⟩
      simp [hM, hH]
    · have hO : h ∈ typeIIFrequencyOrdinaryFrequencies digit length D :=
        mem_typeIIFrequencyOrdinaryFrequencies.mpr ⟨hnotM, hE⟩
      simp [hM, hO]

/-- Exact additive decomposition of every finite-grid sum by the priority
partition. -/
theorem sum_typeIIFrequencyMajor_add_high_add_ordinary
    {M : Type*} [AddCommMonoid M]
    (digit : Fin 10) (length D : Nat) (f : Fin (10 ^ length) → M) :
    (∑ h ∈ typeIIFrequencyMajorFrequencies length D, f h) +
        ((∑ h ∈ typeIIFrequencyHighFrequencies digit length D, f h) +
          ∑ h ∈ typeIIFrequencyOrdinaryFrequencies digit length D, f h) =
      ∑ h : Fin (10 ^ length), f h := by
  classical
  have hMH := typeIIFrequencyMajorFrequencies_disjoint_high digit length D
  have hMO := typeIIFrequencyMajorFrequencies_disjoint_ordinary digit length D
  have hHO := typeIIFrequencyHighFrequencies_disjoint_ordinary digit length D
  have hMHO : Disjoint (typeIIFrequencyMajorFrequencies length D)
      (typeIIFrequencyHighFrequencies digit length D ∪
        typeIIFrequencyOrdinaryFrequencies digit length D) := by
    exact Finset.disjoint_union_right.mpr ⟨hMH, hMO⟩
  calc
    (∑ h ∈ typeIIFrequencyMajorFrequencies length D, f h) +
          ((∑ h ∈ typeIIFrequencyHighFrequencies digit length D, f h) +
            ∑ h ∈ typeIIFrequencyOrdinaryFrequencies digit length D, f h) =
        (∑ h ∈ typeIIFrequencyMajorFrequencies length D, f h) +
          ∑ h ∈ typeIIFrequencyHighFrequencies digit length D ∪
            typeIIFrequencyOrdinaryFrequencies digit length D, f h := by
      rw [Finset.sum_union hHO]
    _ = ∑ h ∈ typeIIFrequencyMajorFrequencies length D ∪
          typeIIFrequencyHighFrequencies digit length D ∪
          typeIIFrequencyOrdinaryFrequencies digit length D, f h := by
      rw [Finset.union_assoc]
      rw [Finset.sum_union hMHO]
    _ = ∑ h : Fin (10 ^ length), f h := by
      rw [typeIIFrequencyMajorFrequencies_union_high_union_ordinary]

/-- Reindex a typed major sum through the natural representatives in the raw
major carrier. -/
theorem sum_typeIIFrequencyMajorFrequencies_reindex
    {M : Type*} [AddCommMonoid M]
    (length D : Nat) (f : Nat → M) :
    (∑ h ∈ typeIIFrequencyMajorFrequencies length D, f h.val) =
      ∑ n ∈ majorArcRawFrequencies (10 ^ length)
        (Real.log (((10 ^ length : Nat) : Real)) ^ D),
        f n := by
  classical
  let raw := majorArcRawFrequencies (10 ^ length)
    (Real.log (((10 ^ length : Nat) : Real)) ^ D)
  have hrawSubset : raw ⊆ Finset.range (10 ^ length) := by
    intro n hn
    exact (Finset.filter_subset _ _ hn)
  apply Finset.sum_bij (fun h hh => h.val)
  · intro h hh
    exact (Finset.mem_filter.mp hh).2
  · intro h₁ hh₁ h₂ hh₂ heq
    exact Fin.ext heq
  · intro n hn
    refine ⟨⟨n, Finset.mem_range.mp (hrawSubset hn)⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
  · intro h hn
    rfl

/-- The Fourier summand attached to a typed decimal-grid frequency. -/
noncomputable def typeIIFrequencyFourierTerm
    (digit : Fin 10) (length : Nat) (w : Nat → Complex)
    (h : Fin (10 ^ length)) : Complex :=
  paddedDigitFourierSum digit length h.val *
    majorArcWeightedPhaseSum (Finset.range (10 ^ length)) w
      (-((h.val : Real) / ((10 ^ length : Nat) : Real)))

/-- The typed major Fourier sum, with the unnormalized grid factor removed. -/
noncomputable def typeIIFrequencyMajorContribution
    (digit : Fin 10) (length D : Nat) (w : Nat → Complex) : Complex :=
  (∑ h ∈ typeIIFrequencyMajorFrequencies length D,
      typeIIFrequencyFourierTerm digit length w h) /
    ((10 ^ length : Nat) : Complex)

/-- The typed major Fourier contribution is exactly the existing natural raw
major contribution. -/
theorem typeIIFrequencyMajorContribution_eq_majorArcRawContribution
    (digit : Fin 10) (length D : Nat) (w : Nat → Complex) :
    typeIIFrequencyMajorContribution digit length D w =
      majorArcRawContribution (10 ^ length)
        (Real.log (((10 ^ length : Nat) : Real)) ^ D)
        (paddedRestrictedNumbers digit length) (Finset.range (10 ^ length)) w := by
  classical
  unfold typeIIFrequencyMajorContribution typeIIFrequencyFourierTerm
  let g : Nat → Complex := fun n =>
    paddedDigitFourierSum digit length n *
      majorArcWeightedPhaseSum (Finset.range (10 ^ length)) w
        (-((n : Real) / ((10 ^ length : Nat) : Real)))
  change (∑ h ∈ typeIIFrequencyMajorFrequencies length D, g h.val) /
      ((10 ^ length : Nat) : Complex) = _
  rw [sum_typeIIFrequencyMajorFrequencies_reindex]
  unfold majorArcRawContribution
  apply congrArg (fun z : Complex => z / ((10 ^ length : Nat) : Complex))
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [g]
  rw [majorArcWeightedPhaseSum_padded_eq]

end

end PrimesRestrictedDigits
