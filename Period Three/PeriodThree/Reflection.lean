module

public import Mathlib.Topology.Algebra.Ring.Real
public import PeriodThree.Statement

meta import all Mathlib.Tactic.Linarith -- shake: keep (used by the order transport proof)
meta import all Mathlib.Tactic.Ring -- shake: keep (used by the reflected distance proof)

/-!
# Reflection conjugacy for interval maps

Negation conjugates a real map with its order-reversing reflection.  This file
transports every clause of Li and Yorke's Theorem I through that conjugacy, as
used for the reversed orbit-order branch in [LY75, Theorem I, p. 987].
-/

@[expose] public section

open Set

namespace PeriodThree

/-- Reflection of a set across the origin, used for the reversed branch of
[LY75, Theorem I, p. 987]. -/
def negSet (S : Set ℝ) : Set ℝ := {x | -x ∈ S}

/-- The map conjugate to `F` by reflection across the origin, as used for the
reversed branch of [LY75, Theorem I, p. 987]. -/
def reverseMap (F : ℝ → ℝ) (x : ℝ) : ℝ := -F (-x)

/-- Membership in the reflected set used in [LY75, reversed branch, p. 987]. -/
@[simp] theorem memNegSet {S : Set ℝ} {x : ℝ} : x ∈ negSet S ↔ -x ∈ S := Iff.rfl

/-- Reflecting a set twice returns the original set; this supports the two-way
transport of [LY75, Theorem I, p. 987]. -/
@[simp] theorem negSetNegSet (S : Set ℝ) : negSet (negSet S) = S := by
  ext x
  simp [negSet]

/-- Reflecting a map twice returns the original map; this supports the two-way
transport of [LY75, Theorem I, p. 987]. -/
@[simp] theorem reverseMapReverseMap (F : ℝ → ℝ) : reverseMap (reverseMap F) = F := by
  funext x
  simp [reverseMap]

/-- Iterates of a reflected map are the reflected iterates of the original
map, the conjugacy used in [LY75, reversed branch, p. 987]. -/
@[simp] theorem reverseMapIterate (F : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    ((reverseMap F)^[n]) x = -(F^[n]) (-x) := by
  induction n with
  | zero => simp
  | succ n ih => simp [Function.iterate_succ_apply', reverseMap, ih]

/-- Reflection preserves periodicity at every proposed period, as required by
[LY75, Theorem I, part T1, p. 987]. -/
theorem isPeriodicPtReverseMapIff (F : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    Function.IsPeriodicPt (reverseMap F) n x ↔ Function.IsPeriodicPt F n (-x) := by
  simp only [Function.IsPeriodicPt, Function.IsFixedPt, reverseMapIterate]
  constructor
  · intro h
    simpa using congrArg Neg.neg h
  · intro h
    simpa using congrArg Neg.neg h

/-- Reflection preserves exact least periods, as required by [LY75, Theorem I,
part T1, p. 987]. -/
@[simp] theorem minimalPeriodReverseMap (F : ℝ → ℝ) (x : ℝ) :
    Function.minimalPeriod (reverseMap F) x = Function.minimalPeriod F (-x) :=
  Function.minimalPeriod_eq_minimalPeriod_iff.mpr
    (fun n => isPeriodicPtReverseMapIff F n x)

/-- Reflection preserves membership in the periodic-point set used in [LY75,
Theorem I, part T2 and condition (B), p. 987]. -/
theorem memPeriodicPtsReverseMapIff (F : ℝ → ℝ) (x : ℝ) :
    x ∈ Function.periodicPts (reverseMap F) ↔ -x ∈ Function.periodicPts F := by
  simp only [Function.mem_periodicPts]
  constructor
  · rintro ⟨n, hn, hx⟩
    exact ⟨n, hn, (isPeriodicPtReverseMapIff F n x).mp hx⟩
  · rintro ⟨n, hn, hx⟩
    exact ⟨n, hn, (isPeriodicPtReverseMapIff F n x).mpr hx⟩

/-- Reflection preserves the complete orbit-distance sequence from [LY75,
equations (2.1)-(2.2) and condition (B), p. 987]. -/
@[simp] theorem orbitDistanceReverseMap (F : ℝ → ℝ) (p q : ℝ) :
    orbitDistance (reverseMap F) p q = orbitDistance F (-p) (-q) := by
  funext n
  simp only [orbitDistance, reverseMapIterate]
  congr 1
  rw [show -(F^[n]) (-p) - -(F^[n]) (-q) = -((F^[n]) (-p) - (F^[n]) (-q)) by ring]
  exact abs_neg _

/-- Negation preserves countability of the scrambled set in [LY75, Theorem I,
part T2, p. 987]. -/
@[simp] theorem countableNegSetIff {S : Set ℝ} : (negSet S).Countable ↔ S.Countable := by
  constructor
  · intro h
    have hp := h.preimage (neg_injective : Function.Injective fun x : ℝ => -x)
    simpa [negSet] using hp
  · intro h
    exact h.preimage (neg_injective : Function.Injective fun x : ℝ => -x)

/-- Order-connectedness is invariant under the reflection used in [LY75,
reversed branch, p. 987]. -/
theorem OrdConnected.negSet {J : Set ℝ} (hJ : J.OrdConnected) : (negSet J).OrdConnected :=
  hJ.preimage_anti fun _ _ h => neg_le_neg h

/-- Continuity on an interval is invariant under the reflection used in
[LY75, reversed branch, p. 987]. -/
theorem ContinuousOn.reflected {J : Set ℝ} {F : ℝ → ℝ} (hF : ContinuousOn F J) :
    ContinuousOn (reverseMap F) (negSet J) := by
  exact (hF.comp continuous_neg.continuousOn fun _ hx => hx).neg

/-- The interval self-map property is invariant under the reflection used in
[LY75, reversed branch, p. 987]. -/
theorem MapsTo.reflected {J : Set ℝ} {F : ℝ → ℝ} (hFJ : MapsTo F J J) :
    MapsTo (reverseMap F) (negSet J) (negSet J) := by
  intro x hx
  change -PeriodThree.reverseMap F x ∈ J
  simpa [reverseMap] using hFJ hx

/-- Reflection swaps the increasing and decreasing alternatives, and therefore
preserves the orbit-order disjunction in [LY75, Theorem I, p. 987]. -/
theorem orbitOrderReverseMapIff (F : ℝ → ℝ) (a : ℝ) :
    OrbitOrder (reverseMap F) a ↔ OrbitOrder F (-a) := by
  simp only [OrbitOrder, reverseMapIterate, reverseMap]
  constructor
  · rintro (h | h)
    · right
      constructor
      · linarith [h.1]
      constructor <;> linarith [h.2.1, h.2.2]
    · left
      constructor
      · linarith [h.1]
      constructor <;> linarith [h.2.1, h.2.2]
  · rintro (h | h)
    · right
      constructor
      · linarith [h.1]
      constructor <;> linarith [h.2.1, h.2.2]
    · left
      constructor
      · linarith [h.1]
      constructor <;> linarith [h.2.1, h.2.2]

private theorem theoremIConclusionOfReflected
    {J : Set ℝ} {F : ℝ → ℝ}
    (h : TheoremIConclusion (reverseMap F) (negSet J)) :
    TheoremIConclusion F J := by
  rcases h with ⟨hperiods, S, hS, hseparated⟩
  refine ⟨?_, negSet S, ?_, ?_⟩
  · intro k hk
    obtain ⟨x, hxJ, hxperiod⟩ := hperiods k hk
    refine ⟨-x, hxJ, ?_⟩
    simpa using hxperiod
  · rcases hS with ⟨hSJ, hSuncountable, hSperiodic, hSpairs⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx
      simpa using hSJ hx
    · simpa using hSuncountable
    · rw [Set.disjoint_left]
      intro x hxS hxperiodic
      apply Set.disjoint_left.mp hSperiodic hxS
      have : -x ∈ Function.periodicPts (reverseMap F) :=
        (memPeriodicPtsReverseMapIff F (-x)).mpr (by simpa using hxperiodic)
      simpa using this
    · intro p q hpS hqS hpq
      have hreflected := hSpairs hpS hqS (fun h => hpq (neg_injective h))
      simpa [LiYorkePair] using hreflected
  · intro p q hpS hqJ hqperiodic
    have hqReflected : -q ∈ Function.periodicPts (reverseMap F) :=
      (memPeriodicPtsReverseMapIff F (-q)).mpr (by simpa using hqperiodic)
    have hreflected := hseparated hpS (by simpa using hqJ) hqReflected
    simpa [SeparatedFromPeriodic] using hreflected

/-- Every clause of the conclusion of Theorem I is invariant under reflection,
including the actual uncountable scrambled set and separation from all periodic
points [LY75, Theorem I, p. 987]. -/
theorem theoremIConclusionReverseMapIff (F : ℝ → ℝ) (J : Set ℝ) :
    TheoremIConclusion (reverseMap F) (negSet J) ↔ TheoremIConclusion F J := by
  constructor
  · exact theoremIConclusionOfReflected
  · intro h
    apply theoremIConclusionOfReflected (J := negSet J) (F := reverseMap F)
    simpa using h

end PeriodThree
