import PrimesRestrictedDigits.SieveAsymptotics.SectionSixLowStrictPath
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixSourceStateConstructor
import Mathlib.Tactic.NormNum

/-!
# Source roots and truncated evaluation for the corrected Section 6 recurrence

This file connects the strict source bands to active nodes and gives the exact scalar
evaluator that recursively inspects only low strict `U` children. It is not the later
occurrence-preserving signed normal form.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixSourceBandMembership
    (band : SectionSixStateBand)
    (X thetaOne thetaTwo d : Real) : Prop :=
  match band with
  | SectionSixStateBand.low => d < X ^ thetaOne
  | SectionSixStateBand.high =>
      X ^ thetaTwo < d ∧ d < X ^ (1 - thetaTwo)

@[simp] theorem sectionSixSourceBandMembership_low
    (X thetaOne thetaTwo d : Real) :
    sectionSixSourceBandMembership SectionSixStateBand.low
      X thetaOne thetaTwo d ↔ d < X ^ thetaOne :=
  Iff.rfl

@[simp] theorem sectionSixSourceBandMembership_high
    (X thetaOne thetaTwo d : Real) :
    sectionSixSourceBandMembership SectionSixStateBand.high
      X thetaOne thetaTwo d ↔
        X ^ thetaTwo < d ∧ d < X ^ (1 - thetaTwo) :=
  Iff.rfl

theorem sectionSixSourceBandMembership_cutoff_le
    {band : SectionSixStateBand} {X thetaOne thetaTwo d : Real}
    (hband : sectionSixSourceBandMembership band
      X thetaOne thetaTwo d) :
    d ≤ sectionSixStateBandCutoff band X thetaOne thetaTwo := by
  cases band with
  | low =>
      exact le_of_lt hband
  | high =>
      exact le_of_lt hband.2

noncomputable def sectionSixSourceBandRoot
    {epsilon : Real} {length ell : Nat}
    (hlength : 1 ≤ length)
    {region : Set (Fin ell → Real)}
    (band : SectionSixStateBand)
    (p : Fin ell → Nat)
    (hp : IsPropositionSixOnePrimeTuple epsilon length region p)
    (delta : Real)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (hband : sectionSixSourceBandMembership band
      ((10 ^ length : Nat) : Real)
      (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
      (primeTupleProduct p : Real))
    (hcutoff_le_X :
      sectionSixStateBandCutoff band ((10 ^ length : Nat) : Real)
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ≤
        ((10 ^ length : Nat) : Real)) :
    SectionSixLowActiveNode
      ((10 ^ length : Nat) : Real) delta
      (sectionSixThetaGap epsilon)
      (sectionSixStateBandCutoff band ((10 ^ length : Nat) : Real)
        (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon))
      (((10 ^ length : Nat) : Real) ^ delta) band ell := by
  have hXNat : 1 < 10 ^ length :=
    Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) ≤ ((10 ^ length : Nat) : Real) := by
    exact_mod_cast hXNat.le
  have hpData := hp
  dsimp [IsPropositionSixOnePrimeTuple] at hpData
  have houterLower : ∀ i,
      ((10 ^ length : Nat) : Real) ^ delta ≤ (p i : Real) := by
    intro i
    exact (Real.rpow_le_rpow_of_exponent_le hX hdeltaGap).trans
      (hpData.2.2.1 i)
  let hinnerPrime : ∀ q, q ∈ ([] : List Nat) → q.Prime := by
    intro q hq
    simp at hq
  let hstate := sectionSixRecurrenceStateOfSourceTuple band
    SectionSixStateKind.T p [] hp hinnerPrime (by decide)
  refine
    { upper := ((10 ^ length : Nat) : Real) ^
        sectionSixThetaGap epsilon
      state := ⟨primeTupleProduct p * [].prod, hstate⟩
      y_eq := rfl
      R_le_X := hcutoff_le_X
      lower_le_upper :=
        Real.rpow_le_rpow_of_exponent_le hX hdeltaGap
      upper_le_range := le_rfl
      modulus_le := ?_
      ordered := by
        intro r hr
        change r ∈ ([] : List Nat) at hr
        simp at hr
      innerRange := by
        intro q hq
        change q ∈ ([] : List Nat) at hq
        simp at hq
      outerLower := houterLower
      activeKind := Or.inl rfl }
  simpa [hstate] using sectionSixSourceBandMembership_cutoff_le hband

noncomputable def sectionSixLowTruncatedValue
    (digit : Fin 10) (length fuel : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (node : SectionSixLowActiveNode X delta theta R y band ell) : Real :=
  match fuel with
  | 0 => sectionSixStateStrictTerm digit length node.state.2 node.upper
  | fuel + 1 =>
      sectionSixStateStrictTerm digit length node.state.2 y -
        (∑ q ∈ sectionSixStateLowPrimeInterval
            node.state R y node.upper,
          if hq : q ∈ sectionSixStateLowPrimeInterval
              node.state R y node.upper then
            sectionSixLowTruncatedValue digit length fuel
              (sectionSixLowActiveChild node q hq)
          else 0) -
        (∑ q ∈ sectionSixStateHighPrimeInterval
            node.state R y node.upper,
          sectionSixStrictPrimeTerm digit length
            (sectionSixStateModulusPNat node.state.2) q) -
        (∑ q ∈ sectionSixStateLowPrimeInterval
            node.state R y node.upper,
          sectionSixRepeatedPrimeTerm digit length
            (sectionSixStateModulusPNat node.state.2) q) -
        ∑ q ∈ sectionSixStateHighPrimeInterval
            node.state R y node.upper,
          sectionSixRepeatedPrimeTerm digit length
            (sectionSixStateModulusPNat node.state.2) q

noncomputable def sectionSixLowTerminalInspection
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (node : SectionSixLowActiveNode X delta theta R y band ell) : Real :=
  sectionSixStateStrictTerm digit length node.state.2 y -
      (∑ q ∈ sectionSixStateHighPrimeInterval node.state R y node.upper,
        sectionSixStrictPrimeTerm digit length
          (sectionSixStateModulusPNat node.state.2) q) -
      (∑ q ∈ sectionSixStateLowPrimeInterval node.state R y node.upper,
        sectionSixRepeatedPrimeTerm digit length
          (sectionSixStateModulusPNat node.state.2) q) -
      ∑ q ∈ sectionSixStateHighPrimeInterval node.state R y node.upper,
        sectionSixRepeatedPrimeTerm digit length
          (sectionSixStateModulusPNat node.state.2) q

theorem sectionSixLowTruncatedValue_eq_stateStrictTerm
    (digit : Fin 10) (length fuel : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (node : SectionSixLowActiveNode X delta theta R y band ell) :
    sectionSixLowTruncatedValue digit length fuel node =
      sectionSixStateStrictTerm digit length node.state.2 node.upper := by
  induction fuel generalizing node with
  | zero =>
      rfl
  | succ fuel ih =>
      unfold sectionSixLowTruncatedValue
      rw [sectionSixStateTerm_eq_four_branch_recurrence
        digit length node.state R node.lower_le_upper]
      have hlow :
          (∑ q ∈ sectionSixStateLowPrimeInterval
              node.state R y node.upper,
            if hq : q ∈ sectionSixStateLowPrimeInterval
                node.state R y node.upper then
              sectionSixLowTruncatedValue digit length fuel
                (sectionSixLowActiveChild node q hq)
            else 0) =
            ∑ q ∈ sectionSixStateLowPrimeInterval
                node.state R y node.upper,
              sectionSixStrictPrimeTerm digit length
                (sectionSixStateModulusPNat node.state.2) q := by
        apply Finset.sum_congr rfl
        intro q hq
        simp only [dif_pos hq]
        rw [ih (sectionSixLowActiveChild node q hq)]
        exact (sectionSixStrictPrimeTerm_eq_stateStrictTerm
          digit length node.state.2 SectionSixStateKind.U
          (sectionSixLowActivePrime node hq)
          (sectionSixLowActiveOrder node hq)).symm
      rw [hlow]
      ring

theorem sectionSixSourceBandRoot_truncatedValue_eq_sourceTerm
    {epsilon : Real} {length ell : Nat}
    (hlength : 1 ≤ length)
    {region : Set (Fin ell → Real)}
    (band : SectionSixStateBand)
    (p : Fin ell → Nat)
    (hp : IsPropositionSixOnePrimeTuple epsilon length region p)
    (delta : Real)
    (hdeltaGap : delta ≤ sectionSixThetaGap epsilon)
    (hband : sectionSixSourceBandMembership band
      ((10 ^ length : Nat) : Real)
      (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
      (primeTupleProduct p : Real))
    (hcutoff_le_X :
      sectionSixStateBandCutoff band ((10 ^ length : Nat) : Real)
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) ≤
        ((10 ^ length : Nat) : Real))
    (digit : Fin 10) (fuel : Nat) :
    sectionSixLowTruncatedValue digit length fuel
        (sectionSixSourceBandRoot hlength band p hp delta hdeltaGap
          hband hcutoff_le_X) =
      sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) := by
  rw [sectionSixLowTruncatedValue_eq_stateStrictTerm]
  unfold sectionSixStateStrictTerm
  congr 1
  apply PNat.eq
  simp [sectionSixSourceBandRoot, Nat.toPNat'_coe,
    sectionSixSourceTuple_outerProduct_pos hp]

theorem sectionSixLowTruncatedValue_succ_of_low_empty
    (digit : Fin 10) (length fuel : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (node : SectionSixLowActiveNode X delta theta R y band ell)
    (hempty : sectionSixStateLowPrimeInterval
      node.state R y node.upper = ∅) :
    sectionSixLowTruncatedValue digit length (fuel + 1) node =
      sectionSixLowTerminalInspection digit length node := by
  simp [sectionSixLowTruncatedValue, sectionSixLowTerminalInspection, hempty]

theorem sectionSixLowTruncatedValue_one_eq_terminal_of_maximal_path
    (digit : Fin 10) (length : Nat)
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {start target : SectionSixLowActiveNode X delta theta R y band ell}
    {steps : List Nat}
    (hX : 1 < X) (hdelta : 0 < delta)
    (hpath : SectionSixLowStrictPath start target steps)
    (hmax : steps.length = Nat.ceil (1 / delta)) :
    sectionSixLowTruncatedValue digit length 1 target =
      sectionSixLowTerminalInspection digit length target := by
  apply sectionSixLowTruncatedValue_succ_of_low_empty
  exact
    sectionSixLowStrictPath_lowPrimeInterval_eq_empty_of_length_eq_ceil_inv_delta
      hX hdelta hpath hmax

end

end PrimesRestrictedDigits
