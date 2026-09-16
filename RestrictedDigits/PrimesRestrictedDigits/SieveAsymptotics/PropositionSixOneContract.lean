import PrimesRestrictedDigits.MajorArcs.Factorization
import PrimesRestrictedDigits.SieveDecomposition.SectionSixPrimeRecurrence
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Proposition 6.1 statement

This file defines the finite prime-tuple carrier and direct eventual statement of Maynard's
Proposition 6.1.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.1, pp. 137 and 156--158.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixThetaOne (epsilon : Real) : Real :=
  9 / 25 + 2 * epsilon

def sectionSixThetaTwo (epsilon : Real) : Real :=
  17 / 40 - 2 * epsilon

def sectionSixThetaGap (epsilon : Real) : Real :=
  sectionSixThetaTwo epsilon - sectionSixThetaOne epsilon

theorem sectionSixThetaGap_eq (epsilon : Real) :
    sectionSixThetaGap epsilon = 13 / 200 - 4 * epsilon := by
  simp only [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  ring

theorem sectionSix_parameter_bounds
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64) :
    0 < sectionSixThetaGap epsilon ∧
      0 < sectionSixThetaOne epsilon ∧
      sectionSixThetaOne epsilon < 1 ∧
      0 < 1 - sectionSixThetaOne epsilon ∧
      1 - sectionSixThetaTwo epsilon < 50 / 77 - epsilon := by
  rw [sectionSixThetaGap_eq]
  simp only [sectionSixThetaOne, sectionSixThetaTwo]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The literal source predicate for one Proposition 6.1 prime tuple. -/
def IsPropositionSixOnePrimeTuple
    (epsilon : Real) (length : Nat) {ell : Nat}
    (region : Set (Fin ell → Real)) (p : Fin ell → Nat) : Prop :=
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  (∀ i, (p i).Prime) ∧
    Monotone p ∧
    (∀ i, X ^ sectionSixThetaGap epsilon ≤ (p i : Real)) ∧
    (primeTupleProduct p : Real) ≤
      X ^ (1 - sectionSixThetaOne epsilon) ∧
    (fun i => normalizedPrimeLog XNat (p i)) ∈ region

/-- The finite realization of the source prime-tuple carrier. The
coordinatewise cutoff at `X` is proved redundant on the accepted parameter
domain. -/
noncomputable def propositionSixOnePrimeTuples
    (epsilon : Real) (ell : Nat) (region : Set (Fin ell → Real))
    (length : Nat) : Finset (Fin ell → Nat) := by
  classical
  let XNat : Nat := 10 ^ length
  exact (Fintype.piFinset fun _ : Fin ell => Nat.primesLE XNat).filter
    (IsPropositionSixOnePrimeTuple epsilon length region)

@[simp] theorem mem_propositionSixOnePrimeTuples
    {epsilon : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)} {p : Fin ell → Nat} :
    p ∈ propositionSixOnePrimeTuples epsilon ell region length ↔
      (∀ i, p i ∈ Nat.primesLE (10 ^ length)) ∧
        IsPropositionSixOnePrimeTuple epsilon length region p := by
  classical
  simp [propositionSixOnePrimeTuples, Fintype.mem_piFinset]

theorem primeTupleProduct_pos_of_mem_propositionSixOnePrimeTuples
    {epsilon : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)} {p : Fin ell → Nat}
    (hp : p ∈ propositionSixOnePrimeTuples epsilon ell region length) :
    0 < primeTupleProduct p := by
  rw [primeTupleProduct]
  apply Finset.prod_pos
  intro i hi
  exact (Nat.prime_of_mem_primesLE
    ((mem_propositionSixOnePrimeTuples.mp hp).1 i)).pos

theorem coe_toPNat'_primeTupleProduct_of_mem
    {epsilon : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)} {p : Fin ell → Nat}
    (hp : p ∈ propositionSixOnePrimeTuples epsilon ell region length) :
    ((primeTupleProduct p).toPNat' : Nat) = primeTupleProduct p := by
  rw [Nat.toPNat'_coe,
    if_pos (primeTupleProduct_pos_of_mem_propositionSixOnePrimeTuples hp)]

theorem mem_propositionSixOnePrimeTuples_iff_source
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {ell length : Nat} (hlength : 1 ≤ length)
    {region : Set (Fin ell → Real)} {p : Fin ell → Nat} :
    p ∈ propositionSixOnePrimeTuples epsilon ell region length ↔
      IsPropositionSixOnePrimeTuple epsilon length region p := by
  rw [mem_propositionSixOnePrimeTuples]
  refine and_iff_right_of_imp ?_
  intro hpData i
  rw [Nat.mem_primesLE]
  dsimp [IsPropositionSixOnePrimeTuple] at hpData
  have hprime : ∀ j, (p j).Prime := hpData.1
  have hproduct : (primeTupleProduct p : Real) ≤
      ((10 ^ length : Nat) : Real) ^
        (1 - sectionSixThetaOne epsilon) := hpData.2.2.2.1
  have hXNat : 1 < 10 ^ length := by
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
    exact_mod_cast hXNat
  have hthetaOne : 0 < sectionSixThetaOne epsilon := by
    simp only [sectionSixThetaOne]
    linarith
  have hpow :
      ((10 ^ length : Nat) : Real) ^
          (1 - sectionSixThetaOne epsilon) <
        ((10 ^ length : Nat) : Real) := by
    calc
      _ < ((10 ^ length : Nat) : Real) ^ (1 : Real) :=
        Real.rpow_lt_rpow_of_exponent_lt hX (by linarith)
      _ = ((10 ^ length : Nat) : Real) := Real.rpow_one _
  have hiProduct : p i ≤ primeTupleProduct p :=
    Finset.single_le_prod' (fun j hj => (hprime j).one_le)
      (Finset.mem_univ i)
  have hiReal : (p i : Real) < ((10 ^ length : Nat) : Real) :=
    (by exact_mod_cast hiProduct : (p i : Real) ≤
      (primeTupleProduct p : Real)) |>.trans_lt (hproduct.trans_lt hpow)
  have hiX : p i < 10 ^ length := by
    exact_mod_cast hiReal
  exact ⟨hiX.le, hprime i⟩

theorem emptyTuple_mem_propositionSixOnePrimeTuples
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    {length : Nat} (hlength : 1 ≤ length) :
    (fun i : Fin 0 => Fin.elim0 i) ∈
      propositionSixOnePrimeTuples epsilon 0 Set.univ length := by
  rw [mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength]
  dsimp [IsPropositionSixOnePrimeTuple]
  refine ⟨?_, ?_, ?_, ?_, Set.mem_univ _⟩
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · have hproduct :
        primeTupleProduct (fun i : Fin 0 => Fin.elim0 i) = 1 := by
      simp [primeTupleProduct]
    rw [hproduct, Nat.cast_one]
    exact Real.one_le_rpow
      (by exact_mod_cast Nat.one_le_pow length 10 (by norm_num))
      (sectionSix_parameter_bounds hepsilon hepsilonSmall).2.2.2.1.le

theorem propositionSixOnePrimeTuples_zero_univ
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    {length : Nat} (hlength : 1 ≤ length) :
    propositionSixOnePrimeTuples epsilon 0 Set.univ length =
      {fun i : Fin 0 => Fin.elim0 i} := by
  classical
  ext p
  constructor
  · intro hp
    simp only [Finset.mem_singleton]
    exact Subsingleton.elim _ _
  · intro hp
    have hpEq : p = fun i : Fin 0 => Fin.elim0 i := by
      simpa only [Finset.mem_singleton] using hp
    subst p
    exact emptyTuple_mem_propositionSixOnePrimeTuples
      hepsilon hepsilonSmall hlength

/-- The exact signed outer sum in Proposition 6.1 at one decimal length. -/
noncomputable def propositionSixOneSum
    (epsilon : Real) (ell : Nat) (region : Set (Fin ell → Real))
    (digit : Fin 10) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  ∑ p ∈ propositionSixOnePrimeTuples epsilon ell region length,
    sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
      (X ^ sectionSixThetaGap epsilon)

theorem propositionSixOneSum_zero_univ
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 ≤ length) :
    propositionSixOneSum epsilon 0 Set.univ digit length =
      sectionSixSiftedSum digit length 1
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) := by
  unfold propositionSixOneSum
  rw [propositionSixOnePrimeTuples_zero_univ
    hepsilon hepsilonSmall hlength]
  simp [primeTupleProduct]
  rfl

/-- Direct eventual-absolute-value expansion of the source's `o_L` claim. -/
def propositionSixOneAsymptotic
    (epsilon : Real) (ell : Nat)
    (region : Set (Fin ell → Real)) : Prop :=
  ∀ rho : Real, 0 < rho →
    ∃ length0 : Nat, 1 ≤ length0 ∧
      ∀ length : Nat, length0 ≤ length →
        ∀ digit : Fin 10,
          |propositionSixOneSum epsilon ell region digit length| ≤
            rho * ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log ((10 ^ length : Nat) : Real)

end

end PrimesRestrictedDigits
