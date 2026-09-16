import PrimesRestrictedDigits.SieveAsymptotics.SectionSixOuterRangePartition
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport
import Mathlib.Data.Fintype.Pi

/-!
# Proposition 6.2 statement

This file defines the strict Type II outer carrier and eventual two-band statement used by
Maynard's Proposition 6.2. The second printed display's selected product is corrected from
repeated `p_j` to `product_(i in I) p_i`.

Source: `MAYNARD-PRD-PUBLISHED`, Proposition 6.2 and Lemma 7.3, pp. 137--138 and 149--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The product of the displayed prime coordinates selected by `I`. -/
def primeTupleSubproduct {ell : Nat}
    (p : Fin ell -> Nat) (I : Finset (Fin ell)) : Nat :=
  I.prod p

@[simp] theorem primeTupleSubproduct_empty {ell : Nat}
    (p : Fin ell -> Nat) :
    primeTupleSubproduct p ∅ = 1 := by
  simp [primeTupleSubproduct]

@[simp] theorem primeTupleSubproduct_univ {ell : Nat}
    (p : Fin ell -> Nat) :
    primeTupleSubproduct p Finset.univ = primeTupleProduct p := by
  rfl

/-- A distinguished coordinate witnesses the printed positive-arity premise. -/
theorem propositionSixTwo_arity_pos {ell : Nat} (j : Fin ell) :
    1 <= ell := by
  exact Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt j.isLt)

/-- The weak integral source cap is exactly the printed weak real cap. -/
theorem propositionSixTwo_nat_cap_iff_real
    {d q X : Nat} (hq : 0 < q) :
    d * q <= X <-> (d : Real) <= (X : Real) / (q : Real) := by
  rw [le_div_iff₀ (by exact_mod_cast hq), ← Nat.cast_mul, Nat.cast_le]

/-- Tuple specialization of the exact source-cap bridge. -/
theorem propositionSixTwo_product_cap_iff_real
    {ell X : Nat} {p : Fin ell -> Nat} (j : Fin ell)
    (hprime : forall i, (p i).Prime) :
    primeTupleProduct p * p j <= X <->
      (primeTupleProduct p : Real) <= (X : Real) / (p j : Real) :=
  propositionSixTwo_nat_cap_iff_real (hprime j).pos

/-- On a nonempty monotone tuple, the source lower bound on the first prime is
equivalent to the coordinatewise form used by the finite carrier. -/
theorem propositionSixTwo_forall_lower_iff_first_lower
    {X : Real} {eta : Real} {ell : Nat} (j : Fin ell)
    {p : Fin ell -> Nat} (hmono : Monotone p) :
    (forall i, X ^ eta <= (p i : Real)) <->
      X ^ eta <= (p ⟨0, Nat.zero_lt_of_lt j.isLt⟩ : Real) := by
  constructor
  · intro h
    exact h _
  · intro h i
    have hindex : (⟨0, Nat.zero_lt_of_lt j.isLt⟩ : Fin ell) <= i := by
      apply Fin.mk_le_mk.mpr
      exact Nat.zero_le _
    exact h.trans (by exact_mod_cast hmono hindex)

/-- The exact source predicate for one strict Proposition 6.2 outer tuple. -/
def IsPropositionSixTwoPrimeTuple
    (epsilon : Real) (length : Nat) {ell : Nat}
    (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real))
    (band : SectionSixDirectBand) (p : Fin ell -> Nat) : Prop :=
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  (forall i, (p i).Prime) ∧
    Monotone p ∧
    (forall i, X ^ sectionSixThetaGap epsilon <= (p i : Real)) ∧
    sectionSixDirectRangeMembership band X
      (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
      (primeTupleSubproduct p I : Real) ∧
    primeTupleProduct p * p j <= XNat ∧
    (fun i => normalizedPrimeLog XNat (p i)) ∈ region

/-- Finite realization of the strict Proposition 6.2 outer carrier. -/
noncomputable def propositionSixTwoPrimeTuples
    (epsilon : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) : Finset (Fin ell -> Nat) := by
  classical
  exact (Fintype.piFinset fun _ : Fin ell =>
    Nat.primesLE (10 ^ length)).filter
      (IsPropositionSixTwoPrimeTuple epsilon length I j region band)

@[simp] theorem mem_propositionSixTwoPrimeTuples
    {epsilon : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {p : Fin ell -> Nat} :
    p ∈ propositionSixTwoPrimeTuples epsilon ell I j region length band <->
      (forall i, p i ∈ Nat.primesLE (10 ^ length)) ∧
        IsPropositionSixTwoPrimeTuple epsilon length I j region band p := by
  classical
  simp [propositionSixTwoPrimeTuples, Fintype.mem_piFinset]

/-- The finite enumeration cutoff adds no condition to the source predicate. -/
theorem mem_propositionSixTwoPrimeTuples_iff_source
    {epsilon : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {p : Fin ell -> Nat} :
    p ∈ propositionSixTwoPrimeTuples epsilon ell I j region length band <->
      IsPropositionSixTwoPrimeTuple epsilon length I j region band p := by
  rw [mem_propositionSixTwoPrimeTuples]
  refine and_iff_right_of_imp ?_
  intro hpData i
  dsimp [IsPropositionSixTwoPrimeTuple] at hpData
  have hprime : forall k, (p k).Prime := hpData.1
  have hcoordinate : p i <= primeTupleProduct p :=
    primeTupleCoordinate_le_product (fun k => (hprime k).one_le) i
  have hproductCap : primeTupleProduct p <= primeTupleProduct p * p j :=
    Nat.le_mul_of_pos_right _ (hprime j).one_le
  rw [Nat.mem_primesLE]
  exact ⟨hcoordinate.trans (hproductCap.trans hpData.2.2.2.2.1), hprime i⟩

/-- Every accepted full displayed product is positive. -/
theorem primeTupleProduct_pos_of_mem_propositionSixTwoPrimeTuples
    {epsilon : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {p : Fin ell -> Nat}
    (hp : p ∈ propositionSixTwoPrimeTuples
      epsilon ell I j region length band) :
    0 < primeTupleProduct p := by
  have hpData :=
    (mem_propositionSixTwoPrimeTuples_iff_source.mp hp)
  dsimp [IsPropositionSixTwoPrimeTuple] at hpData
  exact primeTupleProduct_pos fun i => (hpData.1 i).ne_zero

/-- `toPNat'` preserves every accepted displayed product exactly. -/
theorem coe_toPNat'_primeTupleProduct_of_mem_propositionSixTwoPrimeTuples
    {epsilon : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {p : Fin ell -> Nat}
    (hp : p ∈ propositionSixTwoPrimeTuples
      epsilon ell I j region length band) :
    ((primeTupleProduct p).toPNat' : Nat) = primeTupleProduct p := by
  rw [Nat.toPNat'_coe,
    if_pos (primeTupleProduct_pos_of_mem_propositionSixTwoPrimeTuples hp)]

/-- The exact signed strict Type II sum at one decimal length and band. -/
noncomputable def propositionSixTwoBandSum
    (epsilon : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (digit : Fin 10) (length : Nat)
    (band : SectionSixDirectBand) : Real :=
  ∑ p ∈ propositionSixTwoPrimeTuples epsilon ell I j region length band,
    sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
      (p j : Real)

/-- Direct eventual-absolute-value expansion of both source little-o claims,
with one threshold chosen before the excluded digit and band. -/
def propositionSixTwoAsymptotic
    (epsilon : Real) {ell : Nat} (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) : Prop :=
  forall rho : Real, 0 < rho ->
    exists length0 : Nat, 1 <= length0 ∧
      forall length : Nat, length0 <= length ->
        forall digit : Fin 10,
          forall band : SectionSixDirectBand,
            abs (propositionSixTwoBandSum epsilon ell I j region digit length
              band) <=
              rho * ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log ((10 ^ length : Nat) : Real)

end

end PrimesRestrictedDigits
