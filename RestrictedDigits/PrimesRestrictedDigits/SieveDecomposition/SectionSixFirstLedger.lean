import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstFactorThreshold
import Mathlib.Tactic.Linarith

/-!
# Corrected first Section 6 ledger

This file proves the exact finite identity underlying Maynard's Eq. (6.5). Both omitted
repeated-prime fibers and the signed factor-reduction error remain explicit. No asymptotic
term is discarded here.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 139--140, Eqs. (6.4)--(6.5).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The strict once-dilated outer-prime sum over `(a,b]`. -/
def sectionSixFirstOuterStrictSum
    (digit : Fin 10) (length : Nat) (a b : Real) : Real :=
  ∑ p ∈ sievePrimeInterval a b,
    sectionSixStrictPrimeTerm digit length 1 p

/-- The weak twice-dilated correction over the first outer-prime interval. -/
def sectionSixFirstOuterRepeatedSum
    (digit : Fin 10) (length : Nat) (a b : Real) : Real :=
  ∑ p ∈ sievePrimeInterval a b,
    sectionSixRepeatedPrimeTerm digit length 1 p

/-- The once-dilated outer terms evaluated at a common base threshold. -/
def sectionSixFirstOuterBaseSum
    (digit : Fin 10) (length : Nat) (z a b : Real) : Real :=
  ∑ p ∈ sievePrimeInterval a b,
    sectionSixSiftedSum digit length (Nat.toPNat' p) z

/-- The signed change from `S_p(p)` to `S_p(min(p,sqrt(X/p)))`. -/
def sectionSixFirstFactorError
    (digit : Fin 10) (length : Nat) (a b : Real) : Real :=
  ∑ p ∈ sievePrimeInterval a b,
    (sectionSixSiftedSum digit length (Nat.toPNat' p)
        (sectionSixFirstFactorThreshold length p) -
      sectionSixStrictPrimeTerm digit length 1 p)

/-- The strict two-prime branch after the corrected second recurrence. -/
def sectionSixFirstSecondStrictSum
    (digit : Fin 10) (length : Nat) (z a b : Real) : Real :=
  ∑ p ∈ sievePrimeInterval a b,
    ∑ q ∈ sievePrimeInterval z (sectionSixFirstFactorThreshold length p),
      sectionSixStrictPrimeTerm digit length (Nat.toPNat' p) q

/-- The repeated-inner-prime correction after the second recurrence. -/
def sectionSixFirstSecondRepeatedSum
    (digit : Fin 10) (length : Nat) (z a b : Real) : Real :=
  ∑ p ∈ sievePrimeInterval a b,
    ∑ q ∈ sievePrimeInterval z (sectionSixFirstFactorThreshold length p),
      sectionSixRepeatedPrimeTerm digit length (Nat.toPNat' p) q

/-- The two strict double-prime branches retained in Eq. (6.5). -/
def sectionSixFirstStrictBranches
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z2 : Real := sectionSixZTwo epsilon X
  let z3 : Real := sectionSixZThree epsilon X
  let z4 : Real := sectionSixZFour X
  sectionSixFirstSecondStrictSum digit length z1 z1 z2 +
    sectionSixFirstSecondStrictSum digit length z1 z3 z4

/-- Every signed term not belonging to the two strict Eq. (6.5) branches. -/
def sectionSixFirstLedgerError
    (epsilon : Real) (digit : Fin 10) (length : Nat) : Real :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z2 : Real := sectionSixZTwo epsilon X
  let z3 : Real := sectionSixZThree epsilon X
  let z4 : Real := sectionSixZFour X
  sectionSixSiftedSum digit length 1 z1 -
      sectionSixFirstOuterStrictSum digit length z2 z3 -
      sectionSixFirstOuterBaseSum digit length z1 z1 z2 -
      sectionSixFirstOuterBaseSum digit length z1 z3 z4 +
      sectionSixFirstFactorError digit length z1 z2 +
      sectionSixFirstFactorError digit length z3 z4 -
      sectionSixFirstOuterRepeatedSum digit length z1 z4 +
      sectionSixFirstSecondRepeatedSum digit length z1 z1 z2 +
      sectionSixFirstSecondRepeatedSum digit length z1 z3 z4

private theorem sectionSix_sievePrimeInterval_three_range_union
    {z1 z2 z3 z4 : Real} (h12 : z1 <= z2) (h23 : z2 <= z3)
    (h34 : z3 <= z4) :
    sievePrimeInterval z1 z4 =
      (sievePrimeInterval z1 z2 ∪ sievePrimeInterval z2 z3) ∪
        sievePrimeInterval z3 z4 := by
  classical
  ext p
  simp only [Finset.mem_union, mem_sievePrimeInterval]
  constructor
  · rintro ⟨hp, hp1, hp4⟩
    by_cases hp2 : (p : Real) <= z2
    · exact Or.inl (Or.inl ⟨hp, hp1, hp2⟩)
    by_cases hp3 : (p : Real) <= z3
    · exact Or.inl (Or.inr ⟨hp, lt_of_not_ge hp2, hp3⟩)
    · exact Or.inr ⟨hp, lt_of_not_ge hp3, hp4⟩
  · rintro ((⟨hp, hp1, hp2⟩ | ⟨hp, hp2, hp3⟩) |
      ⟨hp, hp3, hp4⟩)
    · exact ⟨hp, hp1, hp2.trans (h23.trans h34)⟩
    · exact ⟨hp, h12.trans_lt hp2, hp3.trans h34⟩
    · exact ⟨hp, (h12.trans h23).trans_lt hp3, hp4⟩

private theorem sectionSix_sievePrimeInterval_adjacent_disjoint
    (z1 z2 z3 : Real) :
    Disjoint (sievePrimeInterval z1 z2) (sievePrimeInterval z2 z3) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp12 hp23
  exact (not_lt_of_ge (mem_sievePrimeInterval.mp hp12).2.2)
    (mem_sievePrimeInterval.mp hp23).2.1

private theorem sectionSix_sievePrimeInterval_firstTwo_disjoint_third
    (z1 z2 z3 z4 : Real) (h23 : z2 <= z3) :
    Disjoint (sievePrimeInterval z1 z2 ∪ sievePrimeInterval z2 z3)
      (sievePrimeInterval z3 z4) := by
  classical
  rw [Finset.disjoint_union_left]
  constructor
  · rw [Finset.disjoint_left]
    intro p hp12 hp34
    exact (not_lt_of_ge
      ((mem_sievePrimeInterval.mp hp12).2.2.trans h23))
        (mem_sievePrimeInterval.mp hp34).2.1
  · exact sectionSix_sievePrimeInterval_adjacent_disjoint z2 z3 z4

private theorem sectionSix_sum_sievePrimeInterval_three_ranges
    (f : Nat -> Real) {z1 z2 z3 z4 : Real}
    (h12 : z1 <= z2) (h23 : z2 <= z3) (h34 : z3 <= z4) :
    (∑ p ∈ sievePrimeInterval z1 z4, f p) =
      (∑ p ∈ sievePrimeInterval z1 z2, f p) +
        (∑ p ∈ sievePrimeInterval z2 z3, f p) +
          ∑ p ∈ sievePrimeInterval z3 z4, f p := by
  classical
  rw [sectionSix_sievePrimeInterval_three_range_union h12 h23 h34,
    Finset.sum_union
      (sectionSix_sievePrimeInterval_firstTwo_disjoint_third
        z1 z2 z3 z4 h23),
    Finset.sum_union
      (sectionSix_sievePrimeInterval_adjacent_disjoint z1 z2 z3)]

/-- The strict outer-prime sum splits exactly at `z2` and `z3`, with each
boundary assigned to the lower adjacent interval. -/
theorem sectionSixFirstOuterStrictSum_three_ranges
    (digit : Fin 10) (length : Nat) {z1 z2 z3 z4 : Real}
    (h12 : z1 <= z2) (h23 : z2 <= z3) (h34 : z3 <= z4) :
    sectionSixFirstOuterStrictSum digit length z1 z4 =
      sectionSixFirstOuterStrictSum digit length z1 z2 +
        sectionSixFirstOuterStrictSum digit length z2 z3 +
        sectionSixFirstOuterStrictSum digit length z3 z4 := by
  simpa only [sectionSixFirstOuterStrictSum] using
    sectionSix_sum_sievePrimeInterval_three_ranges
      (fun p => sectionSixStrictPrimeTerm digit length 1 p) h12 h23 h34

private theorem sectionSixFirst_sum_variable_upper_recurrence
    (digit : Fin 10) (length : Nat) (P : Finset Nat)
    (upper : Nat -> Real) (z : Real)
    (hupper : ∀ p ∈ P, z <= upper p) :
    (∑ p ∈ P,
      sectionSixSiftedSum digit length (Nat.toPNat' p) (upper p)) =
      (∑ p ∈ P,
        sectionSixSiftedSum digit length (Nat.toPNat' p) z) -
      (∑ p ∈ P,
        ∑ q ∈ sievePrimeInterval z (upper p),
          sectionSixStrictPrimeTerm digit length (Nat.toPNat' p) q) -
      (∑ p ∈ P,
        ∑ q ∈ sievePrimeInterval z (upper p),
          sectionSixRepeatedPrimeTerm digit length (Nat.toPNat' p) q) := by
  classical
  calc
    _ = ∑ p ∈ P,
        (sectionSixSiftedSum digit length (Nat.toPNat' p) z -
          (∑ q ∈ sievePrimeInterval z (upper p),
            sectionSixStrictPrimeTerm digit length (Nat.toPNat' p) q) -
          ∑ q ∈ sievePrimeInterval z (upper p),
            sectionSixRepeatedPrimeTerm digit length
              (Nat.toPNat' p) q) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact sectionSixSiftedSum_eq_sub_strict_sub_repeated
        digit length (Nat.toPNat' p) (hupper p hp)
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]

/-- The exact second-step expansion on any outer interval where the common
base threshold is below every factor threshold. -/
theorem sectionSixFirstOuterStrictSum_eq_base_sub_second_sub_repeated_sub_error
    (digit : Fin 10) (length : Nat) (z a b : Real)
    (hz : ∀ p, p ∈ sievePrimeInterval a b ->
      z <= sectionSixFirstFactorThreshold length p) :
    sectionSixFirstOuterStrictSum digit length a b =
      sectionSixFirstOuterBaseSum digit length z a b -
        sectionSixFirstSecondStrictSum digit length z a b -
        sectionSixFirstSecondRepeatedSum digit length z a b -
        sectionSixFirstFactorError digit length a b := by
  unfold sectionSixFirstOuterStrictSum sectionSixFirstOuterBaseSum
    sectionSixFirstSecondStrictSum sectionSixFirstSecondRepeatedSum
    sectionSixFirstFactorError
  rw [Finset.sum_sub_distrib]
  have hrec := sectionSixFirst_sum_variable_upper_recurrence digit length
    (sievePrimeInterval a b) (sectionSixFirstFactorThreshold length) z hz
  linarith

/-- Exact corrected first ledger through the two strict branches in Eq. (6.5).
Every source little-oh term is retained inside `sectionSixFirstLedgerError`. -/
theorem sectionSixFirstLedger_exact
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    sectionSixSiftedSum digit length 1
        (sectionSixZFour ((10 ^ length : Nat) : Real)) =
      sectionSixFirstStrictBranches epsilon digit length +
        sectionSixFirstLedgerError epsilon digit length := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z2 : Real := sectionSixZTwo epsilon X
  let z3 : Real := sectionSixZThree epsilon X
  let z4 : Real := sectionSixZFour X
  change sectionSixSiftedSum digit length 1 z4 =
    (sectionSixFirstSecondStrictSum digit length z1 z1 z2 +
      sectionSixFirstSecondStrictSum digit length z1 z3 z4) +
    (sectionSixSiftedSum digit length 1 z1 -
      sectionSixFirstOuterStrictSum digit length z2 z3 -
      sectionSixFirstOuterBaseSum digit length z1 z1 z2 -
      sectionSixFirstOuterBaseSum digit length z1 z3 z4 +
      sectionSixFirstFactorError digit length z1 z2 +
      sectionSixFirstFactorError digit length z3 z4 -
      sectionSixFirstOuterRepeatedSum digit length z1 z4 +
      sectionSixFirstSecondRepeatedSum digit length z1 z1 z2 +
      sectionSixFirstSecondRepeatedSum digit length z1 z3 z4)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have horder := sectionSix_cutoffs_strict hepsilon hepsilonSmall hX
  have hrecRaw := sectionSixSiftedSum_eq_sub_strict_sub_repeated
    digit length (1 : PNat)
      (horder.1.trans (horder.2.1.trans horder.2.2.1)).le
  have hrec : sectionSixSiftedSum digit length 1 z4 =
      sectionSixSiftedSum digit length 1 z1 -
        sectionSixFirstOuterStrictSum digit length z1 z4 -
        sectionSixFirstOuterRepeatedSum digit length z1 z4 := by
    simpa only [sectionSixFirstOuterStrictSum,
      sectionSixFirstOuterRepeatedSum] using hrecRaw
  have hpartition := sectionSixFirstOuterStrictSum_three_ranges digit length
    horder.1.le horder.2.1.le horder.2.2.1.le
  have hlowCutoff : ∀ p, p ∈ sievePrimeInterval z1 z2 ->
      z1 <= sectionSixFirstFactorThreshold length p := by
    intro p hp
    apply sectionSixZOne_le_firstFactorThreshold_of_mem hepsilon hlength
    have hpData := mem_sievePrimeInterval.mp hp
    exact mem_sievePrimeInterval.mpr
      ⟨hpData.1, hpData.2.1,
        hpData.2.2.trans (horder.2.1.trans horder.2.2.1).le⟩
  have hhighCutoff : ∀ p, p ∈ sievePrimeInterval z3 z4 ->
      z1 <= sectionSixFirstFactorThreshold length p := by
    intro p hp
    apply sectionSixZOne_le_firstFactorThreshold_of_mem hepsilon hlength
    have hpData := mem_sievePrimeInterval.mp hp
    exact mem_sievePrimeInterval.mpr
      ⟨hpData.1, (horder.1.trans horder.2.1).trans hpData.2.1,
        hpData.2.2⟩
  have hlow :=
    sectionSixFirstOuterStrictSum_eq_base_sub_second_sub_repeated_sub_error
      digit length z1 z1 z2 hlowCutoff
  have hhigh :=
    sectionSixFirstOuterStrictSum_eq_base_sub_second_sub_repeated_sub_error
      digit length z1 z3 z4 hhighCutoff
  rw [hpartition, hlow, hhigh] at hrec
  linarith

end

end PrimesRestrictedDigits
