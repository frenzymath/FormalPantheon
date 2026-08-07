import BoundedGaps.BombieriVinogradov.StandardStatement
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Int.Basic

/-!
# Standard endpoint and residue bridge

This file records the one-way restriction from Vaughan's real endpoint and
integer residue classes to the natural publication surface. The source
endpoint maximum is over `0 < X <= Y` and integer classes coprime to the
modulus; the publication maximum is over `2 <= y <= x` and canonical natural
representatives. See `Vaughan1980`, equation (9), pp. 113--115.
-/

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace BoundedGaps.BombieriVinogradov

/-- The source von Mangoldt sum through the natural floor of a real endpoint. -/
noncomputable def realChebyshevProgressionSum
    (X : Real) (q : Nat) (a : Int) : Real :=
  ∑ n ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun n : Nat =>
    (n : Int) % (q : Int) = a % (q : Int)),
    ArithmeticFunction.vonMangoldt n

/-- The source discrepancy, centered at `X / phi(q)`. -/
noncomputable def realWeightedProgressionDiscrepancy
    (X : Real) (q : Nat) (a : Int) : Real :=
  |realChebyshevProgressionSum X q a -
    X / (Nat.totient q : Real)|

theorem intNatMod_mem_reducedResidues {q : Nat} (hq : 0 < q)
    (a : Int) (ha : Nat.Coprime a.natAbs q) :
    a.natMod q ∈ reducedResidues q := by
  rw [reducedResidues, Finset.mem_filter]
  refine ⟨Finset.mem_range.mpr (Int.natMod_lt (Nat.ne_of_gt hq)), ?_⟩
  apply Nat.coprime_iff_gcd_eq_one.mpr
  have hqz : (q : Int) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hnonneg : 0 ≤ a % (q : Int) := Int.emod_nonneg _ hqz
  have hnatAbs : (a % (q : Int)).natAbs = a.natMod q := by
    change (a % (q : Int)).natAbs = (a % (q : Int)).toNat
    apply Int.ofNat_inj.mp
    rw [Int.natAbs_of_nonneg hnonneg, Int.toNat_of_nonneg hnonneg]
  calc
    Nat.gcd (a.natMod q) q = Int.gcd (a % (q : Int)) (q : Int) := by
      rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, hnatAbs]
    _ = Int.gcd a (q : Int) := Int.gcd_emod _ _
    _ = Nat.gcd a.natAbs q := by
      rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    _ = 1 := Nat.coprime_iff_gcd_eq_one.mp ha

theorem intGcd_eq_one_iff_natCoprime {q : Nat} (a : Int) :
    Int.gcd a (q : Int) = 1 <-> Nat.Coprime a.natAbs q := by
  rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, Nat.coprime_iff_gcd_eq_one]

theorem intModEq_iff_natModEq {n q : Nat} (a : Int) (hq : 0 < q) :
    (n : Int) % (q : Int) = a % (q : Int) <->
      n % q = a.natMod q := by
  have hqz : (q : Int) ≠ 0 := by exact_mod_cast hq.ne'
  have ha_nonneg : 0 ≤ a % (q : Int) := Int.emod_nonneg _ hqz
  have ha_cast : (a.natMod q : Int) = a % (q : Int) := by
    change ((a % (q : Int)).toNat : Int) = a % (q : Int)
    exact Int.toNat_of_nonneg ha_nonneg
  constructor
  · intro h
    apply Int.ofNat_inj.mp
    rw [Int.natCast_emod]
    rw [ha_cast]
    exact h
  · intro h
    rw [← Int.natCast_emod, ← ha_cast]
    exact_mod_cast h

theorem realChebyshevProgressionSum_natCast
    (x q : Nat) (a : Int) (hq : 0 < q) :
    realChebyshevProgressionSum (x : Real) q a =
      chebyshevProgressionSum x q (a.natMod q) := by
  rw [realChebyshevProgressionSum, chebyshevProgressionSum,
    Nat.floor_natCast]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  rw [intModEq_iff_natModEq a hq]
  rw [Nat.mod_eq_of_lt (Int.natMod_lt (Nat.ne_of_gt hq))]

theorem realWeightedProgressionDiscrepancy_natCast
    (x q : Nat) (a : Int) (hq : 0 < q) :
    realWeightedProgressionDiscrepancy (x : Real) q a =
      weightedProgressionDiscrepancy x q (a.natMod q) := by
  rw [realWeightedProgressionDiscrepancy,
    weightedProgressionDiscrepancy,
    realChebyshevProgressionSum_natCast x q a hq]

theorem natCast_mem_sourceEndpointRange {x y : Nat}
    (hy : 2 <= y) (hyx : y <= x) :
    (0 : Real) < (y : Real) ∧ (y : Real) <= (x : Real) := by
  exact ⟨by exact_mod_cast (lt_of_lt_of_le (by norm_num) hy),
    by exact_mod_cast hyx⟩

theorem natCast_mem_sourceModulusRange {Q q : Nat}
    (hq : 1 <= q) (hqQ : q <= Q) :
    (0 : Real) < (q : Real) ∧ (q : Real) <= (Q : Real) := by
  exact ⟨by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq),
    by exact_mod_cast hqQ⟩

theorem maxWeightedProgressionDiscrepancyUpTo_le_of_realMajorant
    {x q : Nat} (hx : 2 <= x) (hq : 0 < q) {E : Real}
    (hE : ∀ X : Real, 0 < X → X <= (x : Real) →
      ∀ a : Int, Nat.Coprime a.natAbs q →
        realWeightedProgressionDiscrepancy X q a <= E) :
    maxWeightedProgressionDiscrepancyUpTo x q <= E := by
  rw [maxWeightedProgressionDiscrepancyUpTo, dif_pos hx, dif_pos hq]
  apply Finset.sup'_le (reducedResidues_nonempty hq)
  intro a ha
  have ha_lt : a < q := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have ha_natMod : (a : Int).natMod q = a := by
    change ((a : Int) % (q : Int)).toNat = a
    rw [← Int.natCast_emod, Nat.mod_eq_of_lt ha_lt]
    simp
  apply Finset.sup'_le (endpointRange_nonempty hx)
  intro y hy
  rw [← ha_natMod, ← realWeightedProgressionDiscrepancy_natCast y q (a : Int) hq]
  apply hE (y : Real)
  · exact (natCast_mem_sourceEndpointRange (Finset.mem_Icc.mp hy).1
      (Finset.mem_Icc.mp hy).2).1
  · exact (natCast_mem_sourceEndpointRange (Finset.mem_Icc.mp hy).1
      (Finset.mem_Icc.mp hy).2).2
  · simpa using (Finset.mem_filter.mp ha).2

theorem sum_maxWeightedProgressionDiscrepancyUpTo_le_of_realMajorant
    {x Q : Nat} (hx : 2 <= x) (hQ : 1 <= Q) (E : Nat → Real)
    (hE : ∀ q ∈ Finset.Icc 1 Q,
      ∀ X : Real, 0 < X → X <= (x : Real) →
      ∀ a : Int, Nat.Coprime a.natAbs q →
        realWeightedProgressionDiscrepancy X q a <= E q) :
    (∑ q ∈ Finset.Icc 1 Q,
      maxWeightedProgressionDiscrepancyUpTo x q) <=
      ∑ q ∈ Finset.Icc 1 Q, E q := by
  have _hQpos : 0 < Q := lt_of_lt_of_le Nat.zero_lt_one hQ
  apply Finset.sum_le_sum
  intro q hq
  apply maxWeightedProgressionDiscrepancyUpTo_le_of_realMajorant hx
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hq).1)
  exact hE q hq

theorem sum_maxWeightedProgressionDiscrepancyUpTo_le_of_realMajorant_bound
    {x Q : Nat} (hx : 2 <= x) (hQ : 1 <= Q)
    (E : Nat → Real) {R : Real}
    (hE : ∀ q ∈ Finset.Icc 1 Q,
      ∀ X : Real, 0 < X → X <= (x : Real) →
      ∀ a : Int, Int.gcd a (q : Int) = 1 →
        realWeightedProgressionDiscrepancy X q a <= E q)
    (hER : (∑ q ∈ Finset.Icc 1 Q, E q) <= R) :
    (∑ q ∈ Finset.Icc 1 Q,
      maxWeightedProgressionDiscrepancyUpTo x q) <= R := by
  apply le_trans
    (sum_maxWeightedProgressionDiscrepancyUpTo_le_of_realMajorant hx hQ E ?_)
    hER
  intro q hq X hX0 hXx a ha
  apply hE q hq X hX0 hXx a
  exact (intGcd_eq_one_iff_natCoprime a).mpr ha

end BoundedGaps.BombieriVinogradov
