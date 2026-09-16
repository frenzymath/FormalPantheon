import PrimesRestrictedDigits.MajorArcs.Factorization
import PrimesRestrictedDigits.MajorArcs.ResiduePhaseSum
import Mathlib.Data.ZMod.Basic

/-!
# Exact product-residue convolution for M3

This supplies the finite carrier algebra behind the M3 calculation on
`MAYNARD-PRD-PUBLISHED`, pp. 186--189. Both last-prime lower bounds and the
strict product cutoff are retained.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The canonical last-prime residue obtained by inverting a supported prefix
modulo `q`. -/
def majorArcPrefixInverseResidue (q m r : Nat) : Nat :=
  (((m : ZMod q)⁻¹ * (r : ZMod q)) : ZMod q).val

/-- The maximum of the two weak lower bounds on the last prime in Eq. (11.2). -/
noncomputable def majorArcLastPrimeLowerCutoff
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta eta : Real) : Real :=
  max ((X : Real) ^ (eta / 4))
    ((X : Real) ^
      (1 - (∑ i, a i) - ((k + 1 : Nat) : Real) * delta))

/-- The last-prime log sum whose product lies in one residue class. -/
noncomputable def majorArcLastPrimeProductResidueLogSum
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta eta : Real)
    (m q r : Nat) : Real :=
  ∑ p ∈ majorArcLastPrimes X a delta eta with
      m * p < X ∧ m * p ≡ r [MOD q],
    Real.log (p : Real)

/-- The actual total region weight on the strict carrier `n < X`. -/
noncomputable def majorArcRegionTotalWeight
    (X : Nat) {k : Nat} (a : Fin k -> Real)
    (delta eta : Real) : Complex :=
  ∑ n ∈ Finset.range X,
    (majorArcRegionWeightAtProduct X a delta eta n : Complex)

/-- Multiplication by a unit prefix transports a product residue to the
canonical inverse residue. -/
theorem mul_modEq_iff_modEq_prefixInverseResidue
    {q m p r : Nat} (hq : 0 < q) (hm : Nat.Coprime m q) :
    m * p ≡ r [MOD q] <->
      p ≡ majorArcPrefixInverseResidue q m r [MOD q] := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hmUnit : IsUnit (m : ZMod q) :=
    (ZMod.isUnit_iff_coprime m q).2 hm
  constructor
  · intro h
    rw [← ZMod.natCast_eq_natCast_iff] at h ⊢
    push_cast at h
    rw [majorArcPrefixInverseResidue, ZMod.natCast_zmod_val]
    calc
      (p : ZMod q) =
          (m : ZMod q)⁻¹ * ((m : ZMod q) * (p : ZMod q)) := by
        rw [← mul_assoc, ZMod.inv_mul_of_unit _ hmUnit, one_mul]
      _ = (m : ZMod q)⁻¹ * (r : ZMod q) := by rw [h]
  · intro h
    rw [← ZMod.natCast_eq_natCast_iff] at h ⊢
    push_cast at h ⊢
    rw [majorArcPrefixInverseResidue, ZMod.natCast_zmod_val] at h
    calc
      (m : ZMod q) * (p : ZMod q) =
          (m : ZMod q) * ((m : ZMod q)⁻¹ * (r : ZMod q)) := by rw [h]
      _ = (r : ZMod q) := by
        rw [← mul_assoc, ZMod.mul_inv_of_unit _ hmUnit, one_mul]

/-- The inverse residue of two units is again coprime to the modulus. -/
theorem prefixInverseResidue_coprime
    {q m r : Nat} (_hq : 0 < q)
    (hm : Nat.Coprime m q) (hr : Nat.Coprime r q) :
    Nat.Coprime (majorArcPrefixInverseResidue q m r) q := by
  letI : NeZero q := ⟨_hq.ne'⟩
  let um := ZMod.unitOfCoprime m hm
  let ur := ZMod.unitOfCoprime r hr
  let u : (ZMod q)ˣ := um⁻¹ * ur
  have hu := ZMod.val_coe_unit_coprime u
  have hcoe : (u : ZMod q) =
      (m : ZMod q)⁻¹ * (r : ZMod q) := by
    dsimp [u, um, ur]
    rw [← ZMod.inv_coe_unit (ZMod.unitOfCoprime m hm),
      ZMod.coe_unitOfCoprime]
  have hval := congrArg ZMod.val hcoe
  simpa only [majorArcPrefixInverseResidue, ← hval] using hu

/-- A nonzero projected prefix is coprime to every divisor of the ambient
power of ten once all coordinate primes exceed five. -/
theorem projectedPrimeBoxWeightAtProduct_coprime_of_dvd_powerTen
    {X K q k m : Nat} {a : Fin k -> Real} {delta eta : Real}
    (hX : 1 < X) (heta : 0 < eta) (ha : ∀ i, eta / 2 <= a i)
    (hlarge : 5 < (X : Real) ^ (eta / 4))
    (hpower : X = 10 ^ K) (hq : q ∣ X)
    (hweight : projectedPrimeBoxWeightAtProduct X a delta m ≠ 0) :
    Nat.Coprime m q := by
  have hfiber :
      ((projectedPrimeBoxTuples X a delta).filter
        (fun p => primeTupleProduct p = m)).Nonempty := by
    by_contra hempty
    have heq :
        (projectedPrimeBoxTuples X a delta).filter
            (fun p => primeTupleProduct p = m) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    apply hweight
    unfold projectedPrimeBoxWeightAtProduct primeTupleWeightAtProduct
    rw [heq, Finset.sum_empty]
  rcases hfiber with ⟨p, hp⟩
  rcases Finset.mem_filter.mp hp with ⟨hpTuple, hproduct⟩
  have primeCoprime {r : Nat} (hr : r.Prime) (hrlarge : 5 < r) :
      Nat.Coprime r q := by
    rw [hr.coprime_iff_not_dvd]
    intro hrq
    have hrpow : r ∣ 10 ^ K := hrq.trans (by simpa [hpower] using hq)
    have hrten : r ∣ 10 := hr.dvd_of_dvd_pow hrpow
    have hrprod : r ∣ 2 * 5 := by
      norm_num at hrten ⊢
      exact hrten
    rcases hr.dvd_mul.mp hrprod with hr2 | hr5
    · have := Nat.le_of_dvd (by norm_num : 0 < 2) hr2
      omega
    · have := Nat.le_of_dvd (by norm_num : 0 < 5) hr5
      omega
  rw [← hproduct, primeTupleProduct,
    Nat.coprime_fintype_prod_left_iff]
  intro i
  let r := p i
  have hrPrime : r.Prime :=
    prime_of_mem_projectedPrimeBoxTuples hpTuple i
  have hbox : normalizedPrimeLog X r ∈ Set.Ioc (a i) (a i + delta) :=
    (mem_projectedPrimeBoxTuples_iff.mp hpTuple).2 i
  have hexponent : eta / 4 <= a i := by linarith [ha i, heta]
  have hlower : (X : Real) ^ (a i) < (r : Real) :=
    (normalizedPrimeLog_mem_Ioc_iff_rpow hX hrPrime _ _).mp hbox |>.1
  have hXone : (1 : Real) <= X := by exact_mod_cast hX.le
  have hscale : (X : Real) ^ (eta / 4) <= (X : Real) ^ (a i) :=
    Real.rpow_le_rpow_of_exponent_le hXone hexponent
  apply primeCoprime hrPrime
  exact_mod_cast hlarge.trans (hscale.trans_lt hlower)

private theorem sum_majorArcRegionWeight_mul_eq_projected
    {X k : Nat} (a : Fin k -> Real) (delta eta : Real)
    (e : Nat -> Complex) (hX : 1 < X) :
    (∑ n ∈ Finset.range X,
      (majorArcRegionWeightAtProduct X a delta eta n : Complex) * e n) =
      ∑ m ∈ Finset.Ico 1 X,
        (projectedPrimeBoxWeightAtProduct X a delta m : Complex) *
          ∑ p ∈ majorArcLastPrimes X a delta eta with m * p < X,
            (Real.log (p : Real) : Complex) * e (m * p) := by
  let W := fun m => projectedPrimeBoxWeightAtProduct X a delta m
  let L := majorArcLastPrimes X a delta eta
  have hfactor (n : Nat) (hn : n < X) :
      (majorArcRegionWeightAtProduct X a delta eta n : Complex) =
        ∑ m ∈ Finset.range X,
          ∑ p ∈ L with m * p = n,
            (W m : Complex) * (Real.log (p : Real) : Complex) := by
    dsimp [W, L]
    rw [majorArcRegionWeightAtProduct_eq_projected_convolution
      a delta eta hX hn]
    push_cast
    rfl
  have hpositiveSubset : Finset.Ico 1 X ⊆ Finset.range X := by
    intro m hm
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hm).2
  calc
    (∑ n ∈ Finset.range X,
        (majorArcRegionWeightAtProduct X a delta eta n : Complex) * e n) =
        ∑ n ∈ Finset.range X,
          ∑ m ∈ Finset.range X,
            ∑ p ∈ L with m * p = n,
              (W m : Complex) * (Real.log (p : Real) : Complex) * e n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hfactor n (Finset.mem_range.mp hn), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_mul]
    _ = ∑ m ∈ Finset.range X,
        ∑ p ∈ L with m * p < X,
          (W m : Complex) * (Real.log (p : Real) : Complex) * e (m * p) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_range]
    _ = ∑ m ∈ Finset.range X,
        (W m : Complex) *
          ∑ p ∈ L with m * p < X,
            (Real.log (p : Real) : Complex) * e (m * p) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = ∑ m ∈ Finset.Ico 1 X,
        (projectedPrimeBoxWeightAtProduct X a delta m : Complex) *
          ∑ p ∈ majorArcLastPrimes X a delta eta with m * p < X,
            (Real.log (p : Real) : Complex) * e (m * p) := by
      dsimp [W, L]
      symm
      apply Finset.sum_subset hpositiveSubset
      intro m hmRange hmNotPositive
      have hm0 : m = 0 := by
        have hmLt := Finset.mem_range.mp hmRange
        have hmNotOne : ¬1 <= m := by
          intro hmOne
          exact hmNotPositive (Finset.mem_Ico.mpr ⟨hmOne, hmLt⟩)
        omega
      subst m
      rw [projectedPrimeBoxWeightAtProduct_zero]
      norm_num

/-- Summing Eq. (11.2) with a product-residue indicator gives the exact
projected convolution. -/
theorem majorArcRegionResidueWeightSum_eq_projected
    {X k q r : Nat} (a : Fin k -> Real) (delta eta : Real)
    (hX : 1 < X) :
    majorArcResidueWeightSum (Finset.range X)
        (fun n => (majorArcRegionWeightAtProduct X a delta eta n : Complex))
        q r =
      ∑ m ∈ Finset.Ico 1 X,
        (projectedPrimeBoxWeightAtProduct X a delta m : Complex) *
          (majorArcLastPrimeProductResidueLogSum
            X a delta eta m q r : Complex) := by
  let e : Nat -> Complex := fun n => if n ≡ r [MOD q] then 1 else 0
  have hleft :
      majorArcResidueWeightSum (Finset.range X)
          (fun n => (majorArcRegionWeightAtProduct X a delta eta n : Complex))
          q r =
        ∑ n ∈ Finset.range X,
          (majorArcRegionWeightAtProduct X a delta eta n : Complex) * e n := by
    unfold majorArcResidueWeightSum
    simp_rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [e]
    split_ifs <;> simp_all
  rw [hleft, sum_majorArcRegionWeight_mul_eq_projected a delta eta e hX]
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  unfold majorArcLastPrimeProductResidueLogSum
  push_cast
  simp_rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  dsimp [e]
  by_cases hcut : m * p < X
  · by_cases hmod : m * p ≡ r [MOD q]
    · simp [hcut, hmod]
    · simp [hcut, hmod]
  · simp [hcut]

/-- Modulus one and residue zero recover the entire finite carrier. -/
theorem majorArcResidueWeightSum_one_zero
    (s : Finset Nat) (w : Nat -> Complex) :
    majorArcResidueWeightSum s w 1 0 = ∑ n ∈ s, w n := by
  unfold majorArcResidueWeightSum
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hn
      exact ⟨hn, by
        change n % 1 = 0 % 1
        rw [Nat.mod_one, Nat.mod_one]⟩
  · intro n hn
    rfl

end PrimesRestrictedDigits
