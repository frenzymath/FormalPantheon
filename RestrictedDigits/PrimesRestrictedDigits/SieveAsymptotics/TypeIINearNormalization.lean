import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineSlabCount

/-!
# Near-product scalar and affine normalization bridges

This file contains the scalar portion of the strict Type II near-region transfer. The cap and
residual-one lemmas are independent of the labelled factorization module; the affine lemma is
the exact change from `log X` to `log N` on the strict near carrier.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A complete cap and a strict lower bound on its continuation factor give
the source outer cap.  No positivity assumption on `D` is needed: a
contradictory lower bound would itself force `D` to be positive. -/
theorem typeIIOuterFactor_lt_rpow_one_sub
    {X D q : Nat} {eta : Real}
    (hX : 1 < X)
    (hDq : ((D * q : Nat) : Real) < X)
    (hq : (X : Real) ^ eta < (q : Real)) :
    (D : Real) < (X : Real) ^ (1 - eta) := by
  have hXpos : (0 : Real) < (X : Real) := by
    exact_mod_cast (Nat.zero_lt_of_lt hX)
  have hXeta : 0 < (X : Real) ^ eta :=
    Real.rpow_pos_of_pos hXpos _
  have hDq' : (D : Real) * (q : Real) < (X : Real) := by
    exact_mod_cast hDq
  have hpowSub : (X : Real) ^ (1 - eta) * (X : Real) ^ eta =
      (X : Real) := by
    rw [← Real.rpow_add hXpos]
    norm_num
  by_contra hnot
  have hDge : (X : Real) ^ (1 - eta) ≤ (D : Real) :=
    le_of_not_gt hnot
  have hDpos : 0 < (D : Real) :=
    (Real.rpow_pos_of_pos hXpos _).trans_le hDge
  have hmid : (D : Real) * (X : Real) ^ eta <
      (D : Real) * (q : Real) :=
    mul_lt_mul_of_pos_left hq hDpos
  have hprod : (X : Real) ^ (1 - eta) * (X : Real) ^ eta <
      (D : Real) * (q : Real) :=
    (mul_le_mul_of_nonneg_right hDge hXeta.le).trans_lt hmid
  rw [hpowSub] at hprod
  exact (not_lt_of_ge hDq'.le) hprod

/-- The strict near lower endpoint excludes an empty residual factor list
once the outer factor has the source cap. -/
theorem typeIINearResidual_ne_one
    {X D m N : Nat} {eta deltaNear : Real}
    (hX : 1 < X) (hdeltaSq : deltaNear ^ 2 < eta)
    (hnear : (X : Real) ^ (1 - deltaNear ^ 2) < (N : Real))
    (hfactor : D * m = N)
    (hcap : (D : Real) < (X : Real) ^ (1 - eta)) :
    m ≠ 1 := by
  intro hm
  subst m
  have hN_eq : N = D := by
    simpa using hfactor.symm
  subst N
  have hnearD : (X : Real) ^ (1 - deltaNear ^ 2) < (D : Real) := by
    simpa using hnear
  have hpowOrder : (1 - eta : Real) < 1 - deltaNear ^ 2 := by
    linarith
  have hpow : (X : Real) ^ (1 - eta) <
      (X : Real) ^ (1 - deltaNear ^ 2) :=
    Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hX) hpowOrder
  linarith

/-- Exact affine-value error when changing the logarithmic base from `X` to
the represented near integer `N`.  The square width is inherited from the
strict near carrier, and no sign or nonzero assumption is imposed on the
normal. -/
theorem abs_typeIIAffineValue_normalizedPrimeLog_sub_le
    {X N r : Nat} {deltaNear : Real}
    {normal : Fin r → Real} {p : Fin r → Nat}
    (hX : 1 < X) (hN : 1 < N)
    (hnear : (X : Real) ^ (1 - deltaNear ^ 2) < (N : Real))
    (hNX : N < X) (hp : ∀ i, (p i).Prime)
    (hproduct : primeTupleProduct p = N) :
    |typeIIAffineValue normal
          (fun i => normalizedPrimeLog N (p i)) -
        typeIIAffineValue normal
          (fun i => normalizedPrimeLog X (p i))| ≤
      deltaNear ^ 2 * typeIIAffineNormalMass normal := by
  have hnearBounds := normalizedPrimeLog_near_bounds hX hnear hNX
  have hcoords := normalizedPrimeLog_product_coordinates hN hp hproduct
  have hbase (i : Fin r) := normalizedPrimeLog_base_change hX hN (p := p i)
  have hcoordDiff (i : Fin r) :
      |normalizedPrimeLog N (p i) - normalizedPrimeLog X (p i)| ≤
        deltaNear ^ 2 := by
    have hi := hcoords.2 i
    have hdiff : normalizedPrimeLog N (p i) -
        normalizedPrimeLog X (p i) =
        (1 - normalizedPrimeLog X N) *
          normalizedPrimeLog N (p i) := by
      rw [hbase i]
      ring
    rw [hdiff, abs_of_nonneg]
    · have hscaleErr : 0 ≤ 1 - normalizedPrimeLog X N := by
        linarith [hnearBounds.2]
      have hscaleErrUpper : 1 - normalizedPrimeLog X N ≤
          deltaNear ^ 2 := by
        linarith [hnearBounds.1]
      have hmulOne : (1 - normalizedPrimeLog X N) *
          normalizedPrimeLog N (p i) ≤
          1 - normalizedPrimeLog X N := by
        nlinarith [hi.2, hscaleErr]
      have hmulUpper := mul_le_mul_of_nonneg_right hscaleErrUpper hi.1.le
      linarith
    · exact mul_nonneg (by linarith [hnearBounds.2]) hi.1.le
  rw [typeIIAffineValue, typeIIAffineValue]
  calc
    |∑ i, normal i * normalizedPrimeLog N (p i) -
        ∑ i, normal i * normalizedPrimeLog X (p i)| =
      |∑ i, normal i *
          (normalizedPrimeLog N (p i) -
            normalizedPrimeLog X (p i))| := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i, |normal i *
          (normalizedPrimeLog N (p i) -
            normalizedPrimeLog X (p i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |normal i| *
          |normalizedPrimeLog N (p i) -
            normalizedPrimeLog X (p i)| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul]
    _ ≤ ∑ i, |normal i| * deltaNear ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hcoordDiff i) (abs_nonneg _)
    _ = deltaNear ^ 2 * typeIIAffineNormalMass normal := by
      rw [typeIIAffineNormalMass, ← Finset.sum_mul]
      ring

/-- Changing from a near target's logarithmic base to the ambient base costs
one square-width error on every coordinate subset, not one error per
coordinate. -/
theorem abs_sum_normalizedPrimeLog_sub_sum_normalizedPrimeLog_le_sq_of_near
    {X N r : Nat} {rho : Real} {p : Fin r -> Nat}
    (hX : 1 < X) (hN : 1 < N)
    (hnear : (X : Real) ^ (1 - rho ^ 2) < (N : Real))
    (hNX : N < X)
    (hprime : ∀ i, (p i).Prime)
    (hproduct : primeTupleProduct p = N)
    (I : Finset (Fin r)) :
    |(∑ i ∈ I, normalizedPrimeLog N (p i)) -
        ∑ i ∈ I, normalizedPrimeLog X (p i)| <= rho ^ 2 := by
  have hnearBounds := normalizedPrimeLog_near_bounds hX hnear hNX
  have hcoords := normalizedPrimeLog_product_coordinates hN hprime hproduct
  have hbase (i : Fin r) := normalizedPrimeLog_base_change hX hN (p := p i)
  have hsumNonnegative :
      0 <= ∑ i ∈ I, normalizedPrimeLog N (p i) := by
    exact Finset.sum_nonneg fun i _ => (hcoords.2 i).1.le
  have hsumUpper :
      (∑ i ∈ I, normalizedPrimeLog N (p i)) <= 1 := by
    calc
      (∑ i ∈ I, normalizedPrimeLog N (p i)) <=
          ∑ i, normalizedPrimeLog N (p i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
        intro i _ _
        exact (hcoords.2 i).1.le
      _ = 1 := hcoords.1
  have hdiff :
      (∑ i ∈ I, normalizedPrimeLog N (p i)) -
          ∑ i ∈ I, normalizedPrimeLog X (p i) =
        (1 - normalizedPrimeLog X N) *
          ∑ i ∈ I, normalizedPrimeLog N (p i) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hbase i]
    ring
  rw [hdiff, abs_of_nonneg]
  · nlinarith [sq_nonneg rho]
  · exact mul_nonneg (by linarith [hnearBounds.2]) hsumNonnegative

end

end PrimesRestrictedDigits
