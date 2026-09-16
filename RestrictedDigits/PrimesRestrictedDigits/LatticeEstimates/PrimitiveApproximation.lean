import PrimesRestrictedDigits.LatticeEstimates.DecimalFactorization
import PrimesRestrictedDigits.LatticeEstimates.SimultaneousApproximation
import Mathlib.Data.Int.GCD

/-!
# Primitive simultaneous rational approximations

This module makes the three-way gcd normalization in `MAYNARD-PRD-PUBLISHED`, Lemma 14.3, p.
202, exact for signed numerators.
-/

namespace PrimesRestrictedDigits

/-- If the approximation constant is smaller than the positive scale, a
signed numerator approximating a nonnegative grid point cannot be negative. -/
theorem int_numerator_nonneg_of_approximation
    {X q : Nat} (a : Fin X) {P C : Real} {b : Int}
    (hX : 0 < X) (hq : 0 < q) (hP : 0 < P) (hCP : C < P)
    (herror :
      |(a.val : Real) / (X : Real) - (b : Real) / (q : Real)| <=
        C / (P * (q : Real))) :
    0 <= b := by
  by_contra hb
  have hbneg : b < 0 := lt_of_not_ge hb
  have hbOne : (b : Real) <= -1 := by
    have hbOneInt : b <= -1 := by omega
    exact_mod_cast hbOneInt
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have haNonneg : 0 <= (a.val : Real) / (X : Real) := by positivity
  have hdiff : 1 / (q : Real) <=
      (a.val : Real) / (X : Real) - (b : Real) / (q : Real) := by
    apply (div_le_iff₀ hqReal).2
    have hbAbs : (1 : Real) <= -(b : Real) := by linarith
    calc
      (1 : Real) <= -(b : Real) := hbAbs
      _ <= ((a.val : Real) / (X : Real) - (b : Real) / (q : Real)) * q := by
        field_simp
        nlinarith
  have habs :
      |(a.val : Real) / (X : Real) - (b : Real) / (q : Real)| =
        (a.val : Real) / (X : Real) - (b : Real) / (q : Real) := by
    rw [abs_of_nonneg]
    exact (div_pos (by norm_num) hqReal).le.trans hdiff
  have hstrict : C / (P * (q : Real)) < 1 / (q : Real) := by
    rw [show C / (P * (q : Real)) = (C / P) / (q : Real) by ring]
    exact (div_lt_div_iff_of_pos_right hqReal).2 ((div_lt_one hP).2 hCP)
  rw [habs] at herror
  exact (not_lt_of_ge hdiff) (herror.trans_lt hstrict)

/-- Lemma 14.1 may be selected with natural numerators. In the small-scale
branch use its explicit zero approximation; in the large branch negativity is
excluded by the strict `10^6<P` error comparison. -/
theorem exists_latticeSimultaneousApproximation_nonnegative
    {X : Nat} (a1 a2 : Fin X) (N K delta : Real)
    (Lambda : RankTwoIntegralLattice)
    (hX : 1 <= X) (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / (X : Real) <= delta)
    (hcard : delta * K * N ^ 2 <=
      ((latticeGeneratingIntegerPoints a1 a2 Lambda delta N).card : Real))
    (hnonlinear : LatticePointsNotContainedInLine
      (latticeGeneratingIntegerPoints a1 a2 Lambda delta N)) :
    exists q : Nat, 0 < q ∧
      (q : Real) <= 1000000 * (X : Real) / (N * K) ∧
      exists b1 b2 : Nat,
        |(a1.val : Real) / (X : Real) - (b1 : Real) / (q : Real)| <=
            1000000 / (N * K * (q : Real)) ∧
        |(a2.val : Real) / (X : Real) - (b2 : Real) / (q : Real)| <=
            1000000 / (N * K * (q : Real)) := by
  have hXpos : 0 < X := Nat.zero_lt_one.trans_le hX
  have hNpos : 0 < N := Real.zero_lt_one.trans_le hN
  have hKpos : 0 < K := Real.zero_lt_one.trans_le hK
  have hPpos : 0 < N * K := mul_pos hNpos hKpos
  by_cases hsmall : N * K <= 1000000
  · have hqBound : (1 : Real) <= 1000000 * (X : Real) / (N * K) := by
      apply (le_div_iff₀ hPpos).2
      have hXReal : (1 : Real) <= X := by exact_mod_cast hX
      nlinarith
    have hone : (1 : Real) <= 1000000 / (N * K) := by
      exact (le_div_iff₀ hPpos).2 (by simpa using hsmall)
    have hangle (a : Fin X) : |(a.val : Real) / (X : Real)| <= 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact (div_le_one (by positivity)).2 (by exact_mod_cast a.isLt.le)
    exact ⟨1, by norm_num, by simpa using hqBound, 0, 0,
      by simpa using (hangle a1).trans hone,
      by simpa using (hangle a2).trans hone⟩
  · have hlarge : (1000000 : Real) < N * K := lt_of_not_ge hsmall
    obtain ⟨q, hq, hqBound, b1, b2, hb1Error, hb2Error⟩ :=
      latticeSimultaneousApproximation a1 a2 N K delta Lambda
        hX hN hK hdelta hdeltaLower hcard hnonlinear
    have hb1Nonneg := int_numerator_nonneg_of_approximation a1 hXpos hq
      hPpos hlarge hb1Error
    have hb2Nonneg := int_numerator_nonneg_of_approximation a2 hXpos hq
      hPpos hlarge hb2Error
    have hb1Cast : ((b1.toNat : Nat) : Real) = (b1 : Real) := by
      exact_mod_cast Int.toNat_of_nonneg hb1Nonneg
    have hb2Cast : ((b2.toNat : Nat) : Real) = (b2 : Real) := by
      exact_mod_cast Int.toNat_of_nonneg hb2Nonneg
    exact ⟨q, hq, hqBound, b1.toNat, b2.toNat,
      by simpa only [hb1Cast] using hb1Error,
      by simpa only [hb2Cast] using hb2Error⟩

/-- Divide two signed numerators and their common positive denominator by
their simultaneous gcd. Both rational values are unchanged. -/
theorem exists_primitiveSimultaneousFraction
    (b1 b2 : Int) (q : Nat) (hq : 0 < q) :
    exists b1' b2' : Int, exists q' : Nat,
      0 < q' ∧ q' <= q ∧
      (b1'.natAbs.gcd b2'.natAbs).Coprime q' ∧
      (b1' : Real) / (q' : Real) = (b1 : Real) / (q : Real) ∧
      (b2' : Real) / (q' : Real) = (b2 : Real) / (q : Real) := by
  let common : Nat := (b1.natAbs.gcd b2.natAbs).gcd q
  have hcommonPos : 0 < common := Nat.gcd_pos_of_pos_right _ hq
  have hcommonQ : common ∣ q := Nat.gcd_dvd_right _ _
  have hcommonGcd : common ∣ b1.natAbs.gcd b2.natAbs := Nat.gcd_dvd_left _ _
  have hcommonB1Nat : common ∣ b1.natAbs :=
    hcommonGcd.trans (Nat.gcd_dvd_left _ _)
  have hcommonB2Nat : common ∣ b2.natAbs :=
    hcommonGcd.trans (Nat.gcd_dvd_right _ _)
  have hcommonB1 : (common : Int) ∣ b1 := by
    rw [Int.natCast_dvd]
    exact hcommonB1Nat
  have hcommonB2 : (common : Int) ∣ b2 := by
    rw [Int.natCast_dvd]
    exact hcommonB2Nat
  let b1' : Int := b1 / common
  let b2' : Int := b2 / common
  let q' : Nat := q / common
  have hq'Pos : 0 < q' :=
    Nat.div_pos (Nat.le_of_dvd hq hcommonQ) hcommonPos
  have hb1Abs : b1'.natAbs = b1.natAbs / common := by
    exact Int.natAbs_ediv_of_dvd hcommonB1
  have hb2Abs : b2'.natAbs = b2.natAbs / common := by
    exact Int.natAbs_ediv_of_dvd hcommonB2
  have hpairGcd : b1'.natAbs.gcd b2'.natAbs =
      (b1.natAbs.gcd b2.natAbs) / common := by
    rw [hb1Abs, hb2Abs, Nat.gcd_div hcommonB1Nat hcommonB2Nat]
  have hprimitive : (b1'.natAbs.gcd b2'.natAbs).Coprime q' := by
    rw [hpairGcd]
    exact Nat.coprime_div_gcd_div_gcd hcommonPos
  have hqReal : (q : Real) ≠ 0 := by exact_mod_cast hq.ne'
  have hq'Eq : q' * common = q := Nat.div_mul_cancel hcommonQ
  have hb1Eq : b1' * common = b1 := Int.ediv_mul_cancel hcommonB1
  have hb2Eq : b2' * common = b2 := Int.ediv_mul_cancel hcommonB2
  refine ⟨b1', b2', q', hq'Pos, Nat.div_le_self _ _, hprimitive, ?_, ?_⟩
  · apply (div_eq_div_iff (by exact_mod_cast hq'Pos.ne') hqReal).2
    exact_mod_cast show b1' * (q : Int) = b1 * q' by
      rw [← hq'Eq, ← hb1Eq]
      push_cast
      ring
  · apply (div_eq_div_iff (by exact_mod_cast hq'Pos.ne') hqReal).2
    exact_mod_cast show b2' * (q : Int) = b2 * q' by
      rw [← hq'Eq, ← hb2Eq]
      push_cast
      ring

/-- Natural-numerator specialization of simultaneous primitive reduction.
This is the form used after the nonnegativity selection above. -/
theorem exists_primitiveSimultaneousFraction_nat
    (b1 b2 q : Nat) (hq : 0 < q) :
    exists b1' b2' q' : Nat,
      0 < q' ∧ q' <= q ∧
      (b1'.gcd b2').Coprime q' ∧
      (b1' : Real) / (q' : Real) = (b1 : Real) / (q : Real) ∧
      (b2' : Real) / (q' : Real) = (b2 : Real) / (q : Real) := by
  let common := (b1.gcd b2).gcd q
  have hcommonPos : 0 < common := Nat.gcd_pos_of_pos_right _ hq
  have hcommonQ : common ∣ q := Nat.gcd_dvd_right _ _
  have hcommonPair : common ∣ b1.gcd b2 := Nat.gcd_dvd_left _ _
  have hcommonB1 : common ∣ b1 := hcommonPair.trans (Nat.gcd_dvd_left _ _)
  have hcommonB2 : common ∣ b2 := hcommonPair.trans (Nat.gcd_dvd_right _ _)
  let b1' := b1 / common
  let b2' := b2 / common
  let q' := q / common
  have hq'Pos : 0 < q' :=
    Nat.div_pos (Nat.le_of_dvd hq hcommonQ) hcommonPos
  have hpairGcd : b1'.gcd b2' = b1.gcd b2 / common := by
    exact Nat.gcd_div hcommonB1 hcommonB2
  have hprimitive : (b1'.gcd b2').Coprime q' := by
    rw [hpairGcd]
    exact Nat.coprime_div_gcd_div_gcd hcommonPos
  have hqEq : q' * common = q := Nat.div_mul_cancel hcommonQ
  have hb1Eq : b1' * common = b1 := Nat.div_mul_cancel hcommonB1
  have hb2Eq : b2' * common = b2 := Nat.div_mul_cancel hcommonB2
  refine ⟨b1', b2', q', hq'Pos, Nat.div_le_self _ _, hprimitive, ?_, ?_⟩
  · apply (div_eq_div_iff (by positivity) (by positivity)).2
    exact_mod_cast show b1' * q = b1 * q' by rw [← hqEq, ← hb1Eq]; ring
  · apply (div_eq_div_iff (by positivity) (by positivity)).2
    exact_mod_cast show b2' * q = b2 * q' by rw [← hqEq, ← hb2Eq]; ring

/-- The two coordinate gcds of a primitive simultaneous fraction are
coprime. This omitted step justifies dividing by their product. -/
theorem coprime_gcd_gcd_of_pair_coprime
    {a b q : Nat} (h : (a.gcd b).Coprime q) :
    (a.gcd q).Coprime (b.gcd q) := by
  rw [Nat.coprime_iff_gcd_eq_one] at h ⊢
  let d := (a.gcd q).gcd (b.gcd q)
  have hda : d ∣ a :=
    (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hdb : d ∣ b :=
    (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hdq : d ∣ q :=
    (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hdtriple : d ∣ (a.gcd b).gcd q :=
    Nat.dvd_gcd (Nat.dvd_gcd hda hdb) hdq
  rw [h] at hdtriple
  exact Nat.dvd_one.mp hdtriple

end PrimesRestrictedDigits
