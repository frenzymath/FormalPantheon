import PrimesRestrictedDigits.LatticeEstimates.PrimitiveApproximation

/-!
# Denominator factorization for Lemma 14.3

This packages the exact arithmetic decomposition used in `MAYNARD-PRD-PUBLISHED`, Lemma 14.3,
pp. 202--203. It adds no false pairwise coprimality between the five denominator factors.
-/

namespace PrimesRestrictedDigits

/-- The oriented denominator and numerator data used by the two Lemma 14.3
factorizations. -/
structure LatticeRationalFactorization (b1 b2 : Int) (q : Nat) where
  b1Prime : Int
  b2Prime : Int
  qPrime : Nat
  g1Prime : Nat
  g2 : Nat
  d0 : Nat
  d1 : Nat
  qPrime_pos : 0 < qPrime
  g1Prime_pos : 0 < g1Prime
  g2_pos : 0 < g2
  d0_pos : 0 < d0
  d1_pos : 0 < d1
  qPrime_coprime_ten : qPrime.Coprime 10
  g1Prime_coprime_ten : g1Prime.Coprime 10
  d0_smooth : IsDecimalSmooth d0
  d1_smooth : IsDecimalSmooth d1
  denominator_eq : q = g1Prime * g2 * d0 * d1 * qPrime
  firstNumerator_eq : b1 = b1Prime * (d1 * g1Prime)
  secondNumerator_eq : b2 = b2Prime * g2
  first_reduced : b1Prime.natAbs.Coprime (d0 * qPrime * g2)
  second_reduced : b2Prime.natAbs.Coprime (d0 * d1 * qPrime * g1Prime)
  ordered : g1Prime * d1 <= g2

theorem LatticeRationalFactorization.qPrime_dvd
    {b1 b2 : Int} {q : Nat} (f : LatticeRationalFactorization b1 b2 q) :
    f.qPrime ∣ q := by
  refine ⟨f.g1Prime * f.g2 * f.d0 * f.d1, ?_⟩
  calc
    q = f.g1Prime * f.g2 * f.d0 * f.d1 * f.qPrime := f.denominator_eq
    _ = f.qPrime * (f.g1Prime * f.g2 * f.d0 * f.d1) := by ring

theorem LatticeRationalFactorization.g1Prime_dvd
    {b1 b2 : Int} {q : Nat} (f : LatticeRationalFactorization b1 b2 q) :
    f.g1Prime ∣ q := by
  refine ⟨f.g2 * f.d0 * f.d1 * f.qPrime, ?_⟩
  calc
    q = f.g1Prime * f.g2 * f.d0 * f.d1 * f.qPrime := f.denominator_eq
    _ = f.g1Prime * (f.g2 * f.d0 * f.d1 * f.qPrime) := by ring

theorem LatticeRationalFactorization.g2_dvd
    {b1 b2 : Int} {q : Nat} (f : LatticeRationalFactorization b1 b2 q) :
    f.g2 ∣ q := by
  refine ⟨f.g1Prime * f.d0 * f.d1 * f.qPrime, ?_⟩
  calc
    q = f.g1Prime * f.g2 * f.d0 * f.d1 * f.qPrime := f.denominator_eq
    _ = f.g2 * (f.g1Prime * f.d0 * f.d1 * f.qPrime) := by ring

theorem LatticeRationalFactorization.d0_dvd
    {b1 b2 : Int} {q : Nat} (f : LatticeRationalFactorization b1 b2 q) :
    f.d0 ∣ q := by
  refine ⟨f.g1Prime * f.g2 * f.d1 * f.qPrime, ?_⟩
  calc
    q = f.g1Prime * f.g2 * f.d0 * f.d1 * f.qPrime := f.denominator_eq
    _ = f.d0 * (f.g1Prime * f.g2 * f.d1 * f.qPrime) := by ring

theorem LatticeRationalFactorization.d1_dvd
    {b1 b2 : Int} {q : Nat} (f : LatticeRationalFactorization b1 b2 q) :
    f.d1 ∣ q := by
  refine ⟨f.g1Prime * f.g2 * f.d0 * f.qPrime, ?_⟩
  calc
    q = f.g1Prime * f.g2 * f.d0 * f.d1 * f.qPrime := f.denominator_eq
    _ = f.d1 * (f.g1Prime * f.g2 * f.d0 * f.qPrime) := by ring

theorem LatticeRationalFactorization.factors_le
    {b1 b2 : Int} {q : Nat} (f : LatticeRationalFactorization b1 b2 q) :
    f.qPrime <= q ∧ f.g1Prime <= q ∧ f.g2 <= q ∧ f.d0 <= q ∧ f.d1 <= q := by
  have hq : 0 < q := by
    calc
      0 < f.g1Prime * f.g2 * f.d0 * f.d1 * f.qPrime :=
        Nat.mul_pos
          (Nat.mul_pos
            (Nat.mul_pos (Nat.mul_pos f.g1Prime_pos f.g2_pos) f.d0_pos)
            f.d1_pos)
          f.qPrime_pos
      _ = q := f.denominator_eq.symm
  exact ⟨Nat.le_of_dvd hq f.qPrime_dvd,
    Nat.le_of_dvd hq f.g1Prime_dvd,
    Nat.le_of_dvd hq f.g2_dvd,
    Nat.le_of_dvd hq f.d0_dvd,
    Nat.le_of_dvd hq f.d1_dvd⟩

/-- A primitive simultaneous fraction whose first coordinate gcd is no larger
than its second has the exact source factorization. -/
theorem exists_latticeRationalFactorization
    {b1 b2 : Int} {q : Nat} (hq : 0 < q)
    (hprimitive : (b1.natAbs.gcd b2.natAbs).Coprime q)
    (hordered : b1.natAbs.gcd q <= b2.natAbs.gcd q) :
    Nonempty (LatticeRationalFactorization b1 b2 q) := by
  let g1 := b1.natAbs.gcd q
  let g2 := b2.natAbs.gcd q
  have hg1Pos : 0 < g1 := Nat.gcd_pos_of_pos_right _ hq
  have hg2Pos : 0 < g2 := Nat.gcd_pos_of_pos_right _ hq
  have hg1b : g1 ∣ b1.natAbs := Nat.gcd_dvd_left _ _
  have hg2b : g2 ∣ b2.natAbs := Nat.gcd_dvd_left _ _
  have hg1q : g1 ∣ q := Nat.gcd_dvd_right _ _
  have hg2q : g2 ∣ q := Nat.gcd_dvd_right _ _
  have hg12 : g1.Coprime g2 :=
    coprime_gcd_gcd_of_pair_coprime hprimitive
  have hgprodq : g1 * g2 ∣ q :=
    hg12.mul_dvd_of_dvd_of_dvd hg1q hg2q
  let rest := q / (g1 * g2)
  have hrestPos : 0 < rest :=
    Nat.div_pos (Nat.le_of_dvd hq hgprodq) (Nat.mul_pos hg1Pos hg2Pos)
  obtain ⟨d0, qPrime, hd0Pos, hqPrimePos, hd0Smooth, hqPrimeTen,
      hd0qPrime⟩ := exists_decimalSmooth_mul_coprime_ten rest hrestPos
  obtain ⟨d1, g1Prime, hd1Pos, hg1PrimePos, hd1Smooth, hg1PrimeTen,
      hd1g1Prime⟩ := exists_decimalSmooth_mul_coprime_ten g1 hg1Pos
  let b1Prime : Int := b1 / g1
  let b2Prime : Int := b2 / g2
  have hg1bInt : (g1 : Int) ∣ b1 := by rw [Int.natCast_dvd]; exact hg1b
  have hg2bInt : (g2 : Int) ∣ b2 := by rw [Int.natCast_dvd]; exact hg2b
  have hb1Abs : b1Prime.natAbs = b1.natAbs / g1 :=
    Int.natAbs_ediv_of_dvd hg1bInt
  have hb2Abs : b2Prime.natAbs = b2.natAbs / g2 :=
    Int.natAbs_ediv_of_dvd hg2bInt
  have hb1Reduced : b1Prime.natAbs.Coprime (q / g1) := by
    rw [hb1Abs]
    exact Nat.coprime_div_gcd_div_gcd hg1Pos
  have hb2Reduced : b2Prime.natAbs.Coprime (q / g2) := by
    rw [hb2Abs]
    exact Nat.coprime_div_gcd_div_gcd hg2Pos
  have hqRest : g1 * g2 * rest = q := Nat.mul_div_cancel' hgprodq
  have hqDivG1 : q / g1 = g2 * rest := by
    apply Nat.eq_of_mul_eq_mul_left hg1Pos
    rw [Nat.mul_div_cancel' hg1q, ← hqRest]
    ring
  have hqDivG2 : q / g2 = g1 * rest := by
    apply Nat.eq_of_mul_eq_mul_left hg2Pos
    rw [Nat.mul_div_cancel' hg2q, ← hqRest]
    ring
  have hdenominator : q = g1Prime * g2 * d0 * d1 * qPrime := by
    rw [← hqRest, ← hd0qPrime, ← hd1g1Prime]
    ring
  have hb1Eq : b1 = b1Prime * (d1 * g1Prime) := by
    have hcast : (g1 : Int) = (d1 : Int) * (g1Prime : Int) := by
      exact_mod_cast hd1g1Prime.symm
    calc
      b1 = b1Prime * (g1 : Int) := (Int.ediv_mul_cancel hg1bInt).symm
      _ = b1Prime * (d1 * g1Prime) := by rw [hcast]
  have hb2Eq : b2 = b2Prime * g2 :=
    (Int.ediv_mul_cancel hg2bInt).symm
  have hb1Reduced' : b1Prime.natAbs.Coprime (d0 * qPrime * g2) := by
    rw [show d0 * qPrime * g2 = g2 * rest by rw [hd0qPrime]; ring,
      ← hqDivG1]
    exact hb1Reduced
  have hb2Reduced' :
      b2Prime.natAbs.Coprime (d0 * d1 * qPrime * g1Prime) := by
    rw [show d0 * d1 * qPrime * g1Prime = g1 * rest by
      calc
        d0 * d1 * qPrime * g1Prime = (d1 * g1Prime) * (d0 * qPrime) := by ring
        _ = g1 * rest := by rw [hd1g1Prime, hd0qPrime],
      ← hqDivG2]
    exact hb2Reduced
  refine ⟨{
    b1Prime := b1Prime
    b2Prime := b2Prime
    qPrime := qPrime
    g1Prime := g1Prime
    g2 := g2
    d0 := d0
    d1 := d1
    qPrime_pos := hqPrimePos
    g1Prime_pos := hg1PrimePos
    g2_pos := hg2Pos
    d0_pos := hd0Pos
    d1_pos := hd1Pos
    qPrime_coprime_ten := hqPrimeTen
    g1Prime_coprime_ten := hg1PrimeTen
    d0_smooth := hd0Smooth
    d1_smooth := hd1Smooth
    denominator_eq := hdenominator
    firstNumerator_eq := hb1Eq
    secondNumerator_eq := hb2Eq
    first_reduced := hb1Reduced'
    second_reduced := hb2Reduced'
    ordered := ?_ }⟩
  calc
    g1Prime * d1 = d1 * g1Prime := by ring
    _ = g1 := hd1g1Prime
    _ <= g2 := by simpa only [g1, g2] using hordered

end PrimesRestrictedDigits
