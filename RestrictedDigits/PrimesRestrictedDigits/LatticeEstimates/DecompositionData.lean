import PrimesRestrictedDigits.LatticeEstimates.DecompositionKey
import PrimesRestrictedDigits.LatticeEstimates.OrientedApproximation
import PrimesRestrictedDigits.LatticeEstimates.SmoothFactorBands

/-!
# Selected scale data for the Lemma 14.3 decomposition

This localizes one chosen oriented primitive approximation and its exact denominator
factorization into the five finite decimal bins from `DecompositionKey`.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Under the source hypothesis `P >= 1`, the selected denominator is at
most `10^(length+6)`. -/
theorem LatticePrimitiveApproximation.q_le_ten_pow_add_six
    {length : Nat} {a1 a2 : Fin (10 ^ length)} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P) (hP : 1 <= P) :
    w.q <= 10 ^ (length + 6) := by
  have hquotient :
      1000000 * (((10 ^ length : Nat) : Real)) / P <=
        1000000 * (((10 ^ length : Nat) : Real)) :=
    div_le_self (by positivity) hP
  have hqReal : (w.q : Real) <= ((10 ^ (length + 6) : Nat) : Real) := by
    calc
      (w.q : Real) <=
          1000000 * (((10 ^ length : Nat) : Real)) / P := w.q_le
      _ <= 1000000 * (((10 ^ length : Nat) : Real)) := hquotient
      _ = ((10 ^ (length + 6) : Nat) : Real) := by
        norm_num only [Nat.cast_pow, Nat.cast_ofNat]
        rw [pow_add]
        norm_num
        ring
  exact_mod_cast hqReal

/-- The canonical five-bin key selected by an exact factorization whose
denominator has the source upper bound. -/
def LatticeRationalFactorization.scaleKey
    {b1 b2 : Int} {q length : Nat}
    (f : LatticeRationalFactorization b1 b2 q)
    (hq : q <= 10 ^ (length + 6)) :
    LatticeDecompositionScaleKey length where
  qPrimeIndex :=
    ⟨factorTenIndex f.qPrime, by
      have hindex := factorTenIndex_le_of_le_ten_pow (f.factors_le.1.trans hq)
      omega⟩
  g1PrimeIndex :=
    ⟨factorTenIndex f.g1Prime, by
      have hindex :=
        factorTenIndex_le_of_le_ten_pow (f.factors_le.2.1.trans hq)
      omega⟩
  g2Index :=
    ⟨factorTenIndex f.g2, by
      have hindex :=
        factorTenIndex_le_of_le_ten_pow (f.factors_le.2.2.1.trans hq)
      omega⟩
  d0Index :=
    ⟨factorTenIndex f.d0, by
      have hindex :=
        factorTenIndex_le_of_le_ten_pow (f.factors_le.2.2.2.1.trans hq)
      omega⟩
  d1Index :=
    ⟨factorTenIndex f.d1, by
      have hindex :=
        factorTenIndex_le_of_le_ten_pow (f.factors_le.2.2.2.2.trans hq)
      omega⟩

/-- The five-scale key canonically attached to one selected factorization. -/
def LatticePrimitiveApproximation.decompositionScaleKey
    {length : Nat} {a1 a2 : Fin (10 ^ length)} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P) (hP : 1 <= P)
    (f : LatticeRationalFactorization (w.b1 : Int) (w.b2 : Int) w.q) :
    LatticeDecompositionScaleKey length :=
  f.scaleKey (w.q_le_ten_pow_add_six hP)

@[simp]
theorem LatticeRationalFactorization.scaleKey_qPrimeScale
    {b1 b2 : Int} {q length : Nat}
    (f : LatticeRationalFactorization b1 b2 q)
    (hq : q <= 10 ^ (length + 6)) :
    (f.scaleKey hq).qPrimeScale = factorTenScale f.qPrime :=
  rfl

@[simp]
theorem LatticeRationalFactorization.scaleKey_g1PrimeScale
    {b1 b2 : Int} {q length : Nat}
    (f : LatticeRationalFactorization b1 b2 q)
    (hq : q <= 10 ^ (length + 6)) :
    (f.scaleKey hq).g1PrimeScale = factorTenScale f.g1Prime :=
  rfl

@[simp]
theorem LatticeRationalFactorization.scaleKey_g2Scale
    {b1 b2 : Int} {q length : Nat}
    (f : LatticeRationalFactorization b1 b2 q)
    (hq : q <= 10 ^ (length + 6)) :
    (f.scaleKey hq).g2Scale = factorTenScale f.g2 :=
  rfl

@[simp]
theorem LatticeRationalFactorization.scaleKey_d0Scale
    {b1 b2 : Int} {q length : Nat}
    (f : LatticeRationalFactorization b1 b2 q)
    (hq : q <= 10 ^ (length + 6)) :
    (f.scaleKey hq).d0Scale = factorTenScale f.d0 :=
  rfl

@[simp]
theorem LatticeRationalFactorization.scaleKey_d1Scale
    {b1 b2 : Int} {q length : Nat}
    (f : LatticeRationalFactorization b1 b2 q)
    (hq : q <= 10 ^ (length + 6)) :
    (f.scaleKey hq).d1Scale = factorTenScale f.d1 :=
  rfl

/-- Every factor lies in the exact source decade band selected by the key. -/
theorem LatticeRationalFactorization.mem_scaleKey_bands
    {b1 b2 : Int} {q length : Nat}
    (f : LatticeRationalFactorization b1 b2 q)
    (hq : q <= 10 ^ (length + 6)) :
    f.qPrime ∈ latticeFactorTenBand (f.scaleKey hq).qPrimeScale ∧
      f.g1Prime ∈ latticeFactorTenBand (f.scaleKey hq).g1PrimeScale ∧
      f.g2 ∈ latticeFactorTenBand (f.scaleKey hq).g2Scale ∧
      f.d0 ∈ latticeFactorTenBand (f.scaleKey hq).d0Scale ∧
      f.d1 ∈ latticeFactorTenBand (f.scaleKey hq).d1Scale := by
  simp only [f.scaleKey_qPrimeScale, f.scaleKey_g1PrimeScale,
    f.scaleKey_g2Scale, f.scaleKey_d0Scale, f.scaleKey_d1Scale]
  exact ⟨mem_latticeFactorTenBand_factorTenScale f.qPrime_pos,
    mem_latticeFactorTenBand_factorTenScale f.g1Prime_pos,
    mem_latticeFactorTenBand_factorTenScale f.g2_pos,
    mem_latticeFactorTenBand_factorTenScale f.d0_pos,
    mem_latticeFactorTenBand_factorTenScale f.d1_pos⟩

/-- The product of the five scales contains the selected denominator. -/
theorem LatticeRationalFactorization.le_scaleKey_denominatorScale
    {b1 b2 : Int} {q length : Nat}
    (f : LatticeRationalFactorization b1 b2 q)
    (hq : q <= 10 ^ (length + 6)) :
    q <= (f.scaleKey hq).denominatorScale := by
  have hbands := f.mem_scaleKey_bands hq
  have hqPrime := (mem_latticeFactorTenBand_iff.mp hbands.1).2.1
  have hg1Prime := (mem_latticeFactorTenBand_iff.mp hbands.2.1).2.1
  have hg2 := (mem_latticeFactorTenBand_iff.mp hbands.2.2.1).2.1
  have hd0 := (mem_latticeFactorTenBand_iff.mp hbands.2.2.2.1).2.1
  have hd1 := (mem_latticeFactorTenBand_iff.mp hbands.2.2.2.2).2.1
  calc
    q = f.g1Prime * f.g2 * f.d0 * f.d1 * f.qPrime := f.denominator_eq
    _ <= (f.scaleKey hq).g1PrimeScale * (f.scaleKey hq).g2Scale *
        (f.scaleKey hq).d0Scale * (f.scaleKey hq).d1Scale *
          (f.scaleKey hq).qPrimeScale := by gcongr
    _ = (f.scaleKey hq).denominatorScale := by
      simp only [LatticeDecompositionScaleKey.denominatorScale]
      ring

/-- The product of the five scales loses strictly less than `10^5`. -/
theorem LatticeRationalFactorization.scaleKey_denominatorScale_lt
    {b1 b2 : Int} {q length : Nat}
    (f : LatticeRationalFactorization b1 b2 q)
    (hq : q <= 10 ^ (length + 6)) :
    (f.scaleKey hq).denominatorScale < 100000 * q := by
  calc
    (f.scaleKey hq).denominatorScale =
        factorTenScale f.qPrime * factorTenScale f.g1Prime *
          factorTenScale f.g2 * factorTenScale f.d0 * factorTenScale f.d1 := by
      simp only [LatticeDecompositionScaleKey.denominatorScale,
        f.scaleKey_qPrimeScale, f.scaleKey_g1PrimeScale,
        f.scaleKey_g2Scale, f.scaleKey_d0Scale, f.scaleKey_d1Scale]
    _ < 100000 *
        (f.qPrime * f.g1Prime * f.g2 * f.d0 * f.d1) :=
      factorTenScale_five_product_lt f.qPrime_pos f.g1Prime_pos f.g2_pos
        f.d0_pos f.d1_pos
    _ = 100000 * q := by
      apply congrArg (100000 * ·)
      calc
        f.qPrime * f.g1Prime * f.g2 * f.d0 * f.d1 =
            f.g1Prime * f.g2 * f.d0 * f.d1 * f.qPrime := by ring
        _ = q := f.denominator_eq.symm

/-- The ordered gcd branch gives the sharp scale relation
`G'_1 D_1 < 100 G_2`. -/
theorem LatticeRationalFactorization.scaleKey_ordered_lt
    {b1 b2 : Int} {q length : Nat}
    (f : LatticeRationalFactorization b1 b2 q)
    (hq : q <= 10 ^ (length + 6)) :
    (f.scaleKey hq).g1PrimeScale * (f.scaleKey hq).d1Scale <
      100 * (f.scaleKey hq).g2Scale := by
  have hbands := f.mem_scaleKey_bands hq
  have hg1 := (mem_latticeFactorTenBand_iff.mp hbands.2.1).2.2
  have hg2 := (mem_latticeFactorTenBand_iff.mp hbands.2.2.1).2.1
  have hd1 := (mem_latticeFactorTenBand_iff.mp hbands.2.2.2.2).2.2
  calc
    (f.scaleKey hq).g1PrimeScale * (f.scaleKey hq).d1Scale <
        (10 * f.g1Prime) * (10 * f.d1) := by gcongr
    _ = 100 * (f.g1Prime * f.d1) := by ring
    _ <= 100 * f.g2 := Nat.mul_le_mul_left 100 f.ordered
    _ <= 100 * (f.scaleKey hq).g2Scale := Nat.mul_le_mul_left 100 hg2

/-- The two decimal-primary factors lie in their selected smooth bands. -/
theorem LatticeRationalFactorization.mem_scaleKey_smooth_bands
    {b1 b2 : Int} {q length : Nat}
    (f : LatticeRationalFactorization b1 b2 q)
    (hq : q <= 10 ^ (length + 6)) :
    f.d0 ∈ latticeSmoothFactorTenBand (f.scaleKey hq).d0Scale ∧
      f.d1 ∈ latticeSmoothFactorTenBand (f.scaleKey hq).d1Scale := by
  have hbands := f.mem_scaleKey_bands hq
  exact ⟨mem_latticeSmoothFactorTenBand_iff.mpr
      ⟨hbands.2.2.2.1, f.d0_smooth⟩,
    mem_latticeSmoothFactorTenBand_iff.mpr
      ⟨hbands.2.2.2.2, f.d1_smooth⟩⟩

/-- The two factors required to be coprime to ten lie in their selected
residual source bands. -/
theorem LatticeRationalFactorization.mem_scaleKey_residual_bands
    {b1 b2 : Int} {q length : Nat}
    (f : LatticeRationalFactorization b1 b2 q)
    (hq : q <= 10 ^ (length + 6)) :
    f.qPrime ∈ hybridResidualSourceDenominators (f.scaleKey hq).qPrimeScale ∧
      f.g1Prime ∈
        hybridResidualSourceDenominators (f.scaleKey hq).g1PrimeScale := by
  have hbands := f.mem_scaleKey_bands hq
  have hqPrime := mem_latticeFactorTenBand_iff.mp hbands.1
  have hg1Prime := mem_latticeFactorTenBand_iff.mp hbands.2.1
  exact ⟨mem_hybridResidualSourceDenominators_iff.mpr
      ⟨hqPrime.1, hqPrime.2.1, hqPrime.2.2, f.qPrime_coprime_ten⟩,
    mem_hybridResidualSourceDenominators_iff.mpr
      ⟨hg1Prime.1, hg1Prime.2.1, hg1Prime.2.2, f.g1Prime_coprime_ten⟩⟩

end

end PrimesRestrictedDigits
