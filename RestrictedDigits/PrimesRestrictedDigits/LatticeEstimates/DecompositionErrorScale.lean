import PrimesRestrictedDigits.LatticeEstimates.DecompositionData

/-!
# Error-scale bounds for the Lemma 14.3 decomposition

This file proves that the deterministic error scale attached to actually selected five-bin
data has the sharp source bounds required by the repaired proof of `MAYNARD-PRD-PUBLISHED`,
Lemma 14.3.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The target determining the error scale of selected data is strictly
larger than one. -/
theorem LatticePrimitiveApproximation.one_lt_scaleKey_errorTarget
    {length : Nat} {a1 a2 : Fin (10 ^ length)} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P) (hP : 1 <= P)
    (f : LatticeRationalFactorization (w.b1 : Int) (w.b2 : Int) w.q) :
    1 < (w.decompositionScaleKey hP f).errorTarget P := by
  let key := w.decompositionScaleKey hP f
  have hPPos : 0 < P := Real.zero_lt_one.trans_le hP
  have hQ0PosNat : 0 < key.denominatorScale := by
    unfold LatticeDecompositionScaleKey.denominatorScale
      LatticeDecompositionScaleKey.qPrimeScale
      LatticeDecompositionScaleKey.g1PrimeScale
      LatticeDecompositionScaleKey.g2Scale
      LatticeDecompositionScaleKey.d0Scale
      LatticeDecompositionScaleKey.d1Scale
    positivity
  have hQ0Pos : 0 < (key.denominatorScale : Real) := by
    exact_mod_cast hQ0PosNat
  have hQ0q : (key.denominatorScale : Real) < 100000 * (w.q : Real) := by
    have hQ0qNat : key.denominatorScale < 100000 * w.q := by
      simpa only [key, LatticePrimitiveApproximation.decompositionScaleKey] using
        f.scaleKey_denominatorScale_lt (w.q_le_ten_pow_add_six hP)
    exact_mod_cast hQ0qNat
  have hPq : (w.q : Real) * P <=
      1000000 * ((10 ^ length : Nat) : Real) :=
    (le_div_iff₀ hPPos).1 w.q_le
  have hproduct :
      P * (key.denominatorScale : Real) <
        ((10 ^ 11 : Nat) : Real) * ((10 ^ length : Nat) : Real) := by
    calc
      P * (key.denominatorScale : Real) <
          P * (100000 * (w.q : Real)) := by gcongr
      _ = 100000 * ((w.q : Real) * P) := by ring
      _ <= 100000 *
          (1000000 * ((10 ^ length : Nat) : Real)) := by gcongr
      _ = ((10 ^ 11 : Nat) : Real) *
          ((10 ^ length : Nat) : Real) := by
        norm_num
        ring
  change 1 <
    (((10 ^ 11 : Nat) : Real) * ((10 ^ length : Nat) : Real)) /
      (P * (key.denominatorScale : Real))
  exact (one_lt_div (mul_pos hPPos hQ0Pos)).2 hproduct

/-- The selected power of ten lies in the exact interval `[T,10T)`. -/
theorem LatticePrimitiveApproximation.scaleKey_errorScale_bounds
    {length : Nat} {a1 a2 : Fin (10 ^ length)} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P) (hP : 1 <= P)
    (f : LatticeRationalFactorization (w.b1 : Int) (w.b2 : Int) w.q) :
    let key := w.decompositionScaleKey hP f
    key.errorTarget P <= (key.errorScale P : Real) ∧
      (key.errorScale P : Real) < 10 * key.errorTarget P := by
  simpa only [LatticeDecompositionScaleKey.errorScale,
    LatticeDecompositionScaleKey.errorScaleIndex,
    latticePositiveRealFactorTenScale] using
    latticePositiveRealFactorTenScale_bounds
      (w.one_lt_scaleKey_errorTarget hP f)

/-- The selected denominator and error scales satisfy the sharp loss-12
source inequality. -/
theorem LatticePrimitiveApproximation.scaleKey_product_lt
    {length : Nat} {a1 a2 : Fin (10 ^ length)} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P) (hP : 1 <= P)
    (f : LatticeRationalFactorization (w.b1 : Int) (w.b2 : Int) w.q) :
    let key := w.decompositionScaleKey hP f
    (((key.errorScale P * key.denominatorScale : Nat) : Real) <
      ((10 ^ 12 : Nat) : Real) * ((10 ^ length : Nat) : Real) / P) := by
  let key := w.decompositionScaleKey hP f
  have hPPos : 0 < P := Real.zero_lt_one.trans_le hP
  have hQ0PosNat : 0 < key.denominatorScale := by
    unfold LatticeDecompositionScaleKey.denominatorScale
      LatticeDecompositionScaleKey.qPrimeScale
      LatticeDecompositionScaleKey.g1PrimeScale
      LatticeDecompositionScaleKey.g2Scale
      LatticeDecompositionScaleKey.d0Scale
      LatticeDecompositionScaleKey.d1Scale
    positivity
  have hQ0Pos : 0 < (key.denominatorScale : Real) := by
    exact_mod_cast hQ0PosNat
  have hupper := (w.scaleKey_errorScale_bounds hP f).2
  calc
    (((key.errorScale P * key.denominatorScale : Nat) : Real)) =
        (key.denominatorScale : Real) * (key.errorScale P : Real) := by
      push_cast
      ring
    _ < (key.denominatorScale : Real) * (10 * key.errorTarget P) := by
      gcongr
    _ = ((10 ^ 12 : Nat) : Real) *
        ((10 ^ length : Nat) : Real) / P := by
      rw [LatticeDecompositionScaleKey.errorTarget]
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      field_simp [ne_of_gt hPPos, ne_of_gt hQ0Pos]
      ring

/-- The scale exponent of selected data is at most `length+11`. -/
theorem LatticePrimitiveApproximation.scaleKey_errorScaleIndex_le
    {length : Nat} {a1 a2 : Fin (10 ^ length)} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P) (hP : 1 <= P)
    (f : LatticeRationalFactorization (w.b1 : Int) (w.b2 : Int) w.q) :
    (w.decompositionScaleKey hP f).errorScaleIndex P <= length + 11 := by
  let key := w.decompositionScaleKey hP f
  have hQ0PosNat : 0 < key.denominatorScale := by
    unfold LatticeDecompositionScaleKey.denominatorScale
      LatticeDecompositionScaleKey.qPrimeScale
      LatticeDecompositionScaleKey.g1PrimeScale
      LatticeDecompositionScaleKey.g2Scale
      LatticeDecompositionScaleKey.d0Scale
      LatticeDecompositionScaleKey.d1Scale
    positivity
  have hQ0One : (1 : Real) <= (key.denominatorScale : Real) := by
    exact_mod_cast hQ0PosNat
  have hdenominatorOne : (1 : Real) <= P * (key.denominatorScale : Real) := by
    nlinarith
  have htarget : key.errorTarget P <=
      ((10 ^ (length + 11) : Nat) : Real) := by
    calc
      key.errorTarget P =
          (((10 ^ 11 : Nat) : Real) * ((10 ^ length : Nat) : Real)) /
            (P * (key.denominatorScale : Real)) := rfl
      _ <= ((10 ^ 11 : Nat) : Real) *
          ((10 ^ length : Nat) : Real) :=
        div_le_self (by positivity) hdenominatorOne
      _ = ((10 ^ (length + 11) : Nat) : Real) := by
        norm_num only [Nat.cast_pow, Nat.cast_ofNat]
        rw [pow_add]
        ring
  simpa only [key, LatticeDecompositionScaleKey.errorScaleIndex] using
    latticePositiveRealFactorTenExponent_le htarget

/-- The primitive approximation error fits inside the deterministic selected
error scale. -/
theorem LatticePrimitiveApproximation.sourceError_lt_scaleKey
    {length : Nat} {a1 a2 : Fin (10 ^ length)} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P) (hP : 1 <= P)
    (f : LatticeRationalFactorization (w.b1 : Int) (w.b2 : Int) w.q) :
    1000000 / (P * (w.q : Real)) <
      ((w.decompositionScaleKey hP f).errorScale P : Real) /
        ((10 ^ length : Nat) : Real) := by
  let key := w.decompositionScaleKey hP f
  have hPPos : 0 < P := Real.zero_lt_one.trans_le hP
  have hqPos : 0 < (w.q : Real) := by exact_mod_cast w.q_pos
  have hQ0PosNat : 0 < key.denominatorScale := by
    unfold LatticeDecompositionScaleKey.denominatorScale
      LatticeDecompositionScaleKey.qPrimeScale
      LatticeDecompositionScaleKey.g1PrimeScale
      LatticeDecompositionScaleKey.g2Scale
      LatticeDecompositionScaleKey.d0Scale
      LatticeDecompositionScaleKey.d1Scale
    positivity
  have hQ0Pos : 0 < (key.denominatorScale : Real) := by
    exact_mod_cast hQ0PosNat
  have hXPos : 0 < ((10 ^ length : Nat) : Real) := by positivity
  have hQ0q : (key.denominatorScale : Real) < 100000 * (w.q : Real) := by
    have hQ0qNat : key.denominatorScale < 100000 * w.q := by
      simpa only [key, LatticePrimitiveApproximation.decompositionScaleKey] using
        f.scaleKey_denominatorScale_lt (w.q_le_ten_pow_add_six hP)
    exact_mod_cast hQ0qNat
  have hfirst :
      1000000 / (P * (w.q : Real)) <
        ((10 ^ 11 : Nat) : Real) /
          (P * (key.denominatorScale : Real)) := by
    apply (div_lt_div_iff₀ (mul_pos hPPos hqPos) (mul_pos hPPos hQ0Pos)).2
    calc
      1000000 * (P * (key.denominatorScale : Real)) <
          1000000 * (P * (100000 * (w.q : Real))) := by gcongr
      _ = ((10 ^ 11 : Nat) : Real) * (P * (w.q : Real)) := by
        norm_num
        ring
  calc
    1000000 / (P * (w.q : Real)) <
        ((10 ^ 11 : Nat) : Real) /
          (P * (key.denominatorScale : Real)) := hfirst
    _ = key.errorTarget P / ((10 ^ length : Nat) : Real) := by
      rw [LatticeDecompositionScaleKey.errorTarget]
      field_simp [ne_of_gt hXPos]
    _ <= (key.errorScale P : Real) /
        ((10 ^ length : Nat) : Real) := by
      exact div_le_div_of_nonneg_right (w.scaleKey_errorScale_bounds hP f).1
        hXPos.le

/-- Both selected coordinate errors lie in the deterministic aligned window. -/
theorem LatticePrimitiveApproximation.errors_le_scaleKey
    {length : Nat} {a1 a2 : Fin (10 ^ length)} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P) (hP : 1 <= P)
    (f : LatticeRationalFactorization (w.b1 : Int) (w.b2 : Int) w.q) :
    let key := w.decompositionScaleKey hP f
    |(a1.val : Real) / ((10 ^ length : Nat) : Real) -
        (w.b1 : Real) / (w.q : Real)| <=
        (key.errorScale P : Real) / ((10 ^ length : Nat) : Real) ∧
      |(a2.val : Real) / ((10 ^ length : Nat) : Real) -
        (w.b2 : Real) / (w.q : Real)| <=
        (key.errorScale P : Real) / ((10 ^ length : Nat) : Real) := by
  exact ⟨w.first_error.trans (w.sourceError_lt_scaleKey hP f).le,
    w.second_error.trans (w.sourceError_lt_scaleKey hP f).le⟩

/-- Every selected key satisfies the two downstream admissibility
inequalities; arbitrary keys are deliberately not asserted admissible. -/
theorem LatticePrimitiveApproximation.scaleKey_isAdmissible
    {length : Nat} {a1 a2 : Fin (10 ^ length)} {P : Real}
    (w : LatticePrimitiveApproximation a1 a2 P) (hP : 1 <= P)
    (f : LatticeRationalFactorization (w.b1 : Int) (w.b2 : Int) w.q) :
    (w.decompositionScaleKey hP f).IsAdmissible P := by
  let key := w.decompositionScaleKey hP f
  refine ⟨(w.scaleKey_product_lt hP f).le, ?_⟩
  have hD1One : 1 <= key.d1Scale := by
    unfold LatticeDecompositionScaleKey.d1Scale
    exact Nat.one_le_pow _ _ (by norm_num)
  have hG1Product : key.g1PrimeScale <= key.g1PrimeScale * key.d1Scale := by
    simpa only [mul_one] using Nat.mul_le_mul_left key.g1PrimeScale hD1One
  have hordered : key.g1PrimeScale * key.d1Scale < 100 * key.g2Scale := by
    simpa only [key, LatticePrimitiveApproximation.decompositionScaleKey] using
      f.scaleKey_ordered_lt (w.q_le_ten_pow_add_six hP)
  have hNat : key.g1PrimeScale <= (10 ^ 12) * key.g2Scale := by
    calc
      key.g1PrimeScale <= key.g1PrimeScale * key.d1Scale := hG1Product
      _ <= 100 * key.g2Scale := hordered.le
      _ <= (10 ^ 12) * key.g2Scale := by gcongr; norm_num
  exact_mod_cast hNat

end

end PrimesRestrictedDigits
