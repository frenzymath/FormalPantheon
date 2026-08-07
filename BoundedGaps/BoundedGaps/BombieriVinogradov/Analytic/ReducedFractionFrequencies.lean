import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.ZMod.Units

/-!
# Reduced-fraction frequencies on the additive unit circle

This file indexes the reduced fractions with denominator at most `Q`, embeds
them in `ℝ / ℤ`, and proves their exact `Q⁻²` separation. It also identifies
the positive-sign circle character with `ZMod.stdAddChar`. See SEM-444 and
MontgomeryVaughanLargeSieve1973, p. 123.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Positive natural moduli bounded above by `Q`. -/
abbrev positiveModuliUpTo (Q : ℕ) :=
  {q : ℕ // q ∈ Finset.Icc 1 Q}

/-- Reduced residue classes for every positive modulus at most `Q`. -/
abbrev reducedFractionIndices (Q : ℕ) :=
  Σ q : positiveModuliUpTo Q, (ZMod q.1)ˣ

/-- The bounded collection of reduced-fraction indices is finite. -/
noncomputable instance reducedFractionIndicesFintype (Q : ℕ) :
    Fintype (reducedFractionIndices Q) := Fintype.ofFinite _

/-- Every modulus occurring in a reduced-fraction index is nonzero. -/
instance positiveModulusNeZero {Q : ℕ}
    (q : positiveModuliUpTo Q) : NeZero q.1 := ⟨by
  have hq := q.2
  simp only [Finset.mem_Icc] at hq
  omega⟩

/-- The point `u / q` in `ℝ / ℤ` attached to a reduced residue `u mod q`. -/
noncomputable def reducedFractionPoint {Q : ℕ}
    (x : reducedFractionIndices Q) : UnitAddCircle :=
  ZMod.toAddCircle (x.2 : ZMod x.1.1)

/-- The standard positive-sign additive character on `ℝ / ℤ`. -/
noncomputable def unitAddCircleAddChar : AddChar UnitAddCircle ℂ :=
  Circle.coeHom.compAddChar AddCircle.toCircle_addChar

/-- Evaluating the circle character at `n * (u/q)` gives `e_q(u*n)`. -/
theorem unitAddCircleAddChar_nsmul_reducedFractionPoint
    {Q : ℕ} (x : reducedFractionIndices Q) (n : ℕ) :
    unitAddCircleAddChar (n • reducedFractionPoint x) =
      ZMod.stdAddChar ((x.2 : ZMod x.1.1) * (n : ZMod x.1.1)) := by
  calc
    unitAddCircleAddChar (n • reducedFractionPoint x) =
        unitAddCircleAddChar (reducedFractionPoint x) ^ n :=
      AddChar.map_nsmul_eq_pow _ _ _
    _ = ZMod.stdAddChar (x.2 : ZMod x.1.1) ^ n := by
      rfl
    _ = ZMod.stdAddChar (n • (x.2 : ZMod x.1.1)) := by
      rw [AddChar.map_nsmul_eq_pow]
    _ = ZMod.stdAddChar
        ((x.2 : ZMod x.1.1) * (n : ZMod x.1.1)) := by
      congr 1
      simp [nsmul_eq_mul, mul_comm]

private theorem addOrderOf_coe_unit {q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) :
    addOrderOf (u : ZMod q) = q := by
  rw [← ZMod.natCast_zmod_val (u : ZMod q)]
  rw [ZMod.addOrderOf_coe (u : ZMod q).val (NeZero.ne q)]
  have hu := ZMod.val_coe_unit_coprime u
  rw [Nat.gcd_comm, hu.gcd_eq_one, Nat.div_one]

/-- A reduced point with denominator `q` has exact additive order `q`. -/
theorem addOrderOf_reducedFractionPoint {Q : ℕ}
    (x : reducedFractionIndices Q) :
    addOrderOf (reducedFractionPoint x) = x.1.1 := by
  apply Nat.dvd_antisymm
  · rw [← addOrderOf_coe_unit x.2]
    exact addOrderOf_map_dvd ZMod.toAddCircle (x.2 : ZMod x.1.1)
  · rw [← addOrderOf_coe_unit x.2,
      addOrderOf_dvd_iff_nsmul_eq_zero]
    apply ZMod.toAddCircle_injective x.1.1
    rw [AddMonoidHom.map_nsmul, map_zero]
    rw [show ZMod.toAddCircle (x.2 : ZMod x.1.1) =
      reducedFractionPoint x by rfl]
    rw [addOrderOf_nsmul_eq_zero]

/-- Distinct reduced-fraction indices give distinct points of `ℝ / ℤ`. -/
theorem reducedFractionPoint_injective {Q : ℕ} :
    Function.Injective
      (reducedFractionPoint : reducedFractionIndices Q → UnitAddCircle) := by
  intro x y hxy
  have hq : x.1.1 = y.1.1 := by
    rw [← addOrderOf_reducedFractionPoint x,
      ← addOrderOf_reducedFractionPoint y, hxy]
  rcases x with ⟨q, u⟩
  rcases y with ⟨r, v⟩
  have hqr : q = r := Subtype.ext hq
  subst r
  have huv : u = v := by
    apply Units.ext
    apply ZMod.toAddCircle_injective q.1
    exact hxy
  subst v
  exact Sigma.ext_iff.mpr ⟨rfl, HEq.rfl⟩

/-- Distinct reduced fractions of denominator at most `Q` are `Q⁻²`-separated. -/
theorem one_div_sq_le_dist_reducedFractionPoint
    {Q : ℕ} {x y : reducedFractionIndices Q} (hxy : x ≠ y) :
    (1 : ℝ) / (Q : ℝ) ^ 2 ≤
      dist (reducedFractionPoint x) (reducedFractionPoint y) := by
  have hxq := x.1.2
  have hyq := y.1.2
  simp only [Finset.mem_Icc] at hxq hyq
  have hQ : 0 < Q := by omega
  have hxzero : x.1.1 • reducedFractionPoint x = 0 := by
    rw [← addOrderOf_reducedFractionPoint x, addOrderOf_nsmul_eq_zero]
  have hyzero : y.1.1 • reducedFractionPoint y = 0 := by
    rw [← addOrderOf_reducedFractionPoint y, addOrderOf_nsmul_eq_zero]
  have hproduct :
      (x.1.1 * y.1.1) •
          (reducedFractionPoint x - reducedFractionPoint y) = 0 := by
    rw [nsmul_sub]
    rw [mul_nsmul, hxzero, nsmul_zero]
    rw [mul_comm, mul_nsmul, hyzero, nsmul_zero, sub_zero]
  have hproduct_pos : 0 < x.1.1 * y.1.1 := Nat.mul_pos hxq.1 hyq.1
  have hfinite :
      IsOfFinAddOrder (reducedFractionPoint x - reducedFractionPoint y) :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨x.1.1 * y.1.1, hproduct_pos, hproduct⟩
  have hdiff : reducedFractionPoint x - reducedFractionPoint y ≠ 0 :=
    sub_ne_zero.mpr (reducedFractionPoint_injective.ne hxy)
  have horder :
      addOrderOf (reducedFractionPoint x - reducedFractionPoint y) ≤
        x.1.1 * y.1.1 :=
    addOrderOf_le_of_nsmul_eq_zero hproduct_pos hproduct
  have hunit :
      (1 : ℝ) ≤
        (addOrderOf
          (reducedFractionPoint x - reducedFractionPoint y) : ℝ) *
          ‖reducedFractionPoint x - reducedFractionPoint y‖ := by
    simpa [nsmul_eq_mul] using
      AddCircle.le_add_order_smul_norm_of_isOfFinAddOrder hfinite hdiff
  rw [dist_eq_norm]
  rw [div_le_iff₀ (sq_pos_of_pos (Nat.cast_pos.mpr hQ))]
  calc
    (1 : ℝ) ≤
        (addOrderOf
          (reducedFractionPoint x - reducedFractionPoint y) : ℝ) *
          ‖reducedFractionPoint x - reducedFractionPoint y‖ := hunit
    _ ≤ ((x.1.1 * y.1.1 : ℕ) : ℝ) *
          ‖reducedFractionPoint x - reducedFractionPoint y‖ := by
      gcongr
    _ ≤ (Q : ℝ) ^ 2 *
          ‖reducedFractionPoint x - reducedFractionPoint y‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      norm_cast
      nlinarith
    _ = ‖reducedFractionPoint x - reducedFractionPoint y‖ *
          (Q : ℝ) ^ 2 := by ring

end

end BoundedGaps.Maynard
