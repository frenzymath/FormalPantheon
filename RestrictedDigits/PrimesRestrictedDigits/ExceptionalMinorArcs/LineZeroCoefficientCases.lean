import PrimesRestrictedDigits.ExceptionalMinorArcs.LineZeroCoefficientWitnesses
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The four zero-coefficient witness cases

This separates the four coordinate branches hidden by "entirely analogous"
in `MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 210--211.
-/

namespace PrimesRestrictedDigits

/-- Positive zero-coefficient witnesses whose first relation coefficient is
zero. -/
noncomputable def zeroFirstCoefficientPlaneWitnesses {X : Nat}
    (C : Finset (Fin X)) (V : Real) :
    Finset (LowHeightPlaneWitness X) :=
  (positiveZeroCoefficientPlaneWitnesses C V).filter fun w =>
    w.v 0 = 0

/-- Positive zero-coefficient witnesses whose second relation coefficient is
zero. -/
noncomputable def zeroSecondCoefficientPlaneWitnesses {X : Nat}
    (C : Finset (Fin X)) (V : Real) :
    Finset (LowHeightPlaneWitness X) :=
  (positiveZeroCoefficientPlaneWitnesses C V).filter fun w =>
    w.v 1 = 0

/-- Positive zero-coefficient witnesses whose scale coefficient is zero. -/
noncomputable def zeroThirdCoefficientPlaneWitnesses {X : Nat}
    (C : Finset (Fin X)) (V : Real) :
    Finset (LowHeightPlaneWitness X) :=
  (positiveZeroCoefficientPlaneWitnesses C V).filter fun w =>
    w.v 2 = 0

/-- Positive zero-coefficient witnesses whose constant coefficient is zero. -/
noncomputable def zeroFourthCoefficientPlaneWitnesses {X : Nat}
    (C : Finset (Fin X)) (V : Real) :
    Finset (LowHeightPlaneWitness X) :=
  (positiveZeroCoefficientPlaneWitnesses C V).filter fun w =>
    w.v4 = 0

/-- The zero-coefficient witness carrier is covered by its four coordinate
filters. -/
theorem positiveZeroCoefficientPlaneWitnesses_eq_union_cases
    {X : Nat} (C : Finset (Fin X)) (V : Real) :
    positiveZeroCoefficientPlaneWitnesses C V =
      (((zeroFirstCoefficientPlaneWitnesses C V ∪
          zeroSecondCoefficientPlaneWitnesses C V) ∪
        zeroThirdCoefficientPlaneWitnesses C V) ∪
        zeroFourthCoefficientPlaneWitnesses C V) := by
  classical
  ext w
  simp only [zeroFirstCoefficientPlaneWitnesses,
    zeroSecondCoefficientPlaneWitnesses,
    zeroThirdCoefficientPlaneWitnesses,
    zeroFourthCoefficientPlaneWitnesses, Finset.mem_filter,
    Finset.mem_union]
  constructor
  · intro hw
    rcases (mem_positiveZeroCoefficientPlaneWitnesses.mp hw).2.2 with
      hzero | hzero | hzero | hzero
    · exact Or.inl (Or.inl (Or.inl ⟨hw, hzero⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hw, hzero⟩))
    · exact Or.inl (Or.inr ⟨hw, hzero⟩)
    · exact Or.inr ⟨hw, hzero⟩
  · rintro (((⟨hw, _⟩ | ⟨hw, _⟩) | ⟨hw, _⟩) | ⟨hw, _⟩) <;>
      exact hw

/-- An integral multiple of `X` and a bounded error cannot cancel below the
scale `X` unless both coefficients vanish. -/
theorem eq_zero_of_mul_scale_add_eq_zero
    {X : Nat} {V : Real} {u t : Int}
    (_hV : 0 <= V) (hVX : V < (X : Real))
    (hu : abs (u : Real) <= V) (ht : abs (t : Real) <= V)
    (hrel : u * (X : Int) + t = 0) :
    And (u = 0) (t = 0) := by
  by_cases huZero : u = 0
  · subst u
    simp only [zero_mul, zero_add] at hrel
    exact ⟨rfl, hrel⟩
  · have huNat : 1 <= u.natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr huZero)
    have huCast : (1 : Real) <= (u.natAbs : Real) := by
      exact_mod_cast huNat
    have huOne : (1 : Real) <= abs (u : Real) := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using huCast
    have hXPos : (0 : Real) < X := by linarith
    have htEq : t = -u * (X : Int) := by linear_combination hrel
    have hXle : (X : Real) <= abs (t : Real) := by
      calc
        (X : Real) = 1 * X := by ring
        _ <= abs (u : Real) * X := by gcongr
        _ = abs ((u : Real) * X) := by
          rw [abs_mul, abs_of_pos hXPos]
        _ = abs (t : Real) := by
          rw [htEq]
          push_cast
          rw [neg_mul, abs_neg]
    linarith

/-- Every signed target formed from three bounded source terms has one fixed
quadratic outer-scale envelope. -/
theorem lineZeroTermTarget_natAbs_le_three_mul_sq
    {X : Nat} {V : Real} (a : Fin X) (u w t : Int)
    (hV : 0 <= V) (hVX : V < (X : Real))
    (hu : abs (u : Real) <= V) (hw : abs (w : Real) <= V)
    (ht : abs (t : Real) <= V) :
    ((u * (a.val : Int) + w * (X : Int) + t).natAbs : Real) <=
      3 * ((X : Real) ^ 2) := by
  have hXNat : 1 <= X := Nat.one_le_iff_ne_zero.mpr (by
    intro hX
    subst X
    exact Fin.elim0 a)
  have hXOne : (1 : Real) <= X := by exact_mod_cast hXNat
  have ha : (a.val : Real) <= X := by exact_mod_cast a.isLt.le
  have hVle : V <= (X : Real) := hVX.le
  rw [Nat.cast_natAbs, Int.cast_abs]
  push_cast
  calc
    abs ((u : Real) * a.val + (w : Real) * X + t) <=
        abs ((u : Real) * a.val) + abs ((w : Real) * X) +
          abs (t : Real) := abs_add_three _ _ _
    _ = abs (u : Real) * a.val + abs (w : Real) * X +
        abs (t : Real) := by
      rw [abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : Real) <= a.val),
        abs_of_nonneg (by positivity : (0 : Real) <= X)]
    _ <= V * X + V * X + V := by gcongr
    _ <= X * X + X * X + X := by gcongr
    _ <= 3 * X ^ 2 := by nlinarith

private theorem card_zeroElements_le_one
    {X : Nat} (C : Finset (Fin X)) :
    (C.filter fun a => a.val = 0).card <= 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  apply Fin.ext
  exact (Finset.mem_filter.mp ha).2.trans
    (Finset.mem_filter.mp hb).2.symm

/-- There are at most `2*#C` ordered pairs in `C^2` having a zero member. -/
theorem card_zeroElementPlanePairCover_le
    {X : Nat} (C : Finset (Fin X)) :
    (zeroElementPlanePairCover C).card <= 2 * C.card := by
  classical
  let Czero := C.filter fun a => a.val = 0
  have hzero : Czero.card <= 1 := card_zeroElements_le_one C
  calc
    (zeroElementPlanePairCover C).card <=
        (Czero.product C).card + (C.product Czero).card := by
      simpa only [zeroElementPlanePairCover, Czero] using
        Finset.card_union_le (Czero.product C) (C.product Czero)
    _ = Czero.card * C.card + C.card * Czero.card := by
      simp only [Finset.product_eq_sprod, Finset.card_product]
    _ <= 1 * C.card + C.card * 1 := by gcongr
    _ = 2 * C.card := by ring

end PrimesRestrictedDigits
