import Waring.Analytic.HuaCriticalQuotient

/-!
# Polynomial sums for Hua's normalized-derivative cancellation

This file gives a formal-polynomial complete-sum interface and the exact
Taylor identity used to cancel `t+1` digits in Hua's induction
[HUA1957-BOOK, p. 6].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Complete standard-character sum of an integer formal polynomial. -/
noncomputable def integerFormalPolynomialCompleteSum
    {q : Nat} [NeZero q] (F : Polynomial Int) : Complex :=
  ∑ x : ZMod q,
    ZMod.stdAddChar
      ((F.map (Int.castRingHom (ZMod q))).eval x)

/-- The formal complete sum written using the standard natural
representatives of the residue classes. -/
theorem integerFormalPolynomialCompleteSum_eq_fin
    {q : Nat} [NeZero q] (F : Polynomial Int) :
    integerFormalPolynomialCompleteSum (q := q) F =
      ∑ y : Fin q,
        ZMod.stdAddChar ((F.eval (y.val : Int) : Int) : ZMod q) := by
  rw [integerFormalPolynomialCompleteSum]
  rw [← (ZMod.finEquiv q).toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  apply congrArg ZMod.stdAddChar
  rw [show (ZMod.finEquiv q).toEquiv y =
      ((y.val : Nat) : ZMod q) by
    change ZMod.finEquiv q y = _
    exact zmod_finEquiv_apply y]
  rw [show ((y.val : Nat) : ZMod q) =
      (Int.castRingHom (ZMod q)) (y.val : Int) by simp]
  exact Polynomial.eval_map_apply _ _

/-- The formal-polynomial sum agrees with the existing five-coefficient
interface on Chen's zero-constant quintic. -/
theorem integerFormalPolynomialCompleteSum_fifthPolynomialFormal
    {q : Nat} [NeZero q] (a₀ a₁ a₂ a₃ a₄ : Int) :
    integerFormalPolynomialCompleteSum (q := q)
        (fifthPolynomialFormal a₀ a₁ a₂ a₃ a₄) =
      integerPolynomialCompleteSum (q := q) a₀ a₁ a₂ a₃ a₄ := by
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  simp [fifthPolynomialFormal, fifthPolynomial]

/-- If `n` divides `m`, a shift by `m` has square zero modulo `n*m`. -/
theorem modulusScale_sq_eq_zero (n m : Nat) (hm : n ∣ m)
    (z : ZMod (n * m)) :
    (((m : Nat) : ZMod (n * m)) * z) ^ 2 = 0 := by
  have hzero : (((m * m : Nat) : ZMod (n * m))) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    rcases hm with ⟨c, rfl⟩
    exact ⟨c, by ring⟩
  calc
    (((m : Nat) : ZMod (n * m)) * z) ^ 2 =
        ((m * m : Nat) : ZMod (n * m)) * z ^ 2 := by
      push_cast
      ring
    _ = 0 := by rw [hzero]; simp

/-- Taylor expansion at the `t+1`-digit shift is exactly linear modulo
`p^(t+1)*m` when `p^(t+1)` divides `m`. -/
theorem eval_add_huaDigitScale
    (p t m : Nat) (hm : p ^ (t + 1) ∣ m)
    (F D : Polynomial Int)
    (hderivative :
      F.derivative = Polynomial.C ((p : Int) ^ t) * D)
    (y z : ZMod (p ^ (t + 1) * m)) :
    (F.map (Int.castRingHom (ZMod (p ^ (t + 1) * m)))).eval
        (y + (m : ZMod (p ^ (t + 1) * m)) * z) =
      (F.map (Int.castRingHom (ZMod (p ^ (t + 1) * m)))).eval y +
        (D.map (Int.castRingHom (ZMod (p ^ (t + 1) * m)))).eval y *
          (((p ^ t * m : Nat) : ZMod (p ^ (t + 1) * m)) * z) := by
  have hsquare := modulusScale_sq_eq_zero (p ^ (t + 1)) m hm z
  rw [Polynomial.eval_add_of_sq_eq_zero _ _ _ hsquare]
  rw [Polynomial.derivative_map, hderivative, Polynomial.map_mul]
  simp
  ring

end Waring.Analytic
