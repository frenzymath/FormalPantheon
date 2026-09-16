import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Character sums from one-sided finite-fiber bounds

If every fiber is at most `A + E`, while the total cardinality is exactly
`card(Y) * A`, subtracting the fiber sizes from the common upper bound gives
nonnegative deficiencies of total size `card(Y) * E`.  A mean-zero bounded
weight therefore gives a sum of norm at most that total deficiency.
 -/

namespace Waring.Analytic

open scoped BigOperators

/-- A one-sided uniform fiber bound controls every mean-zero bounded weighted
sum over the source. -/
theorem norm_fintype_sum_comp_le_of_card_fiber_le
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (g : X → Y) (weight : Y → Complex) (A E : Nat)
    (hfiber : ∀ y : Y,
      (Finset.univ.filter fun x : X ↦ g x = y).card ≤ A + E)
    (hcard : Fintype.card X = Fintype.card Y * A)
    (hmean : ∑ y : Y, weight y = 0)
    (hweight : ∀ y : Y, ‖weight y‖ ≤ 1) :
    ‖∑ x : X, weight (g x)‖ ≤ (Fintype.card Y * E : Nat) := by
  classical
  let N : Y → Nat := fun y ↦
    (Finset.univ.filter fun x : X ↦ g x = y).card
  have hN (y : Y) : N y ≤ A + E := hfiber y
  have hNsum : ∑ y : Y, N y = Fintype.card X := by
    have hpartition := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset X)) (t := (Finset.univ : Finset Y))
      (f := g) (by intro x hx; simp)
    simpa only [Finset.card_univ, N] using hpartition.symm
  have hdefsum : ∑ y : Y, (A + E - N y) = Fintype.card Y * E := by
    rw [Finset.sum_tsub_distrib]
    · have hconst :
          (∑ _y : Y, (A + E)) = Fintype.card Y * (A + E) := by simp
      rw [hconst, hNsum, hcard]
      calc
        Fintype.card Y * (A + E) - Fintype.card Y * A =
            Fintype.card Y * (A + E - A) :=
          (Nat.mul_sub_left_distrib _ _ _).symm
        _ = Fintype.card Y * E := by simp
    · intro y hy
      exact hN y
  have hgroup :
      (∑ x : X, weight (g x)) =
        ∑ y : Y, (N y : Complex) * weight y := by
    rw [← Finset.sum_fiberwise' (Finset.univ : Finset X) g weight]
    apply Finset.sum_congr rfl
    intro y hy
    simp only [Finset.sum_const, nsmul_eq_mul, N]
  have hrecenter :
      (∑ y : Y, (N y : Complex) * weight y) =
        -∑ y : Y, ((A + E - N y : Nat) : Complex) * weight y := by
    calc
      (∑ y : Y, (N y : Complex) * weight y) =
          ∑ y : Y, (
            ((A + E : Nat) : Complex) * weight y -
              ((A + E - N y : Nat) : Complex) * weight y) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Nat.cast_sub (hN y)]
        ring
      _ = ((A + E : Nat) : Complex) * (∑ y : Y, weight y) -
          ∑ y : Y,
            ((A + E - N y : Nat) : Complex) * weight y := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = -∑ y : Y,
          ((A + E - N y : Nat) : Complex) * weight y := by
        rw [hmean]
        simp
  rw [hgroup, hrecenter, norm_neg]
  calc
    ‖∑ y : Y, ((A + E - N y : Nat) : Complex) * weight y‖ ≤
        ∑ y : Y,
          ‖((A + E - N y : Nat) : Complex) * weight y‖ :=
      norm_sum_le _ _
    _ ≤ ∑ y : Y, ((A + E - N y : Nat) : Real) := by
      apply Finset.sum_le_sum
      intro y hy
      rw [norm_mul, Complex.norm_natCast]
      simpa using mul_le_mul_of_nonneg_left (hweight y)
        (Nat.cast_nonneg (A + E - N y))
    _ = (Fintype.card Y * E : Nat) := by
      exact_mod_cast hdefsum

end Waring.Analytic
