import PrimesRestrictedDigits.Fourier.IncomingPath
import Mathlib.Algebra.BigOperators.Fin

/-!
# Fixed-length digit-word products

The incoming path recurrence peels the terminal free digit first. This file
reindexes the resulting paths by forward words and their concatenated suffix
windows, using commutativity of real multiplication for the factor order.
-/

open scoped BigOperators Matrix

namespace PrimesRestrictedDigits

def concatenatedDigitWord {steps length : ℕ}
    (word : DigitWindowState steps) (future : DigitWindowState length) :
    Fin (steps + length) → Fin 10 :=
  Fin.append word future

def concatenatedDigitWindow {steps length : ℕ}
    (word : DigitWindowState steps) (future : DigitWindowState length)
    (start : Fin steps) : Fin (length + 1) → Fin 10 :=
  fun offset => concatenatedDigitWord word future
    ⟨(start : ℕ) + (offset : ℕ), by omega⟩

theorem concatenatedDigitWindow_append_last {steps length : ℕ}
    (word : DigitWindowState steps) (last : Fin 10)
    (future : DigitWindowState length) :
    concatenatedDigitWindow (appendDigitWindow word last) future
        (Fin.last steps) =
      prependDigitWindow last future := by
  funext offset
  refine Fin.cases ?_ (fun j => ?_) offset
  · unfold concatenatedDigitWindow concatenatedDigitWord
    simp only [Fin.val_zero, Nat.add_zero]
    have hindex :
        (⟨((Fin.last steps : Fin (steps + 1)) : ℕ), by omega⟩ :
          Fin ((steps + 1) + length)) =
            Fin.castAdd length (Fin.last steps) := by
      apply Fin.ext
      rfl
    rw [hindex, Fin.append_left]
    simp [appendDigitWindow, prependDigitWindow]
  · unfold concatenatedDigitWindow concatenatedDigitWord
      prependDigitWindow
    have hindex :
        (⟨((Fin.last steps : Fin (steps + 1)) : ℕ) +
            ((Fin.succ j : Fin (length + 1)) : ℕ), by omega⟩ :
          Fin ((steps + 1) + length)) =
            Fin.natAdd (steps + 1) j := by
      apply Fin.ext
      simp
      omega
    rw [hindex, Fin.append_right]
    simp

theorem concatenatedDigitWindow_append_castSucc {steps length : ℕ}
    (word : DigitWindowState steps) (last : Fin 10)
    (future : DigitWindowState length) (start : Fin steps) :
    concatenatedDigitWindow (appendDigitWindow word last) future
        start.castSucc =
      concatenatedDigitWindow word
        (digitWindowPrefix (prependDigitWindow last future)) start := by
  funext offset
  unfold concatenatedDigitWindow concatenatedDigitWord
  simp only [Fin.val_castSucc]
  by_cases hlt : (start : ℕ) + (offset : ℕ) < steps
  · let q : Fin steps := ⟨(start : ℕ) + (offset : ℕ), hlt⟩
    let q' : Fin (steps + 1) :=
      ⟨(start : ℕ) + (offset : ℕ), by omega⟩
    have hleft :
        (⟨(start : ℕ) + (offset : ℕ), by omega⟩ :
          Fin ((steps + 1) + length)) = Fin.castAdd length q' := by
      apply Fin.ext
      rfl
    have hright :
        (⟨(start : ℕ) + (offset : ℕ), by omega⟩ :
          Fin (steps + length)) = Fin.castAdd length q := by
      apply Fin.ext
      rfl
    rw [hleft, Fin.append_left, hright, Fin.append_left]
    have hq : q' = q.castSucc := by
      apply Fin.ext
      rfl
    rw [hq]
    simp [appendDigitWindow]
  · by_cases heq : (start : ℕ) + (offset : ℕ) = steps
    · let qlast : Fin (steps + 1) := Fin.last steps
      let jzero : Fin length := ⟨0, by omega⟩
      have hleft :
          (⟨(start : ℕ) + (offset : ℕ), by omega⟩ :
            Fin ((steps + 1) + length)) = Fin.castAdd length qlast := by
        apply Fin.ext
        simp [qlast, heq]
      have hright :
          (⟨(start : ℕ) + (offset : ℕ), by omega⟩ :
            Fin (steps + length)) = Fin.natAdd steps jzero := by
        apply Fin.ext
        simp [jzero, heq]
      rw [hleft, Fin.append_left, hright, Fin.append_right]
      dsimp [qlast]
      simp [appendDigitWindow, prependDigitWindow, digitWindowPrefix, jzero]
    · let jleft : Fin length :=
        ⟨(start : ℕ) + (offset : ℕ) - (steps + 1), by omega⟩
      let jright : Fin length :=
        ⟨(start : ℕ) + (offset : ℕ) - steps, by omega⟩
      have hleft :
          (⟨(start : ℕ) + (offset : ℕ), by omega⟩ :
            Fin ((steps + 1) + length)) =
              Fin.natAdd (steps + 1) jleft := by
        apply Fin.ext
        simp [jleft]
        omega
      have hright :
          (⟨(start : ℕ) + (offset : ℕ), by omega⟩ :
            Fin (steps + length)) = Fin.natAdd steps jright := by
        apply Fin.ext
        simp [jright]
        omega
      rw [hleft, Fin.append_right, hright, Fin.append_right]
      unfold digitWindowPrefix
      have hshift : jright.castSucc = jleft.succ := by
        apply Fin.ext
        simp [jleft, jright]
        omega
      rw [hshift]
      simp [prependDigitWindow]

def digitWordPathProduct {steps length : ℕ}
    (weight : (Fin (length + 1) → Fin 10) → ℝ)
    (word : DigitWindowState steps) (future : DigitWindowState length) : ℝ :=
  ∏ start : Fin steps,
    weight (concatenatedDigitWindow word future start)

theorem digitWordPathProduct_append {steps length : ℕ}
    (weight : (Fin (length + 1) → Fin 10) → ℝ)
    (word : DigitWindowState steps) (last : Fin 10)
    (future : DigitWindowState length) :
    digitWordPathProduct weight (appendDigitWindow word last) future =
      weight (prependDigitWindow last future) *
        digitWordPathProduct weight word
          (digitWindowPrefix (prependDigitWindow last future)) := by
  unfold digitWordPathProduct
  rw [Fin.prod_univ_castSucc]
  rw [mul_comm]
  apply congrArg₂ (· * ·)
  · rw [concatenatedDigitWindow_append_last]
  · apply Finset.prod_congr rfl
    intro start hstart
    rw [concatenatedDigitWindow_append_castSucc]

theorem digitWordPathSum_eq_sum_wordProduct {steps length : ℕ}
    (weight : (Fin (length + 1) → Fin 10) → ℝ)
    (future : DigitWindowState length) :
    digitWordPathSum weight steps future =
      ∑ word : DigitWindowState steps,
        digitWordPathProduct weight word future := by
  induction steps generalizing future with
  | zero =>
      rw [digitWordPathSum]
      simp [digitWordPathProduct]
  | succ steps ih =>
      rw [digitWordPathSum]
      simp_rw [ih]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      rw [← Finset.sum_product']
      have hsum :
          (∑ pair : DigitWindowState steps × Fin 10,
            weight (prependDigitWindow pair.2 future) *
              digitWordPathProduct weight pair.1
                (digitWindowPrefix
                  (prependDigitWindow pair.2 future))) =
            ∑ word : DigitWindowState (steps + 1),
              digitWordPathProduct weight word future := by
        apply Fintype.sum_equiv (appendDigitWindowEquiv steps)
        intro pair
        exact (digitWordPathProduct_append weight pair.1 pair.2 future).symm
      simpa only [Finset.univ_product_univ] using hsum

end PrimesRestrictedDigits
