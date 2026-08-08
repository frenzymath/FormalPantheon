import Waring.Analytic.LinearPhaseBound
import Waring.Analytic.WeylDifferenceInequality
import Waring.Analytic.WeylQuadraticPhase

/-!
# The fourth-difference bound for a quadratic fifth-power phase

This file turns each shifted quadratic correlation into a zero-safe linear
Fourier coefficient.
-/

namespace Waring.Analytic

open scoped BigOperators ComplexConjugate

/-- A zero-based sum of a linear standard character is the interval Fourier
coefficient on the positive integer interval of the same length. -/
theorem sum_range_stdAddChar_mul_succ_eq_intervalFourierCoefficient
    {q : Nat} [NeZero q] (frequency : ZMod q) (m : Nat) :
    (∑ y ∈ Finset.range m,
        ZMod.stdAddChar (frequency * ((y + 1 : Nat) : ZMod q))) =
      intervalFourierCoefficient 0 m (-frequency) := by
  unfold intervalFourierCoefficient
  rw [Int.Ioc_eq_finset_map]
  simp [add_comm]

/-- The frequency of the linear character after the fourth positive shift. -/
def fifthQuadraticFrequency {q : Nat} (a : ZMod q)
    (h₁ h₂ h₃ l : Nat) : ZMod q :=
  a * (120 * (h₁ : ZMod q) * (h₂ : ZMod q) * (h₃ : ZMod q) *
    (l : ZMod q))

/-- The norm square of a quadratic third-difference sum is bounded by the
sum of zero-safe linear weights over all positive fourth shifts. -/
theorem norm_fifthQuadraticSum_sq_le
    {q : Nat} [NeZero q] (a : ZMod q) (h₁ h₂ h₃ n P : Nat)
    (hnP : n ≤ P) :
    ‖∑ y ∈ Finset.range n, fifthQuadraticChar a h₁ h₂ h₃ (y + 1)‖ ^ 2 ≤
      n + 2 * ∑ h ∈ Finset.range n,
        diophantineMinWeight q P
          (-fifthQuadraticFrequency a h₁ h₂ h₃ (h + 1)) := by
  let z : Nat → Complex := fun y ↦ fifthQuadraticChar a h₁ h₂ h₃ (y + 1)
  have hz : ∀ y < n, ‖z y‖ = 1 := by
    intro y _
    dsimp [z, fifthQuadraticChar]
    norm_num
  have hbase := norm_sum_range_sq_le_sum_shiftCorrelation z n hz
  calc
    ‖∑ y ∈ Finset.range n, fifthQuadraticChar a h₁ h₂ h₃ (y + 1)‖ ^ 2 ≤
        n + 2 * ∑ h ∈ Finset.range n,
          ‖∑ y ∈ Finset.range (n - h - 1),
            z (y + h + 1) * conj (z y)‖ := by
      simpa [z] using hbase
    _ ≤ n + 2 * ∑ h ∈ Finset.range n,
        diophantineMinWeight q P
          (-fifthQuadraticFrequency a h₁ h₂ h₃ (h + 1)) := by
      gcongr with h hh
      have hhn : h < n := Finset.mem_range.mp hh
      let l := h + 1
      let m := n - h - 1
      let constant : ZMod q :=
        a * (60 * (h₁ : ZMod q) * (h₂ : ZMod q) * (h₃ : ZMod q) *
          (l : ZMod q) * ((h₁ : ZMod q) + (h₂ : ZMod q) +
            (h₃ : ZMod q) + (l : ZMod q)))
      let frequency := fifthQuadraticFrequency a h₁ h₂ h₃ l
      have hcorrelation :
          (∑ y ∈ Finset.range m, z (y + h + 1) * conj (z y)) =
            ZMod.stdAddChar constant *
              intervalFourierCoefficient 0 m (-frequency) := by
        calc
          (∑ y ∈ Finset.range m, z (y + h + 1) * conj (z y)) =
              ∑ y ∈ Finset.range m,
                ZMod.stdAddChar constant *
                  ZMod.stdAddChar (frequency * ((y + 1 : Nat) : ZMod q)) := by
            apply Finset.sum_congr rfl
            intro y _
            dsimp [z, l, constant, frequency, fifthQuadraticFrequency]
            rw [show y + h + 1 + 1 = (y + 1) + (h + 1) by omega]
            simpa [mul_assoc] using
              fifthQuadraticChar_mul_conj a h₁ h₂ h₃ (y + 1) (h + 1)
          _ = ZMod.stdAddChar constant *
              ∑ y ∈ Finset.range m,
                ZMod.stdAddChar (frequency * ((y + 1 : Nat) : ZMod q)) := by
            rw [Finset.mul_sum]
          _ = ZMod.stdAddChar constant *
              intervalFourierCoefficient 0 m (-frequency) := by
            rw [sum_range_stdAddChar_mul_succ_eq_intervalFourierCoefficient]
      rw [show n - h - 1 = m by rfl, hcorrelation, norm_mul]
      have hconstantNorm : ‖ZMod.stdAddChar constant‖ = 1 := by norm_num
      rw [hconstantNorm, one_mul]
      exact norm_intervalFourierCoefficient_le_diophantineMinWeight
        0 m P (by omega) (-frequency)

/-- Extending the diagonal and positive-shift ranges to the ambient length
`P` gives Chen's zero-safe form of equation (13). -/
theorem norm_fifthQuadraticSum_sq_le_full
    {q : Nat} [NeZero q] (a : ZMod q) (h₁ h₂ h₃ n P : Nat)
    (hnP : n ≤ P) :
    ‖∑ y ∈ Finset.range n, fifthQuadraticChar a h₁ h₂ h₃ (y + 1)‖ ^ 2 ≤
      P + 2 * ∑ h ∈ Finset.range P,
        diophantineMinWeight q P
          (-fifthQuadraticFrequency a h₁ h₂ h₃ (h + 1)) := by
  calc
    ‖∑ y ∈ Finset.range n, fifthQuadraticChar a h₁ h₂ h₃ (y + 1)‖ ^ 2 ≤
        n + 2 * ∑ h ∈ Finset.range n,
          diophantineMinWeight q P
            (-fifthQuadraticFrequency a h₁ h₂ h₃ (h + 1)) :=
      norm_fifthQuadraticSum_sq_le a h₁ h₂ h₃ n P hnP
    _ ≤ P + 2 * ∑ h ∈ Finset.range P,
        diophantineMinWeight q P
          (-fifthQuadraticFrequency a h₁ h₂ h₃ (h + 1)) := by
      apply add_le_add
      · exact_mod_cast hnP
      · apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono hnP) fun h _ _ ↦
              diophantineMinWeight_nonneg q P
                (-fifthQuadraticFrequency a h₁ h₂ h₃ (h + 1))
        · norm_num

end Waring.Analytic
