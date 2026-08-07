import BoundedGaps.Maynard.MaynardS1StarredFactorization
import BoundedGaps.Maynard.MaynardSquarefreeRoughTail
import Mathlib.Algebra.Order.Ring.Abs

noncomputable section

/-!
# The rough tail over all S1 cross coordinates

The finite cross-coordinate sum is an exact power of the one-coordinate
mass.  Removing the all-one tuple leaves a difference of powers, which keeps
the scalar rough tail's inverse-cutoff decay.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def squarefreeRoughUnitSupport (D Q : ℕ) : Finset ℕ :=
  insert 1 (squarefreeRoughSupport D Q)

def squarefreeRoughUnitMass (D Q : ℕ) : ℝ :=
  ∑ n ∈ squarefreeRoughUnitSupport D Q,
    primeTotientSquareWeight n

theorem one_not_mem_squarefreeRoughSupport (D Q : ℕ) :
    1 ∉ squarefreeRoughSupport D Q := by
  simp [squarefreeRoughSupport]

theorem squarefreeRoughUnitMass_eq (D Q : ℕ) :
    squarefreeRoughUnitMass D Q =
      1 + squarefreeRoughTotientSquareTail D Q := by
  classical
  unfold squarefreeRoughUnitMass squarefreeRoughUnitSupport
    squarefreeRoughTotientSquareTail
  rw [Finset.sum_insert (one_not_mem_squarefreeRoughSupport D Q)]
  norm_num [primeTotientSquareWeight]

theorem squarefreeRoughTotientSquareTail_nonneg (D Q : ℕ) :
    0 ≤ squarefreeRoughTotientSquareTail D Q := by
  unfold squarefreeRoughTotientSquareTail
  apply Finset.sum_nonneg
  intro n hn
  exact primeTotientSquareWeight_nonneg n

theorem one_le_squarefreeRoughUnitMass (D Q : ℕ) :
    1 ≤ squarefreeRoughUnitMass D Q := by
  rw [squarefreeRoughUnitMass_eq]
  exact le_add_of_nonneg_right
    (squarefreeRoughTotientSquareTail_nonneg D Q)

theorem squarefreeRoughUnitMass_nonneg (D Q : ℕ) :
    0 ≤ squarefreeRoughUnitMass D Q :=
  zero_le_one.trans (one_le_squarefreeRoughUnitMass D Q)

theorem squarefreeRoughUnitMass_le_exp_eight
    {D Q : ℕ} (hD : 0 < D) :
    squarefreeRoughUnitMass D Q ≤ Real.exp 8 := by
  let E := ∏ p ∈ roughPrimeSupport D Q,
    (1 + primeTotientSquareWeight p)
  calc
    squarefreeRoughUnitMass D Q =
        1 + squarefreeRoughTotientSquareTail D Q :=
      squarefreeRoughUnitMass_eq D Q
    _ ≤ 1 + (E - 1) := by
      gcongr
      unfold E
      rw [← nonemptySubsetSum_eq_eulerProduct_sub_one]
      exact squarefreeRoughTail_le_nonemptySubsetSum D Q
    _ = E := by ring
    _ ≤ Real.exp 8 := by
      unfold E
      exact roughPrimeEulerProduct_le_exp_eight hD

def roughCrossTupleSupport (H : Finset ℕ) (D Q : ℕ) :
    Finset (∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) :=
  (offDiagonalPairs H).pi fun _ => squarefreeRoughUnitSupport D Q

def crossTotientSquareWeight
    (H : Finset ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) : ℝ :=
  (1 : ℝ) / (crossTotientProduct H s : ℝ) ^ 2

def roughCrossTupleTotientSquareTail
    (H : Finset ℕ) (D Q : ℕ) : ℝ :=
  ∑ s ∈ (roughCrossTupleSupport H D Q).erase
      (oneCrossMoebiusTuple H),
    crossTotientSquareWeight H s

theorem oneCrossMoebiusTuple_mem_roughCrossTupleSupport
    (H : Finset ℕ) (D Q : ℕ) :
    oneCrossMoebiusTuple H ∈ roughCrossTupleSupport H D Q := by
  rw [roughCrossTupleSupport, Finset.mem_pi]
  intro ab hab
  simp [squarefreeRoughUnitSupport, oneCrossMoebiusTuple]

theorem crossTotientSquareWeight_eq_product
    (H : Finset ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) :
    crossTotientSquareWeight H s =
      ∏ x ∈ (offDiagonalPairs H).attach,
        primeTotientSquareWeight (s x.1 x.2) := by
  unfold crossTotientSquareWeight crossTotientProduct
    primeTotientSquareWeight
  push_cast
  rw [← Finset.prod_pow]
  simp only [one_div, Finset.prod_inv_distrib]

theorem crossTotientSquareWeight_one (H : Finset ℕ) :
    crossTotientSquareWeight H (oneCrossMoebiusTuple H) = 1 := by
  simp [crossTotientSquareWeight, crossTotientProduct,
    oneCrossMoebiusTuple]

theorem sum_roughCrossTupleSupport_eq_pow
    (H : Finset ℕ) (D Q : ℕ) :
    (∑ s ∈ roughCrossTupleSupport H D Q,
        crossTotientSquareWeight H s) =
      (squarefreeRoughUnitMass D Q) ^ (offDiagonalPairs H).card := by
  classical
  have hprod := Finset.prod_sum (offDiagonalPairs H)
    (fun _ => squarefreeRoughUnitSupport D Q)
    (fun _ n => primeTotientSquareWeight n)
  calc
    (∑ s ∈ roughCrossTupleSupport H D Q,
        crossTotientSquareWeight H s) =
        ∑ s ∈ roughCrossTupleSupport H D Q,
          ∏ x ∈ (offDiagonalPairs H).attach,
            primeTotientSquareWeight (s x.1 x.2) := by
      apply Finset.sum_congr rfl
      intro s hs
      exact crossTotientSquareWeight_eq_product H s
    _ = ∏ ab ∈ offDiagonalPairs H,
          ∑ n ∈ squarefreeRoughUnitSupport D Q,
            primeTotientSquareWeight n := by
      exact hprod.symm
    _ = ∏ _ab ∈ offDiagonalPairs H,
          squarefreeRoughUnitMass D Q := by
      rfl
    _ = (squarefreeRoughUnitMass D Q) ^
        (offDiagonalPairs H).card := Finset.prod_const _

theorem roughCrossTupleTotientSquareTail_eq_pow_sub_one
    (H : Finset ℕ) (D Q : ℕ) :
    roughCrossTupleTotientSquareTail H D Q =
      (squarefreeRoughUnitMass D Q) ^ (offDiagonalPairs H).card - 1 := by
  have hone := oneCrossMoebiusTuple_mem_roughCrossTupleSupport H D Q
  have hsplit := Finset.sum_erase_add
    (s := roughCrossTupleSupport H D Q)
    (f := crossTotientSquareWeight H) hone
  rw [crossTotientSquareWeight_one,
    sum_roughCrossTupleSupport_eq_pow] at hsplit
  unfold roughCrossTupleTotientSquareTail
  linarith

theorem roughCrossTupleTotientSquareTail_le
    {H : Finset ℕ} {D Q : ℕ} (hD : 0 < D) :
    roughCrossTupleTotientSquareTail H D Q ≤
      (8 * Real.exp 8 / (D : ℝ)) *
        ((offDiagonalPairs H).card : ℝ) *
          (Real.exp 8) ^ ((offDiagonalPairs H).card - 1) := by
  let M := squarefreeRoughUnitMass D Q
  let m := (offDiagonalPairs H).card
  have hMone : 1 ≤ M := one_le_squarefreeRoughUnitMass D Q
  have hMnonneg : 0 ≤ M := squarefreeRoughUnitMass_nonneg D Q
  have hMexp : M ≤ Real.exp 8 := squarefreeRoughUnitMass_le_exp_eight hD
  have hMtail : M - 1 ≤ 8 * Real.exp 8 / (D : ℝ) := by
    unfold M
    rw [squarefreeRoughUnitMass_eq]
    simpa using squarefreeRoughTotientSquareTail_le (Q := Q) hD
  have hpow := abs_pow_sub_pow_le (a := M) (b := (1 : ℝ)) (n := m)
  have hMpow : 1 ≤ M ^ m := one_le_pow₀ hMone
  norm_num only [one_pow] at hpow
  rw [abs_of_nonneg (sub_nonneg.mpr hMpow),
    abs_of_nonneg (sub_nonneg.mpr hMone), abs_of_nonneg hMnonneg,
    max_eq_left hMone] at hpow
  have hpowExp : M ^ (m - 1) ≤ (Real.exp 8) ^ (m - 1) :=
    pow_le_pow_left₀ hMnonneg hMexp _
  have hconstantNonneg : 0 ≤
      (8 * Real.exp 8 / (D : ℝ)) * (m : ℝ) := by positivity
  calc
    roughCrossTupleTotientSquareTail H D Q = M ^ m - 1 := by
      exact roughCrossTupleTotientSquareTail_eq_pow_sub_one H D Q
    _ ≤ (M - 1) * (m : ℝ) * M ^ (m - 1) := hpow
    _ ≤ (8 * Real.exp 8 / (D : ℝ)) *
        (m : ℝ) * M ^ (m - 1) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right hMtail (Nat.cast_nonneg m)
      · positivity
    _ ≤ (8 * Real.exp 8 / (D : ℝ)) *
        (m : ℝ) * (Real.exp 8) ^ (m - 1) := by
      exact mul_le_mul_of_nonneg_left hpowExp hconstantNonneg

end BoundedGaps.Maynard
