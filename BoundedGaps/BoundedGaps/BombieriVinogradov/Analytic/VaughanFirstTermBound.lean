import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveConductorFibers
import BoundedGaps.BombieriVinogradov.Analytic.VaughanTwistedDecomposition
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Vaughan's first-term bound

This file proves the natural-endpoint version of Akbary--Hambrook2013v2,
equation (6.7). The final bound uses Mathlib's verified Chebyshev constant
`log 4 + 4`, not the source's sharper constant `A_0`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt

noncomputable section

/-- The first twisted Vaughan term is bounded by its nonnegative coefficient
sum. -/
theorem norm_vaughanTwistedSumOne_le_cutoffSum
    (U : ℝ) (y q : ℕ) (χ : DirichletCharacter ℂ q) :
    ‖vaughanTwistedSumOne U y q χ‖ ≤
      ∑ n ∈ (Finset.Icc 1 y).filter (fun n : ℕ ↦ (n : ℝ) ≤ U),
        ArithmeticFunction.vonMangoldt n := by
  unfold vaughanTwistedSumOne
  calc
    ‖∑ n ∈ (Finset.Icc 1 y).filter (fun n : ℕ ↦ (n : ℝ) ≤ U),
        χ n * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤
        ∑ n ∈ (Finset.Icc 1 y).filter (fun n : ℕ ↦ (n : ℝ) ≤ U),
          ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ (Finset.Icc 1 y).filter (fun n : ℕ ↦ (n : ℝ) ≤ U),
        ArithmeticFunction.vonMangoldt n := by
      apply Finset.sum_le_sum
      intro n _hn
      rw [norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg
        (χ.norm_le_one n)

/-- The scalar coefficient sum is contained in Mathlib's Chebyshev prefix. -/
theorem vaughanTwistedSumOne_cutoffSum_le_psi (U : ℝ) (y : ℕ) :
    (∑ n ∈ (Finset.Icc 1 y).filter (fun n : ℕ ↦ (n : ℝ) ≤ U),
      ArithmeticFunction.vonMangoldt n) ≤ Chebyshev.psi U := by
  rw [Chebyshev.psi]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnBounds := Finset.mem_Icc.mp hn'.1
    exact Finset.mem_Ioc.mpr
      ⟨Nat.zero_lt_one.trans_le hnBounds.1, Nat.le_floor hn'.2⟩
  · intro n _hn _hnnot
    exact ArithmeticFunction.vonMangoldt_nonneg

/-- The first twisted Vaughan term is bounded by `psi(U)`. -/
theorem norm_vaughanTwistedSumOne_le_psi
    (U : ℝ) (y q : ℕ) (χ : DirichletCharacter ℂ q) :
    ‖vaughanTwistedSumOne U y q χ‖ ≤ Chebyshev.psi U :=
  (norm_vaughanTwistedSumOne_le_cutoffSum U y q χ).trans
    (vaughanTwistedSumOne_cutoffSum_le_psi U y)

/-- Mathlib's explicit Chebyshev estimate bounds the first twisted term. -/
theorem norm_vaughanTwistedSumOne_le_log_four_add_four_mul
    {U : ℝ} (hU : 0 ≤ U) (y q : ℕ) (χ : DirichletCharacter ℂ q) :
    ‖vaughanTwistedSumOne U y q χ‖ ≤ (Real.log 4 + 4) * U :=
  (norm_vaughanTwistedSumOne_le_psi U y q χ).trans
    (Chebyshev.psi_le_const_mul_self hU)

/-- Maximum first Vaughan term over positive natural endpoints through `x`,
totalized to zero when the interval is empty. -/
noncomputable def vaughanTwistedSumOneEndpointMaximum
    (U : ℝ) (x q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  if hx : 1 ≤ x then
    (Finset.Icc 1 x).sup' ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hx⟩⟩
      (fun y ↦ ‖vaughanTwistedSumOne U y q χ‖)
  else 0

/-- The first-term endpoint maximum is bounded by `psi(U)`. -/
theorem vaughanTwistedSumOneEndpointMaximum_le_psi
    (U : ℝ) (x q : ℕ) (χ : DirichletCharacter ℂ q) :
    vaughanTwistedSumOneEndpointMaximum U x q χ ≤ Chebyshev.psi U := by
  unfold vaughanTwistedSumOneEndpointMaximum
  split_ifs with hx
  · apply Finset.sup'_le
    intro y _hy
    exact norm_vaughanTwistedSumOne_le_psi U y q χ
  · exact Chebyshev.psi_nonneg U

/-- Finite natural specialization of the source's weighted primitive
first-term estimate, given any bound for `psi(U)`. -/
theorem sum_weightedPrimitiveVaughanTwistedSumOneEndpointMaximum_le
    {U B : ℝ} (hB : Chebyshev.psi U ≤ B) (x Q : ℕ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : primitiveCharacters q,
          vaughanTwistedSumOneEndpointMaximum U x q χ.1) ≤
      B * (Q : ℝ) ^ 2 := by
  have hBnonneg : 0 ≤ B := (Chebyshev.psi_nonneg U).trans hB
  calc
    (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ χ : primitiveCharacters q,
            vaughanTwistedSumOneEndpointMaximum U x q χ.1) ≤
        ∑ q ∈ Finset.Ioc 0 Q, (q : ℝ) * B := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q := (Finset.mem_Ioc.mp hq).1
      have hphi : 0 < (q.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hqpos
      have hmass :
          (∑ χ : primitiveCharacters q,
            vaughanTwistedSumOneEndpointMaximum U x q χ.1) ≤
            (q.totient : ℝ) * B := by
        calc
          (∑ χ : primitiveCharacters q,
              vaughanTwistedSumOneEndpointMaximum U x q χ.1) ≤
              ∑ _χ : primitiveCharacters q, B := by
            apply Finset.sum_le_sum
            intro χ _hχ
            exact (vaughanTwistedSumOneEndpointMaximum_le_psi
              U x q χ.1).trans hB
          _ = (Fintype.card (primitiveCharacters q) : ℝ) * B := by
            simp
          _ ≤ (q.totient : ℝ) * B := by
            gcongr
            exact_mod_cast card_primitiveCharacters_le_totient hqpos
      calc
        (q : ℝ) / (q.totient : ℝ) *
            (∑ χ : primitiveCharacters q,
              vaughanTwistedSumOneEndpointMaximum U x q χ.1) ≤
            (q : ℝ) / (q.totient : ℝ) *
              ((q.totient : ℝ) * B) := by
          gcongr
        _ = (q : ℝ) * B := by field_simp
    _ ≤ ∑ _q ∈ Finset.Ioc 0 Q, (Q : ℝ) * B := by
      apply Finset.sum_le_sum
      intro q hq
      gcongr
      exact_mod_cast (Finset.mem_Ioc.mp hq).2
    _ = B * (Q : ℝ) ^ 2 := by
      simp [Nat.card_Ioc]
      ring

/-- Equation (6.7) with Mathlib's verified Chebyshev constant in place of the
paper's sharper `A_0`. -/
theorem sum_weightedPrimitiveVaughanTwistedSumOneEndpointMaximum_le_log_four_add_four_mul
    {U : ℝ} (hU : 0 ≤ U) (x Q : ℕ) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ χ : primitiveCharacters q,
          vaughanTwistedSumOneEndpointMaximum U x q χ.1) ≤
      (Real.log 4 + 4) * U * (Q : ℝ) ^ 2 :=
  sum_weightedPrimitiveVaughanTwistedSumOneEndpointMaximum_le
    (Chebyshev.psi_le_const_mul_self hU) x Q

end

end BoundedGaps.Maynard
