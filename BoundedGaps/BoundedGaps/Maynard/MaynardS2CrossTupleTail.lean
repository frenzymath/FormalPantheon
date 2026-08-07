import BoundedGaps.Maynard.MaynardS2CrossReciprocalGSquareTail
import BoundedGaps.Maynard.MaynardS1CrossTupleTail

noncomputable section

/-!
# Tuple tail for the S2 starred cross variables

The ordered off-diagonal cross variables factor into independent squarefree
rough supports. Removing the all-one tuple leaves the inverse-cutoff tail
used in the S2 cross-coordinate estimate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def roughS2CrossTupleReciprocalGSquareWeight
    (H : Finset ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) : ℝ :=
  ∏ x ∈ (offDiagonalPairs H).attach,
    ∏ p ∈ (s x.1 x.2).primeFactors,
      maynardS2CrossPrimeSquareWeight p

def roughS2CrossTupleReciprocalGSquareTail
    (H : Finset ℕ) (D Q : ℕ) : ℝ :=
  ∑ s ∈ (roughCrossTupleSupport H D Q).erase
      (oneCrossMoebiusTuple H),
    roughS2CrossTupleReciprocalGSquareWeight H s

def squarefreeRoughReciprocalGUnitMass (D Q : ℕ) : ℝ :=
  ∑ n ∈ squarefreeRoughUnitSupport D Q,
    ∏ p ∈ n.primeFactors, maynardS2CrossPrimeSquareWeight p

theorem roughS2CrossTupleReciprocalGSquareWeight_eq_inv_g_product
    {H : Finset ℕ} {D Q : ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hs : s ∈ roughCrossTupleSupport H D Q) :
    roughS2CrossTupleReciprocalGSquareWeight H s =
      ∏ x ∈ (offDiagonalPairs H).attach,
        (1 : ℝ) / (maynardS2G (s x.1 x.2) : ℝ) ^ 2 := by
  unfold roughS2CrossTupleReciprocalGSquareWeight
  apply Finset.prod_congr rfl
  intro x hx
  have hsx := (Finset.mem_pi.mp hs) x.1 x.2
  have hsq : Squarefree (s x.1 x.2) := by
    rw [roughCrossTupleSupport] at hs
    have hsx' := (Finset.mem_pi.mp hs) x.1 x.2
    rw [squarefreeRoughUnitSupport, Finset.mem_insert] at hsx'
    rcases hsx' with hOne | hsx'
    · rw [hOne]
      simp
    · exact squarefreeRoughSupport_squarefree hsx'
  exact (inv_maynardS2G_sq_eq_primeFactors_product hsq).symm

theorem squarefreeRoughReciprocalGUnitMass_eq (D Q : ℕ) :
    squarefreeRoughReciprocalGUnitMass D Q =
      1 + squarefreeRoughReciprocalGSquareTail D Q := by
  classical
  unfold squarefreeRoughReciprocalGUnitMass
    squarefreeRoughUnitSupport squarefreeRoughReciprocalGSquareTail
  rw [Finset.sum_insert (one_not_mem_squarefreeRoughSupport D Q)]
  simp only [Nat.primeFactors_one, Finset.prod_empty]
  apply congrArg (fun x : ℝ => 1 + x)
  apply Finset.sum_congr rfl
  intro n hn
  exact (inv_maynardS2G_sq_eq_primeFactors_product
    (squarefreeRoughSupport_squarefree hn)).symm

theorem squarefreeRoughReciprocalGUnitMass_nonneg (D Q : ℕ) :
    0 ≤ squarefreeRoughReciprocalGUnitMass D Q := by
  unfold squarefreeRoughReciprocalGUnitMass
  exact Finset.sum_nonneg fun n hn =>
    Finset.prod_nonneg fun p hp =>
      maynardS2CrossPrimeSquareWeight_nonneg p

theorem squarefreeRoughReciprocalGUnitMass_le_exp_thirtyTwo
    {D Q : ℕ} (hD : 2 ≤ D) :
    squarefreeRoughReciprocalGUnitMass D Q ≤ Real.exp 32 := by
  let E := ∏ p ∈ roughPrimeSupport D Q,
    (1 + maynardS2CrossPrimeSquareWeight p)
  calc
    squarefreeRoughReciprocalGUnitMass D Q =
        1 + squarefreeRoughReciprocalGSquareTail D Q :=
      squarefreeRoughReciprocalGUnitMass_eq D Q
    _ ≤ 1 + (E - 1) := by
      gcongr
      unfold E
      rw [← reciprocalGNonemptySubsetSum_eq_eulerProduct_sub_one]
      exact squarefreeRoughReciprocalGSquareTail_le_nonemptySubsetSum D Q
    _ = E := by ring
    _ ≤ Real.exp 32 := by
      unfold E
      exact roughPrimeReciprocalGSquareEulerProduct_le_exp_thirtyTwo hD

theorem roughS2CrossTupleReciprocalGSquareWeight_eq_product
    (H : Finset ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) :
    roughS2CrossTupleReciprocalGSquareWeight H s =
      ∏ x ∈ (offDiagonalPairs H).attach,
        (∏ p ∈ (s x.1 x.2).primeFactors,
          maynardS2CrossPrimeSquareWeight p) := by
  rfl

theorem sum_roughCrossTupleSupport_eq_reciprocalG_pow
    (H : Finset ℕ) (D Q : ℕ) :
    (∑ s ∈ roughCrossTupleSupport H D Q,
        roughS2CrossTupleReciprocalGSquareWeight H s) =
      (squarefreeRoughReciprocalGUnitMass D Q) ^
        (offDiagonalPairs H).card := by
  classical
  have hprod := Finset.prod_sum (offDiagonalPairs H)
    (fun _ => squarefreeRoughUnitSupport D Q)
    (fun _ n => ∏ p ∈ n.primeFactors,
      maynardS2CrossPrimeSquareWeight p)
  calc
    (∑ s ∈ roughCrossTupleSupport H D Q,
        roughS2CrossTupleReciprocalGSquareWeight H s) =
        ∑ s ∈ roughCrossTupleSupport H D Q,
          ∏ x ∈ (offDiagonalPairs H).attach,
            (∏ p ∈ (s x.1 x.2).primeFactors,
              maynardS2CrossPrimeSquareWeight p) := by rfl
    _ = ∏ ab ∈ offDiagonalPairs H,
          ∑ n ∈ squarefreeRoughUnitSupport D Q,
            ∏ p ∈ n.primeFactors,
              maynardS2CrossPrimeSquareWeight p := hprod.symm
    _ = ∏ _ab ∈ offDiagonalPairs H,
          squarefreeRoughReciprocalGUnitMass D Q := by rfl
    _ = (squarefreeRoughReciprocalGUnitMass D Q) ^
        (offDiagonalPairs H).card := Finset.prod_const _

theorem roughS2CrossTupleReciprocalGSquareTail_eq_pow_sub_one
    (H : Finset ℕ) (D Q : ℕ) :
    roughS2CrossTupleReciprocalGSquareTail H D Q =
      (squarefreeRoughReciprocalGUnitMass D Q) ^
        (offDiagonalPairs H).card - 1 := by
  have hone := oneCrossMoebiusTuple_mem_roughCrossTupleSupport H D Q
  have hsplit := Finset.sum_erase_add
    (s := roughCrossTupleSupport H D Q)
    (f := roughS2CrossTupleReciprocalGSquareWeight H) hone
  have honeWeight : roughS2CrossTupleReciprocalGSquareWeight H
      (oneCrossMoebiusTuple H) = 1 := by
    simp [roughS2CrossTupleReciprocalGSquareWeight,
      oneCrossMoebiusTuple]
  rw [honeWeight, sum_roughCrossTupleSupport_eq_reciprocalG_pow] at hsplit
  unfold roughS2CrossTupleReciprocalGSquareTail
  linarith

theorem roughS2CrossTupleReciprocalGSquareTail_le
    {H : Finset ℕ} {D Q : ℕ} (hD : 2 ≤ D) :
    roughS2CrossTupleReciprocalGSquareTail H D Q ≤
      (32 * Real.exp 32 / (D : ℝ)) *
        ((offDiagonalPairs H).card : ℝ) *
          (Real.exp 32) ^ ((offDiagonalPairs H).card - 1) := by
  let M := squarefreeRoughReciprocalGUnitMass D Q
  let m := (offDiagonalPairs H).card
  have hMone : 1 ≤ M := by
    dsimp [M]
    rw [squarefreeRoughReciprocalGUnitMass_eq]
    have htail0 : 0 ≤ squarefreeRoughReciprocalGSquareTail D Q := by
      unfold squarefreeRoughReciprocalGSquareTail
      exact Finset.sum_nonneg fun n hn => by positivity
    linarith
  have hMnonneg : 0 ≤ M := squarefreeRoughReciprocalGUnitMass_nonneg D Q
  have hMexp : M ≤ Real.exp 32 :=
    squarefreeRoughReciprocalGUnitMass_le_exp_thirtyTwo hD
  have hMtail : M - 1 ≤ 32 * Real.exp 32 / (D : ℝ) := by
    dsimp [M]
    rw [squarefreeRoughReciprocalGUnitMass_eq]
    simpa using squarefreeRoughReciprocalGSquareTail_le (Q := Q) hD
  have hpow := abs_pow_sub_pow_le (a := M) (b := (1 : ℝ)) (n := m)
  have hMpow : 1 ≤ M ^ m := one_le_pow₀ hMone
  norm_num only [one_pow] at hpow
  rw [abs_of_nonneg (sub_nonneg.mpr hMpow),
    abs_of_nonneg (sub_nonneg.mpr hMone), abs_of_nonneg hMnonneg,
    max_eq_left hMone] at hpow
  have hpowExp : M ^ (m - 1) ≤ (Real.exp 32) ^ (m - 1) :=
    pow_le_pow_left₀ hMnonneg hMexp _
  have hconstantNonneg : 0 ≤
      (32 * Real.exp 32 / (D : ℝ)) * (m : ℝ) := by positivity
  calc
    roughS2CrossTupleReciprocalGSquareTail H D Q = M ^ m - 1 := by
      exact roughS2CrossTupleReciprocalGSquareTail_eq_pow_sub_one H D Q
    _ ≤ (M - 1) * (m : ℝ) * M ^ (m - 1) := hpow
    _ ≤ (32 * Real.exp 32 / (D : ℝ)) *
        (m : ℝ) * M ^ (m - 1) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right hMtail (Nat.cast_nonneg m)
      · positivity
    _ ≤ (32 * Real.exp 32 / (D : ℝ)) *
        (m : ℝ) * (Real.exp 32) ^ (m - 1) := by
      exact mul_le_mul_of_nonneg_left hpowExp hconstantNonneg
    _ = _ := by rfl

end BoundedGaps.Maynard
