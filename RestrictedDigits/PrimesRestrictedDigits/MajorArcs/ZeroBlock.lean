import PrimesRestrictedDigits.MajorArcs.LogSubdivision
import PrimesRestrictedDigits.MajorArcs.ProjectedBox

/-!
# The zero block in the major-arc subdivision

This supplies the crude estimate omitted when published p. 187 changes from
all subdivision blocks to the positive blocks required by Eq. (5.1).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The prime-log exponential sum on one major-arc subdivision block. -/
noncomputable def majorArcPrimePhaseBlockSum
    (X J m j b q : ℕ) (c : ℤ) : ℂ :=
  ∑ p ∈ (majorArcBlock (X : ℝ) J m j).filter Nat.Prime,
    (Real.log (p : ℝ) : ℂ) *
      majorArcPhase (((m * p : ℕ) : ℝ) *
        ((b : ℝ) / (q : ℝ) + (c : ℝ) / (X : ℝ)))

theorem projectedPrimeBoxWeightAtProduct_nonneg
    (X : ℕ) {k : ℕ} (a : Fin k → ℝ) (delta : ℝ) (m : ℕ) :
    0 ≤ projectedPrimeBoxWeightAtProduct X a delta m := by
  unfold projectedPrimeBoxWeightAtProduct primeTupleWeightAtProduct
  apply Finset.sum_nonneg
  intro p hp
  unfold primeTupleLogWeight
  exact Finset.prod_nonneg fun i hi => Real.log_natCast_nonneg (p i)

theorem majorArcZeroBlock_primeLog_le
    {X J m : ℕ} (hJ : 0 < J) (hm : 0 < m) :
    (∑ p ∈ (majorArcBlock (X : ℝ) J m 0).filter Nat.Prime,
      Real.log (p : ℝ)) ≤
      Real.log 4 * majorArcBlockLength (X : ℝ) J m := by
  let U := majorArcBlockLength (X : ℝ) J m
  have hU : 0 ≤ U := by
    dsimp [U, majorArcBlockLength]
    positivity
  have hsubset :
      (majorArcBlock (X : ℝ) J m 0).filter Nat.Prime ⊆
        (Finset.Ioc 0 ⌊U⌋₊).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    have hpblock := mem_naturalLeftClosedRightOpenInterval.mp hp.1
    refine ⟨?_, hp.2⟩
    rw [Finset.mem_Ioc]
    refine ⟨hp.2.pos, ?_⟩
    apply Nat.le_floor
    simpa [majorArcBlock, majorArcBlockUpper, U] using hpblock.2.le
  calc
    (∑ p ∈ (majorArcBlock (X : ℝ) J m 0).filter Nat.Prime,
        Real.log (p : ℝ)) ≤
        ∑ p ∈ (Finset.Ioc 0 ⌊U⌋₊).filter Nat.Prime,
          Real.log (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp hnot
      exact Real.log_natCast_nonneg p
    _ = Chebyshev.theta U := by rw [Chebyshev.theta]
    _ ≤ Real.log 4 * U := Chebyshev.theta_le_log4_mul_x hU
    _ = _ := rfl

private theorem norm_majorArcPhase_zeroBlock (x : ℝ) :
    ‖majorArcPhase x‖ = 1 := by
  rw [majorArcPhase]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_majorArcPrimePhaseBlockSum_le_primeLog
    (X J m j b q : ℕ) (c : ℤ) :
    ‖majorArcPrimePhaseBlockSum X J m j b q c‖ ≤
      ∑ p ∈ (majorArcBlock (X : ℝ) J m j).filter Nat.Prime,
        Real.log (p : ℝ) := by
  unfold majorArcPrimePhaseBlockSum
  calc
    ‖∑ p ∈ (majorArcBlock (X : ℝ) J m j).filter Nat.Prime,
        (Real.log (p : ℝ) : ℂ) *
          majorArcPhase (((m * p : ℕ) : ℝ) *
            ((b : ℝ) / (q : ℝ) + (c : ℝ) / (X : ℝ)))‖ ≤
        ∑ p ∈ (majorArcBlock (X : ℝ) J m j).filter Nat.Prime,
          ‖(Real.log (p : ℝ) : ℂ) *
            majorArcPhase (((m * p : ℕ) : ℝ) *
              ((b : ℝ) / (q : ℝ) + (c : ℝ) / (X : ℝ)))‖ :=
      norm_sum_le _ _
    _ = ∑ p ∈ (majorArcBlock (X : ℝ) J m j).filter Nat.Prime,
          Real.log (p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_majorArcPhase_zeroBlock, mul_one,
        abs_of_nonneg (Real.log_natCast_nonneg p)]

theorem norm_majorArcPrimePhaseBlockSum_zero_le
    {X J m b q : ℕ} {c : ℤ} (hJ : 0 < J) (hm : 0 < m) :
    ‖majorArcPrimePhaseBlockSum X J m 0 b q c‖ ≤
      Real.log 4 * majorArcBlockLength (X : ℝ) J m :=
  (norm_majorArcPrimePhaseBlockSum_le_primeLog X J m 0 b q c).trans
    (majorArcZeroBlock_primeLog_le hJ hm)

private theorem norm_sum_projectedPrimeBox_blocks_le
    {X J k : ℕ} {a : Fin k → ℝ} {delta : ℝ}
    (hX : 3 ≤ X) (hJ : 0 < J) (F : ℕ → ℂ)
    (hF : ∀ m ∈ Finset.Ico 1 X,
      ‖F m‖ ≤ Real.log 4 * majorArcBlockLength (X : ℝ) J m) :
    ‖∑ m ∈ Finset.Ico 1 X,
        (projectedPrimeBoxWeightAtProduct X a delta m : ℂ) * F m‖ ≤
      (Real.log 4 * majorArcSubdivisionWidth J * (X : ℝ)) *
        (2 * Real.log 4 * Real.log (X : ℝ)) ^ k := by
  let W := fun m => projectedPrimeBoxWeightAtProduct X a delta m
  let K := Real.log 4 * majorArcSubdivisionWidth J * (X : ℝ)
  have hK : 0 ≤ K := by
    dsimp [K, majorArcSubdivisionWidth]
    positivity
  have hsumSubset :
      (∑ m ∈ Finset.Ico 1 X, W m / (m : ℝ)) ≤
        ∑ m ∈ Finset.range X, W m / (m : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hm).2
    · intro m hm hnot
      exact div_nonneg (projectedPrimeBoxWeightAtProduct_nonneg X a delta m)
        (by positivity)
  calc
    ‖∑ m ∈ Finset.Ico 1 X,
        (projectedPrimeBoxWeightAtProduct X a delta m : ℂ) * F m‖ ≤
        ∑ m ∈ Finset.Ico 1 X,
          ‖(projectedPrimeBoxWeightAtProduct X a delta m : ℂ) * F m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Ico 1 X, W m *
          (Real.log 4 * majorArcBlockLength (X : ℝ) J m) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (projectedPrimeBoxWeightAtProduct_nonneg X a delta m)]
      exact mul_le_mul_of_nonneg_left (hF m hm)
        (projectedPrimeBoxWeightAtProduct_nonneg X a delta m)
    _ = K * ∑ m ∈ Finset.Ico 1 X, W m / (m : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hmpos : 0 < m := (Finset.mem_Ico.mp hm).1
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
      rw [majorArcBlockLength_eq_width_mul (X : ℝ) hJ hmpos]
      dsimp [K, W]
      field_simp
    _ ≤ K * (∑ m ∈ Finset.range X, W m / (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hsumSubset hK
    _ ≤ K * (2 * Real.log 4 * Real.log (X : ℝ)) ^ k := by
      apply mul_le_mul_of_nonneg_left _ hK
      exact sum_projectedPrimeBoxWeight_div_le_log_pow X a delta hX
    _ = _ := rfl

theorem norm_sum_projectedPrimeBox_zeroBlock_le
    {X J k : ℕ} (a : Fin k → ℝ) (delta : ℝ) (b q : ℕ) (c : ℤ)
    (hX : 3 ≤ X) (hJ : 0 < J) (_hq : 0 < q) :
    ‖∑ m ∈ Finset.Ico 1 X,
      (projectedPrimeBoxWeightAtProduct X a delta m : ℂ) *
        majorArcPrimePhaseBlockSum X J m 0 b q c‖ ≤
      (Real.log 4 * majorArcSubdivisionWidth J * (X : ℝ)) *
        (2 * Real.log 4 * Real.log (X : ℝ)) ^ k := by
  apply norm_sum_projectedPrimeBox_blocks_le hX hJ
  intro m hm
  exact norm_majorArcPrimePhaseBlockSum_zero_le hJ (Finset.mem_Ico.mp hm).1

theorem norm_sum_projectedPrimeBox_logSubdivision_zeroBlock_le
    {X D k : ℕ} (a : Fin k → ℝ) (delta : ℝ)
    (b q : ℕ) (c : ℤ) (hX : 4 ≤ X) (hq : 0 < q) :
    ‖∑ m ∈ Finset.Ico 1 X,
      (projectedPrimeBoxWeightAtProduct X a delta m : ℂ) *
        majorArcPrimePhaseBlockSum X
          (majorArcLogSubdivisionCount X D (k + 1)) m 0 b q c‖ ≤
      (Real.log 4 *
          (Real.log (X : ℝ) ^
            majorArcLogSubdivisionExponent D (k + 1))⁻¹ *
          (X : ℝ)) *
        (2 * Real.log 4 * Real.log (X : ℝ)) ^ k := by
  calc
    ‖∑ m ∈ Finset.Ico 1 X,
      (projectedPrimeBoxWeightAtProduct X a delta m : ℂ) *
        majorArcPrimePhaseBlockSum X
          (majorArcLogSubdivisionCount X D (k + 1)) m 0 b q c‖ ≤
        (Real.log 4 * majorArcSubdivisionWidth
            (majorArcLogSubdivisionCount X D (k + 1)) * (X : ℝ)) *
          (2 * Real.log 4 * Real.log (X : ℝ)) ^ k := by
      exact norm_sum_projectedPrimeBox_zeroBlock_le a delta b q c
        (by omega) (majorArcLogSubdivisionCount_pos (by omega)) hq
    _ ≤ (Real.log 4 *
          (Real.log (X : ℝ) ^
            majorArcLogSubdivisionExponent D (k + 1))⁻¹ *
          (X : ℝ)) *
        (2 * Real.log 4 * Real.log (X : ℝ)) ^ k := by
      gcongr
      exact majorArcLogSubdivisionWidth_le_inv_log_pow (by omega)

end PrimesRestrictedDigits
