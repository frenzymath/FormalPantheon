import BoundedGaps.Maynard.MaynardYDiagonalExplicit
import BoundedGaps.Maynard.ConcreteSquarefreeMeanLimit

noncomputable section

namespace BoundedGaps.Maynard

open MeasureTheory Set
open scoped BigOperators

/-! Arithmetic form of the logarithmic simplex cutoff. -/

def normalizedDivisorLogTuple
    (H : Finset ℕ) (R : ℕ) (u : H → ℕ) : H → ℝ :=
  fun h => Real.log (u h) / Real.log R

theorem eventually_one_lt_engelsmaMaynardRadius
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in Filter.atTop, 1 < engelsmaMaynardRadius alpha N := by
  have hlog := tendsto_log_engelsmaMaynardRadius_atTop halpha
  filter_upwards [hlog.eventually (Filter.eventually_gt_atTop 0)] with N hN
  have hreal : (1 : ℝ) < engelsmaMaynardRadius alpha N :=
    (Real.log_pos_iff (Nat.cast_nonneg _)).mp hN
  exact_mod_cast hreal

theorem log_divisorTupleProduct_eq_sum
    {H : Finset ℕ} {u : H → ℕ}
    (huPos : ∀ h : H, 0 < u h) :
    Real.log (divisorTupleProduct H u) =
      ∑ h : H, Real.log (u h) := by
  unfold divisorTupleProduct
  rw [Nat.cast_prod, Real.log_prod]
  intro h hh
  exact_mod_cast (huPos h).ne'

theorem sum_normalizedDivisorLogTuple_eq_log_product_div
    {H : Finset ℕ} {R : ℕ} {u : H → ℕ}
    (_hR : 1 < R) (huPos : ∀ h : H, 0 < u h) :
    ∑ h : H, normalizedDivisorLogTuple H R u h =
      Real.log (divisorTupleProduct H u) / Real.log R := by
  unfold normalizedDivisorLogTuple
  rw [← Finset.sum_div]
  rw [log_divisorTupleProduct_eq_sum huPos]

theorem divisorTupleProduct_lt_iff_sum_normalizedDivisorLogTuple_lt_one
    {H : Finset ℕ} {R : ℕ} {u : H → ℕ}
    (hR : 1 < R) (huPos : ∀ h : H, 0 < u h) :
    divisorTupleProduct H u < R ↔
      ∑ h : H, normalizedDivisorLogTuple H R u h < 1 := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (Nat.zero_lt_of_lt hR)
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hprodPos : 0 < divisorTupleProduct H u := by
    unfold divisorTupleProduct
    apply Finset.prod_pos
    intro h hh
    exact huPos h
  have hprodReal : (0 : ℝ) < divisorTupleProduct H u := by
    exact_mod_cast hprodPos
  have hsum := sum_normalizedDivisorLogTuple_eq_log_product_div hR huPos
  constructor
  · intro hlt
    have hltReal : (divisorTupleProduct H u : ℝ) < R := by
      exact_mod_cast hlt
    have hloglt : Real.log (divisorTupleProduct H u) < Real.log R :=
      Real.strictMonoOn_log (Set.mem_Ioi.mpr hprodReal)
        (Set.mem_Ioi.mpr hRpos) hltReal
    rw [hsum]
    exact (div_lt_iff₀ hlogR).2 (by simpa using hloglt)
  · intro hlt
    have hquot : Real.log (divisorTupleProduct H u) / Real.log R < 1 := by
      rw [← hsum]
      exact hlt
    have hloglt : Real.log (divisorTupleProduct H u) < Real.log R := by
      simpa using (div_lt_iff₀ hlogR).mp hquot
    by_contra hnot
    have hRle : R ≤ divisorTupleProduct H u := Nat.le_of_not_gt hnot
    have hRleReal : (R : ℝ) ≤ divisorTupleProduct H u := by
      exact_mod_cast hRle
    have hlogle : Real.log R ≤ Real.log (divisorTupleProduct H u) :=
      Real.strictMonoOn_log.monotoneOn hRpos hprodReal hRleReal
    linarith

theorem normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
    {H : Finset ℕ} {R : ℕ} {u : H → ℕ}
    (hR : 1 < R) (hu : u ∈ maynardDivisorTupleBox H R) (h : H) :
    normalizedDivisorLogTuple H R u h ∈ Set.Icc (0 : ℝ) 1 := by
  have huBounds := mem_maynardDivisorTupleBox_iff.mp hu h
  have huPos : 0 < u h := huBounds.1
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (Nat.zero_lt_of_lt hR)
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have huReal : (0 : ℝ) < u h := by exact_mod_cast huPos
  have huLe : (u h : ℝ) ≤ R := by exact_mod_cast huBounds.2.le
  have hloguNonneg : 0 ≤ Real.log (u h) :=
    Real.log_nonneg (by exact_mod_cast huBounds.1)
  have hloguLe : Real.log (u h) ≤ Real.log R :=
    Real.strictMonoOn_log.monotoneOn huReal hRpos huLe
  exact ⟨div_nonneg hloguNonneg hlogR.le,
    (div_le_iff₀ hlogR).2 (by simpa using hloguLe)⟩

theorem normalizedDivisorLogTuple_mem_cube_and_sum_lt_one_of_mem_support
    {H : Finset ℕ} {R W : ℕ} {u : H → ℕ}
    (hR : 1 < R) (hu : u ∈ maynardDivisorTupleSupport H R W) :
    (∀ h : H,
      normalizedDivisorLogTuple H R u h ∈ Set.Icc (0 : ℝ) 1) ∧
      ∑ h : H, normalizedDivisorLogTuple H R u h < 1 := by
  have huSupport := isMaynardDivisorTuple_of_mem_support hu
  have huBox := huSupport.mem_maynardDivisorTupleBox
  constructor
  · intro h
    exact normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
      hR huBox h
  · apply (divisorTupleProduct_lt_iff_sum_normalizedDivisorLogTuple_lt_one
      hR (fun h => (mem_maynardDivisorTupleBox_iff.mp huBox h).1)).mp
    exact huSupport.1

set_option maxRecDepth 2000 in
theorem engelsmaSmallKCandidate_eq_polynomial_of_mem_support
    {R W : ℕ} {u : BoundedGaps.engelsmaTuple → ℕ}
    (hR : 1 < R)
    (hu : u ∈ maynardDivisorTupleSupport BoundedGaps.engelsmaTuple R W) :
    engelsmaSmallKCandidate
        (normalizedDivisorLogTuple BoundedGaps.engelsmaTuple R u) =
      smallKRealPolynomial (fun i =>
        normalizedDivisorLogTuple BoundedGaps.engelsmaTuple R u
          (engelsmaIndexEquiv.symm i)) := by
  let t := normalizedDivisorLogTuple BoundedGaps.engelsmaTuple R u
  have htData :=
    normalizedDivisorLogTuple_mem_cube_and_sum_lt_one_of_mem_support hR hu
  have ht : (fun i => t (engelsmaIndexEquiv.symm i)) ∈
      maynardSimplex 105 := by
    constructor
    · rw [maynardCube, maynardCubeOf, Set.mem_pi]
      intro i hi
      exact htData.1 (engelsmaIndexEquiv.symm i)
    · have hsum : (∑ i : Fin 105, t (engelsmaIndexEquiv.symm i)) =
          ∑ h : BoundedGaps.engelsmaTuple, t h :=
        (engelsmaIndexEquiv.symm.sum_comp t)
      rw [hsum]
      exact htData.2.le
  unfold engelsmaSmallKCandidate smallKCandidate
  rw [if_pos ht]

set_option maxRecDepth 2000 in
theorem engelsmaMaynardYDiagonal_eq_polynomial_sum
    {alpha : ℝ} {N : ℕ}
    (hR : 1 < engelsmaMaynardRadius alpha N) :
    engelsmaMaynardYDiagonal alpha N =
      ∑ u ∈ maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
        smallKRealPolynomial (fun i =>
          normalizedDivisorLogTuple BoundedGaps.engelsmaTuple
            (engelsmaMaynardRadius alpha N) u (engelsmaIndexEquiv.symm i)) ^ 2 /
          ∏ h : BoundedGaps.engelsmaTuple,
            (Nat.totient (u h) : ℝ) := by
  rw [engelsmaMaynardYDiagonal_eq_explicit]
  apply Finset.sum_congr rfl
  intro u hu
  have hpoly := engelsmaSmallKCandidate_eq_polynomial_of_mem_support hR hu
  change engelsmaSmallKCandidate
      (normalizedDivisorLogTuple BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) u) ^ 2 /
      ∏ h : BoundedGaps.engelsmaTuple, (Nat.totient (u h) : ℝ) = _
  rw [hpoly]

end BoundedGaps.Maynard
