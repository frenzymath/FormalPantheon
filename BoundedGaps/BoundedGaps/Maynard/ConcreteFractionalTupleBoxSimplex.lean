import BoundedGaps.Maynard.ConcreteFractionalTupleBox
import BoundedGaps.Maynard.MaynardLogSimplex

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

theorem tendsto_engelsmaFractionalLogSum_div_logRadius
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (beta : H → ℝ) (hbeta : ∀ h, 0 ≤ beta h) :
    Tendsto (fun N : ℕ =>
      (∑ h : H, Real.log (engelsmaMaynardRadius (alpha * beta h) N)) /
        Real.log (engelsmaMaynardRadius alpha N))
      atTop (nhds (∑ h : H, beta h)) := by
  have hbase : Tendsto (fun N : ℕ =>
      Real.log ((N - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
  have hcoord : ∀ h : H, Tendsto (fun N : ℕ =>
      Real.log (engelsmaMaynardRadius (alpha * beta h) N) /
        Real.log ((N - 1 : ℕ) : ℝ))
      atTop (nhds (alpha * beta h)) := by
    intro h
    by_cases hzero : beta h = 0
    · have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds
      have hzeroT : Tendsto (fun N : ℕ =>
          Real.log (engelsmaMaynardRadius (alpha * beta h) N) /
            Real.log ((N - 1 : ℕ) : ℝ)) atTop (nhds 0) := by
        apply hconst.congr'
        filter_upwards [] with N
        simp [hzero, engelsmaMaynardRadius, maynardDivisorCutoff]
      simpa [hzero] using hzeroT
    · have hpos : 0 < beta h := lt_of_le_of_ne (hbeta h) (Ne.symm hzero)
      simpa using tendsto_log_engelsmaMaynardRadius_div_log_sub
        (mul_pos halpha hpos)
  have hsum : Tendsto (fun N : ℕ =>
      ∑ h : H, Real.log (engelsmaMaynardRadius (alpha * beta h) N) /
        Real.log ((N - 1 : ℕ) : ℝ))
      atTop (nhds (∑ h : H, alpha * beta h)) := by
    apply tendsto_finsetSum Finset.univ
    intro h hh
    exact hcoord h
  have hden : Tendsto (fun N : ℕ =>
      Real.log (engelsmaMaynardRadius alpha N) /
        Real.log ((N - 1 : ℕ) : ℝ))
      atTop (nhds alpha) :=
    tendsto_log_engelsmaMaynardRadius_div_log_sub halpha
  have hquot := hsum.div hden (ne_of_gt halpha)
  have hquot' : Tendsto (fun N : ℕ =>
      (∑ h : H, Real.log (engelsmaMaynardRadius (alpha * beta h) N) /
        Real.log ((N - 1 : ℕ) : ℝ)) /
        (Real.log (engelsmaMaynardRadius alpha N) /
          Real.log ((N - 1 : ℕ) : ℝ)))
      atTop (nhds ((∑ h : H, alpha * beta h) / alpha)) := by
    apply hquot.congr'
    exact Eventually.of_forall (fun N => rfl)
  have hlimit : (∑ h : H, alpha * beta h) / alpha = ∑ h : H, beta h := by
    rw [← Finset.mul_sum]
    field_simp [halpha.ne']
  have hquotOne : Tendsto (fun N : ℕ =>
      (∑ h : H, Real.log (engelsmaMaynardRadius (alpha * beta h) N) /
        Real.log ((N - 1 : ℕ) : ℝ)) /
        (Real.log (engelsmaMaynardRadius alpha N) /
          Real.log ((N - 1 : ℕ) : ℝ)))
      atTop (nhds (∑ h : H, beta h)) := by
    rw [hlimit] at hquot'
    exact hquot'
  apply hquotOne.congr'
  filter_upwards [hbase.eventually (eventually_ne_atTop 0),
    (tendsto_log_engelsmaMaynardRadius_atTop halpha).eventually
      (eventually_gt_atTop 0)] with N hbaseNe hdenPos
  simp only [Finset.sum_div]
  field_simp [hbaseNe, hdenPos.ne']

set_option maxRecDepth 10000 in
theorem eventually_engelsmaFractionalTupleBox_subset_preSievedSimplexTupleSupport
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (beta : H → ℝ) (hbeta : ∀ h, 0 ≤ beta h)
    (hsum : ∑ h : H, beta h < 1) :
    ∀ᶠ N : ℕ in atTop,
      engelsmaFractionalTupleBox H alpha beta N ⊆
        preSievedSimplexTupleSupport H
          (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) := by
  have hlogsum := tendsto_engelsmaFractionalLogSum_div_logRadius
    halpha beta hbeta
  have hmargin := hlogsum.eventually (Iio_mem_nhds hsum)
  have hR := tendsto_log_engelsmaMaynardRadius_atTop halpha
  filter_upwards [hmargin, hR.eventually (eventually_gt_atTop 0)] with
      N hmarginN hlogR
  intro u hu
  have huBox : u ∈ squarefreeCoprimeTupleBox
      H (engelsmaMaynardModulus N)
      (fun h => engelsmaMaynardRadius (alpha * beta h) N) := by
    simpa [engelsmaFractionalTupleBox] using hu
  rw [squarefreeCoprimeTupleBox, Fintype.mem_piFinset] at huBox
  have hRnat : 1 < engelsmaMaynardRadius alpha N := by
    have hRreal : (1 : ℝ) < engelsmaMaynardRadius alpha N :=
      (Real.log_pos_iff (Nat.cast_nonneg _)).mp hlogR
    exact_mod_cast hRreal
  have hlogsumQ :
      ∑ h : H, Real.log
          (engelsmaMaynardRadius (alpha * beta h) N) <
        Real.log (engelsmaMaynardRadius alpha N) := by
    simpa only [one_mul] using (div_lt_iff₀ hlogR).mp hmarginN
  have hlogsumU : ∑ h : H, Real.log (u h) <
      Real.log (engelsmaMaynardRadius alpha N) := by
    apply lt_of_le_of_lt
    · apply Finset.sum_le_sum
      intro h hh
      have huh := Finset.mem_filter.mp (huBox h)
      have huLe : u h ≤ engelsmaMaynardRadius (alpha * beta h) N :=
        (Finset.mem_Icc.mp huh.1).2
      have huPos : 0 < u h := (Finset.mem_Icc.mp huh.1).1
      have hQPos : 0 < engelsmaMaynardRadius (alpha * beta h) N :=
        huPos.trans_le huLe
      have huReal : (0 : ℝ) < u h := by exact_mod_cast huPos
      have hQReal : (0 : ℝ) < engelsmaMaynardRadius
          (alpha * beta h) N := by exact_mod_cast hQPos
      have huLeReal : (u h : ℝ) ≤ engelsmaMaynardRadius
          (alpha * beta h) N := by exact_mod_cast huLe
      exact Real.strictMonoOn_log.monotoneOn huReal hQReal huLeReal
    · exact hlogsumQ
  have hprodPos : 0 < divisorTupleProduct H u := by
    unfold divisorTupleProduct
    apply Finset.prod_pos
    intro h hh
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp (huBox h)).1).1
  have hsumNorm : ∑ h : H,
      normalizedDivisorLogTuple H
        (engelsmaMaynardRadius alpha N) u h < 1 := by
    unfold normalizedDivisorLogTuple
    rw [← Finset.sum_div]
    apply (div_lt_iff₀ hlogR).2
    simpa only [one_mul] using hlogsumU
  have hprodLt : divisorTupleProduct H u <
      engelsmaMaynardRadius alpha N :=
    (divisorTupleProduct_lt_iff_sum_normalizedDivisorLogTuple_lt_one
      (by exact hRnat) (fun h =>
        (Finset.mem_Icc.mp (Finset.mem_filter.mp (huBox h)).1).1)).mpr hsumNorm
  apply Finset.mem_filter.mpr
  constructor
  · rw [preSievedCommonTupleSupport, Fintype.mem_piFinset]
    intro h
    rw [preSievedCommonCoordinateSupport, Finset.mem_filter]
    have huh := Finset.mem_filter.mp (huBox h)
    have huPos := (Finset.mem_Icc.mp huh.1).1
    have hcoordLe : u h ≤ divisorTupleProduct H u :=
      Nat.le_of_dvd hprodPos (divisorTupleCoordinate_dvd_product u h)
    exact ⟨Finset.mem_range.mpr (lt_of_le_of_lt hcoordLe hprodLt),
      ⟨huPos, huh.2.1, huh.2.2⟩⟩
  · exact hprodLt

end BoundedGaps.Maynard
