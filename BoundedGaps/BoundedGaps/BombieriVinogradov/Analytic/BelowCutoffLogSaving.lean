import BoundedGaps.BombieriVinogradov.Analytic.SmallTermLogSaving

/-!
# Logarithmic saving for every total modulus cutoff

This file closes the range below SEM-570's logarithmic conductor floor. The
floor itself is eventually admissible in the logarithmically reduced
square-root range, and the globally Chebyshev-centered summands are
nonnegative. A sum below the floor can therefore be enlarged to the floor and
bounded by SEM-570 without changing its coefficient.

The centered discrepancy comes from `AkbaryHambrook2013v2`, equation (1.2)
and Section 7, printed pp. 3 and 24--25. The cutoff-range and two-branch
closure are project-derived. Semantic review: `SEM-571`.
-/

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

noncomputable section

/-- The totalized globally Chebyshev-centered endpoint/residue maximum is
nonnegative for every endpoint and modulus. -/
theorem maxCenteredProgressionDiscrepancyUpTo_nonneg (x q : ℕ) :
    0 ≤ maxCenteredProgressionDiscrepancyUpTo x q := by
  by_cases hx : 2 ≤ x
  · by_cases hq : 0 < q
    · rw [maxCenteredProgressionDiscrepancyUpTo_eq_sup_endpoint_residues hx hq]
      let a := (coprimeResidues_nonempty hq).choose
      have ha : a ∈ coprimeResidues q := (coprimeResidues_nonempty hq).choose_spec
      exact Finset.le_sup'_of_le
        (fun y ↦
          (coprimeResidues q).sup' (coprimeResidues_nonempty hq) (fun b ↦
            |chebyshevProgressionSum y q b -
              Chebyshev.psi (y : ℝ) / (q.totient : ℝ)|))
        (Finset.mem_Icc.mpr ⟨le_rfl, hx⟩)
        (Finset.le_sup'_of_le
          (fun b ↦
            |chebyshevProgressionSum 2 q b -
              Chebyshev.psi (2 : ℝ) / (q.totient : ℝ)|)
          ha (abs_nonneg _))
    · simp [maxCenteredProgressionDiscrepancyUpTo,
        maxCenteredProgressionDiscrepancy, hx, hq]
  · simp [maxCenteredProgressionDiscrepancyUpTo, hx]

/-- The floored logarithmic conductor cutoff is eventually inside the
logarithmically reduced square-root range. This scalar fact holds for every
real exponent parameter. -/
theorem exists_siegelWalfiszConductorCutoff_le_logReducedSqrt
    (A : ℝ) :
    ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        (siegelWalfiszConductorCutoff (A + 5) x : ℝ) ≤
          Real.sqrt (x : ℝ) /
            Real.rpow (Real.log (x : ℝ)) (A + 5) := by
  have hdom :=
    ((isLittleO_log_rpow_rpow_atTop (2 * (A + 5))
      (show (0 : ℝ) < 1 / 2 by norm_num)).comp_tendsto
        tendsto_natCast_atTop_atTop).eventuallyLE
  rw [Filter.eventually_atTop] at hdom
  obtain ⟨N, hN⟩ := hdom
  refine ⟨max 4 N, le_max_left _ _, ?_⟩
  intro x hx
  have hNx : N ≤ x := (le_max_right 4 N).trans hx
  have hx4 : 4 ≤ x := (le_max_left 4 N).trans hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hlogOne : 1 ≤ Real.log (x : ℝ) := one_le_log_natCast hx4
  have hlogPos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hlogOne
  have hscalePos :
      0 < Real.rpow (Real.log (x : ℝ)) (A + 5) :=
    Real.rpow_pos_of_pos hlogPos _
  have hgrowth := hN x hNx
  simp only [Function.comp_apply, Real.norm_eq_abs] at hgrowth
  rw [abs_of_nonneg (Real.rpow_nonneg hlogPos.le _),
    abs_of_nonneg (Real.rpow_nonneg hxpos.le _)] at hgrowth
  apply (le_div_iff₀ hscalePos).2
  calc
    (siegelWalfiszConductorCutoff (A + 5) x : ℝ) *
          Real.rpow (Real.log (x : ℝ)) (A + 5) ≤
        Real.rpow (Real.log (x : ℝ)) (A + 5) *
          Real.rpow (Real.log (x : ℝ)) (A + 5) :=
      mul_le_mul_of_nonneg_right
        (natCast_siegelWalfiszConductorCutoff_le (A + 5) x) hscalePos.le
    _ = Real.rpow (Real.log (x : ℝ)) ((A + 5) + (A + 5)) :=
      (Real.rpow_add hlogPos (A + 5) (A + 5)).symm
    _ = Real.rpow (Real.log (x : ℝ)) (2 * (A + 5)) := by ring_nf
    _ ≤ Real.rpow (x : ℝ) (1 / 2 : ℝ) := hgrowth
    _ = Real.sqrt (x : ℝ) := (Real.sqrt_eq_rpow (x : ℝ)).symm

/-- SEM-570's complete globally Chebyshev-centered logarithmic saving holds
for every total cutoff in the logarithmically reduced square-root range. -/
theorem
    exists_siegelWalfisz_sum_maxCenteredProgressionDiscrepancyUpTo_le_logSaving_allCutoffs :
    ∀ A : ℝ, 0 ≤ A →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∃ X0 : ℕ, 4 ≤ X0 ∧
          ∀ x : ℕ, X0 ≤ x →
            ∀ Q : ℕ,
              (Q : ℝ) ≤ Real.sqrt (x : ℝ) /
                  Real.rpow (Real.log (x : ℝ)) (A + 5) →
                (∑ q ∈ Finset.Icc 1 Q,
                  maxCenteredProgressionDiscrepancyUpTo x q) ≤
                  (C + 40 * vaughanPrimitiveMeanEquationOneTwoConstant
                    (Real.log 4 + 4)) * (x : ℝ) /
                      Real.rpow (Real.log (x : ℝ)) A := by
  intro A hA
  obtain ⟨C, c, hC, hc, Xbase, hXbase, hbase⟩ :=
    exists_siegelWalfisz_sum_maxCenteredProgressionDiscrepancyUpTo_le_logSaving
      A hA
  obtain ⟨Xrange, hXrange, hrange⟩ :=
    exists_siegelWalfiszConductorCutoff_le_logReducedSqrt A
  refine ⟨C, c, hC, hc, max Xbase Xrange,
    hXbase.trans (le_max_left _ _), ?_⟩
  intro x hx Q hQrange
  have hxBase : Xbase ≤ x := (le_max_left Xbase Xrange).trans hx
  have hxRange : Xrange ≤ x := (le_max_right Xbase Xrange).trans hx
  let R := siegelWalfiszConductorCutoff (A + 5) x
  have hRrange :
      (R : ℝ) ≤ Real.sqrt (x : ℝ) /
        Real.rpow (Real.log (x : ℝ)) (A + 5) := by
    simpa only [R] using hrange x hxRange
  by_cases hRQ : R ≤ Q
  · exact hbase x hxBase Q (by simpa only [R] using hRQ) hQrange
  · have hQR : Q ≤ R := (Nat.lt_of_not_ge hRQ).le
    calc
      (∑ q ∈ Finset.Icc 1 Q,
          maxCenteredProgressionDiscrepancyUpTo x q) ≤
          ∑ q ∈ Finset.Icc 1 R,
            maxCenteredProgressionDiscrepancyUpTo x q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc le_rfl hQR)
        intro q _ _
        exact maxCenteredProgressionDiscrepancyUpTo_nonneg x q
      _ ≤ (C + 40 * vaughanPrimitiveMeanEquationOneTwoConstant
            (Real.log 4 + 4)) * (x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) A :=
        hbase x hxBase R le_rfl hRrange

end

end BoundedGaps.Maynard
