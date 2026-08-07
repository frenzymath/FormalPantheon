import BoundedGaps.BombieriVinogradov.Analytic.VaughanAbelLogSavingCoefficient

/-!
# Logarithmic saving for the Siegel--Walfisz small term

This file absorbs SEM-568's exact small exponential term at the common
`floor ((log x) ^ (A + 5))` cutoff, then combines it with SEM-569's Abel-term
saving. The resulting discrepancy estimate remains globally
Chebyshev-centered and conditional on the total cutoff lying above the
conductor split.

Sources: `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 12.4, printed
pp. 121--122; `AkbaryHambrook2013v2`, Theorem 1.3 and Section 7, printed pp. 3 and
24--25; and `Vaughan1980`, p. 113. The scalar absorption and exact composition
are project-derived. Semantic review: `SEM-570`.
-/

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

noncomputable section

private theorem exists_five_mul_sqrtLog_rpow_le_exp
    (A c : ℝ) (hc : 0 < c) :
    ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ x : ℕ, X0 ≤ x →
        5 * Real.rpow (Real.sqrt (Real.log (x : ℝ))) (4 * A + 12) ≤
          Real.exp (c * Real.sqrt (Real.log (x : ℝ))) := by
  have huTop : Tendsto
      (fun x : ℕ ↦ Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hdom :=
    (((isLittleO_rpow_exp_pos_mul_atTop (4 * A + 12) hc).const_mul_left 5).comp_tendsto
      huTop).eventuallyLE
  rw [Filter.eventually_atTop] at hdom
  obtain ⟨N, hN⟩ := hdom
  refine ⟨max 4 N, le_max_left _ _, ?_⟩
  intro x hx
  have hNx : N ≤ x := (le_max_right 4 N).trans hx
  have huNonneg : 0 ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_nonneg _
  have hleft :
      0 ≤ 5 * (Real.sqrt (Real.log (x : ℝ))) ^ (4 * A + 12) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg huNonneg _)
  have hbound := hN x hNx
  simp only [Function.comp_apply, Real.norm_eq_abs] at hbound
  rw [abs_of_nonneg hleft, abs_of_pos (Real.exp_pos _)] at hbound
  simpa only [Real.rpow_eq_pow] using hbound

/-- The exact SEM-568 small exponential term has an `A`th logarithmic saving.
The threshold depends only on `A,c`, not on the nonnegative coefficient `C` or
the modulus cutoff `Q`. -/
theorem exists_siegelWalfiszSmallTerm_le_logSaving
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    ∃ X0 : ℕ, 4 ≤ X0 ∧
      ∀ C : ℝ, 0 ≤ C →
        ∀ x : ℕ, X0 ≤ x →
          ∀ Q : ℕ,
            siegelWalfiszConductorCutoff (A + 5) x ≤ Q →
              (Q : ℝ) ≤ Real.sqrt (x : ℝ) →
                4 * (((siegelWalfiszConductorCutoff (A + 5) x - 1 : ℕ) : ℝ)) *
                    (1 + Real.log (Q : ℝ)) *
                      (C * ((x : ℝ) * Real.exp
                        (-c * Real.sqrt (Real.log (x : ℝ))))) ≤
                  C * (x : ℝ) /
                    Real.rpow (Real.log (x : ℝ)) A := by
  obtain ⟨X0, hX0, hpolynomial⟩ :=
    exists_five_mul_sqrtLog_rpow_le_exp A c hc
  refine ⟨X0, hX0, ?_⟩
  intro C hC x hx Q hRQ hQsqrt
  have hx4 : 4 ≤ x := hX0.trans hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hlogOne : 1 ≤ Real.log (x : ℝ) := one_le_log_natCast hx4
  have hlogPos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hlogOne
  have hlogNonneg : 0 ≤ Real.log (x : ℝ) := hlogPos.le
  have hApFive : 0 < A + 5 := by linarith
  have hRone : 1 ≤ siegelWalfiszConductorCutoff (A + 5) x :=
    one_le_siegelWalfiszConductorCutoff hApFive hx4
  have hQone : 1 ≤ Q := hRone.trans hRQ
  have hQpos : 0 < Q := Nat.zero_lt_of_lt hQone
  have hQoneReal : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQone
  have hRsubScale :
      (((siegelWalfiszConductorCutoff (A + 5) x - 1 : ℕ) : ℝ)) ≤
        Real.rpow (Real.log (x : ℝ)) (A + 5) := by
    calc
      (((siegelWalfiszConductorCutoff (A + 5) x - 1 : ℕ) : ℝ)) ≤
          (siegelWalfiszConductorCutoff (A + 5) x : ℝ) := by
        exact_mod_cast Nat.sub_le (siegelWalfiszConductorCutoff (A + 5) x) 1
      _ ≤ Real.rpow (Real.log (x : ℝ)) (A + 5) :=
        natCast_siegelWalfiszConductorCutoff_le (A + 5) x
  have hfourLog :
      4 * (1 + Real.log (Q : ℝ)) ≤ 5 * Real.log (x : ℝ) :=
    (four_mul_one_add_log_lt_five_mul_log_of_le_sqrt hx4 hQpos hQsqrt).le
  have hfourLogNonneg : 0 ≤ 4 * (1 + Real.log (Q : ℝ)) := by
    have : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg hQoneReal
    positivity
  have hprefix :
      4 * (((siegelWalfiszConductorCutoff (A + 5) x - 1 : ℕ) : ℝ)) *
          (1 + Real.log (Q : ℝ)) ≤
        5 * Real.rpow (Real.log (x : ℝ)) (A + 6) := by
    calc
      4 * (((siegelWalfiszConductorCutoff (A + 5) x - 1 : ℕ) : ℝ)) *
          (1 + Real.log (Q : ℝ)) =
        (((siegelWalfiszConductorCutoff (A + 5) x - 1 : ℕ) : ℝ)) *
          (4 * (1 + Real.log (Q : ℝ))) := by ring
      _ ≤ Real.rpow (Real.log (x : ℝ)) (A + 5) *
          (5 * Real.log (x : ℝ)) :=
        mul_le_mul hRsubScale hfourLog hfourLogNonneg
          (Real.rpow_nonneg hlogNonneg _)
      _ = 5 * (Real.rpow (Real.log (x : ℝ)) (A + 5) *
          Real.log (x : ℝ)) := by ring
      _ = 5 * (Real.rpow (Real.log (x : ℝ)) (A + 5) *
          Real.rpow (Real.log (x : ℝ)) (1 : ℝ)) :=
        congrArg
          (fun y : ℝ => 5 *
            (Real.rpow (Real.log (x : ℝ)) (A + 5) * y))
          (Real.rpow_one (Real.log (x : ℝ))).symm
      _ = 5 * Real.rpow (Real.log (x : ℝ)) ((A + 5) + 1) :=
        congrArg (fun y : ℝ => 5 * y)
          (Real.rpow_add hlogPos (A + 5) 1).symm
      _ = 5 * Real.rpow (Real.log (x : ℝ)) (A + 6) := by ring_nf
  have hsqrtSq : Real.sqrt (Real.log (x : ℝ)) ^ 2 =
      Real.log (x : ℝ) := Real.sq_sqrt hlogNonneg
  have hpowerIdentity :
      Real.rpow (Real.log (x : ℝ)) (2 * A + 6) =
        Real.rpow (Real.sqrt (Real.log (x : ℝ))) (4 * A + 12) := by
    calc
      Real.rpow (Real.log (x : ℝ)) (2 * A + 6) =
          Real.rpow (Real.sqrt (Real.log (x : ℝ)) ^ 2) (2 * A + 6) := by
        rw [hsqrtSq]
      _ = Real.rpow
          (Real.rpow (Real.sqrt (Real.log (x : ℝ))) (2 : ℝ))
            (2 * A + 6) :=
        congrArg (fun y : ℝ => Real.rpow y (2 * A + 6))
          (Real.rpow_two (Real.sqrt (Real.log (x : ℝ)))).symm
      _ = Real.rpow (Real.sqrt (Real.log (x : ℝ)))
          ((2 : ℝ) * (2 * A + 6)) :=
        (Real.rpow_mul (Real.sqrt_nonneg _) 2 (2 * A + 6)).symm
      _ = Real.rpow (Real.sqrt (Real.log (x : ℝ))) (4 * A + 12) := by
        ring_nf
  have hpolynomialAtX := hpolynomial x hx
  have hdecay :
      5 * Real.rpow (Real.log (x : ℝ)) (2 * A + 6) *
          Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) ≤ 1 := by
    rw [hpowerIdentity]
    calc
      5 * Real.rpow (Real.sqrt (Real.log (x : ℝ))) (4 * A + 12) *
          Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) ≤
        Real.exp (c * Real.sqrt (Real.log (x : ℝ))) *
          Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) :=
        mul_le_mul_of_nonneg_right hpolynomialAtX (Real.exp_pos _).le
      _ = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1
        ring_nf
  have hscaleSplit :
      Real.rpow (Real.log (x : ℝ)) (2 * A + 6) =
        Real.rpow (Real.log (x : ℝ)) (A + 6) *
          Real.rpow (Real.log (x : ℝ)) A := by
    calc
      Real.rpow (Real.log (x : ℝ)) (2 * A + 6) =
          Real.rpow (Real.log (x : ℝ)) ((A + 6) + A) := by ring_nf
      _ = Real.rpow (Real.log (x : ℝ)) (A + 6) *
          Real.rpow (Real.log (x : ℝ)) A :=
        Real.rpow_add hlogPos (A + 6) A
  have hsavePos : 0 < Real.rpow (Real.log (x : ℝ)) A :=
    Real.rpow_pos_of_pos hlogPos _
  have hdecayDiv :
      5 * Real.rpow (Real.log (x : ℝ)) (A + 6) *
          Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) ≤
        1 / Real.rpow (Real.log (x : ℝ)) A := by
    apply (le_div_iff₀ hsavePos).2
    calc
      5 * Real.rpow (Real.log (x : ℝ)) (A + 6) *
            Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) *
          Real.rpow (Real.log (x : ℝ)) A =
        5 * Real.rpow (Real.log (x : ℝ)) (2 * A + 6) *
          Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) := by
        rw [hscaleSplit]
        ring
      _ ≤ 1 := hdecay
  have htailNonneg :
      0 ≤ C * ((x : ℝ) *
        Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by positivity
  calc
    4 * (((siegelWalfiszConductorCutoff (A + 5) x - 1 : ℕ) : ℝ)) *
          (1 + Real.log (Q : ℝ)) *
            (C * ((x : ℝ) * Real.exp
              (-c * Real.sqrt (Real.log (x : ℝ))))) ≤
        (5 * Real.rpow (Real.log (x : ℝ)) (A + 6)) *
          (C * ((x : ℝ) * Real.exp
            (-c * Real.sqrt (Real.log (x : ℝ))))) :=
      mul_le_mul_of_nonneg_right hprefix htailNonneg
    _ = (C * (x : ℝ)) *
        (5 * Real.rpow (Real.log (x : ℝ)) (A + 6) *
          Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) := by ring
    _ ≤ (C * (x : ℝ)) *
        (1 / Real.rpow (Real.log (x : ℝ)) A) :=
      mul_le_mul_of_nonneg_left hdecayDiv (mul_nonneg hC hxpos.le)
    _ = C * (x : ℝ) /
        Real.rpow (Real.log (x : ℝ)) A := by ring

/-- On the shared `A+5` range, SEM-568's complete globally centered
discrepancy sum has the requested logarithmic saving. -/
theorem
    exists_siegelWalfisz_sum_maxCenteredProgressionDiscrepancyUpTo_le_logSaving :
    ∀ A : ℝ, 0 ≤ A →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∃ X0 : ℕ, 4 ≤ X0 ∧
          ∀ x : ℕ, X0 ≤ x →
            ∀ Q : ℕ,
              siegelWalfiszConductorCutoff (A + 5) x ≤ Q →
                (Q : ℝ) ≤ Real.sqrt (x : ℝ) /
                    Real.rpow (Real.log (x : ℝ)) (A + 5) →
                  (∑ q ∈ Finset.Icc 1 Q,
                    maxCenteredProgressionDiscrepancyUpTo x q) ≤
                    (C + 40 * vaughanPrimitiveMeanEquationOneTwoConstant
                      (Real.log 4 + 4)) * (x : ℝ) /
                        Real.rpow (Real.log (x : ℝ)) A := by
  intro A hA
  have hApFive : 0 < A + 5 := by linarith
  obtain ⟨C, c, hC, hc, Xbase, hXbase, hbase⟩ :=
    exists_siegelWalfisz_sum_maxCenteredProgressionDiscrepancyUpTo_le_small_add_equationOneTwo
      (A + 5) hApFive
  obtain ⟨Xsmall, hXsmall, hsmall⟩ :=
    exists_siegelWalfiszSmallTerm_le_logSaving A c hA hc
  obtain ⟨Xabel, hXabel, habel⟩ :=
    exists_vaughanPrimitiveMeanEquationOneTwoAbelTerm_le_logSaving A hA
  refine ⟨C, c, hC, hc, max Xbase (max Xsmall Xabel),
    hXbase.trans (le_max_left _ _), ?_⟩
  intro x hx Q hRQ hQrange
  have hxBase : Xbase ≤ x := (le_max_left Xbase (max Xsmall Xabel)).trans hx
  have hxPair : max Xsmall Xabel ≤ x :=
    (le_max_right Xbase (max Xsmall Xabel)).trans hx
  have hxSmall : Xsmall ≤ x := (le_max_left Xsmall Xabel).trans hxPair
  have hxAbel : Xabel ≤ x := (le_max_right Xsmall Xabel).trans hxPair
  have hx4 : 4 ≤ x := hXbase.trans hxBase
  have hlogOne : 1 ≤ Real.log (x : ℝ) := one_le_log_natCast hx4
  have hscaleOne :
      1 ≤ Real.rpow (Real.log (x : ℝ)) (A + 5) :=
    Real.one_le_rpow hlogOne hApFive.le
  have hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ) :=
    hQrange.trans (div_le_self (Real.sqrt_nonneg _) hscaleOne)
  have hbaseAtX := hbase x hxBase Q hRQ hQsqrt
  have hsmallAtX := hsmall C hC.le x hxSmall Q hRQ hQsqrt
  have habelAtX := habel x hxAbel Q hRQ hQrange
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        maxCenteredProgressionDiscrepancyUpTo x q) ≤
        4 * (((siegelWalfiszConductorCutoff (A + 5) x - 1 : ℕ) : ℝ)) *
          (1 + Real.log (Q : ℝ)) *
            (C * ((x : ℝ) * Real.exp
              (-c * Real.sqrt (Real.log (x : ℝ))))) +
          vaughanPrimitiveMeanEquationOneTwoConstant (Real.log 4 + 4) *
            vaughanPrimitiveMeanAbelEnvelope x
              (siegelWalfiszConductorCutoff (A + 5) x : ℝ) Q *
              vaughanPrimitiveMeanEquationOneTwoLogPower x := hbaseAtX
    _ ≤ C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A +
        (40 * vaughanPrimitiveMeanEquationOneTwoConstant
          (Real.log 4 + 4)) * (x : ℝ) /
            Real.rpow (Real.log (x : ℝ)) A :=
      add_le_add hsmallAtX habelAtX
    _ = (C + 40 * vaughanPrimitiveMeanEquationOneTwoConstant
          (Real.log 4 + 4)) * (x : ℝ) /
        Real.rpow (Real.log (x : ℝ)) A := by ring

end

end BoundedGaps.Maynard
