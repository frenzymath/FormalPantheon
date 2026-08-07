import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthTermConclusion
import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthTermScales

/-!
# Equation (6.15) for Vaughan's fourth term

This file performs the dyadic scale summation for the fourth Vaughan term.
It exports a robust all-parameter form with a totalized nonnegative scale
logarithm and the corrected strict source-context form.

Source: `AkbaryHambrook2013v2`, Section 6, printed p. 23, equation (6.15).
Semantic review: `SEM-458`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Weighted endpoint maxima are bounded by the sum of the separately
weighted fourth-term dyadic block maxima. -/
theorem sum_weightedPrimitiveVaughanTwistedSumFourEndpointMaximum_le_sum_dyadicBlockMaximum
    {U V : ℝ} {x Q : ℕ}
    (hx : 1 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanTwistedSumFourEndpointMaximum U V x q chi.1) ≤
      ∑ alpha ∈ vaughanFourthDyadicExponents U V x,
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ chi : primitiveCharacters q,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 := by
  classical
  let scales := vaughanFourthDyadicExponents U V x
  let weight : ℕ → ℝ := fun q ↦ (q : ℝ) / (q.totient : ℝ)
  have hendpoint :
      (∑ q ∈ Finset.Ioc 0 Q,
        weight q * ∑ chi : primitiveCharacters q,
          vaughanTwistedSumFourEndpointMaximum U V x q chi.1) ≤
        ∑ q ∈ Finset.Ioc 0 Q,
          weight q * ∑ chi : primitiveCharacters q,
            ∑ alpha ∈ scales,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 := by
    apply Finset.sum_le_sum
    intro q _hq
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum
      intro chi _hchi
      exact vaughanTwistedSumFourEndpointMaximum_le_sum_dyadicBlockMaximum
        hU hV hx chi.1
    · dsimp only [weight]
      positivity
  have hreorder :
      (∑ q ∈ Finset.Ioc 0 Q,
        weight q * ∑ chi : primitiveCharacters q,
          ∑ alpha ∈ scales,
            vaughanFourthDyadicBlockMaximum U V x q alpha chi.1) =
        ∑ alpha ∈ scales,
          ∑ q ∈ Finset.Ioc 0 Q,
            weight q * ∑ chi : primitiveCharacters q,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 := by
    have hperq (q : ℕ) :
        weight q * ∑ chi : primitiveCharacters q,
            ∑ alpha ∈ scales,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 =
          ∑ alpha ∈ scales,
            weight q * ∑ chi : primitiveCharacters q,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    calc
      _ = ∑ q ∈ Finset.Ioc 0 Q,
          ∑ alpha ∈ scales,
            weight q * ∑ chi : primitiveCharacters q,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 := by
        apply Finset.sum_congr rfl
        intro q _hq
        exact hperq q
      _ = _ := Finset.sum_comm
  calc
    _ ≤ ∑ q ∈ Finset.Ioc 0 Q,
        weight q * ∑ chi : primitiveCharacters q,
          ∑ alpha ∈ scales,
            vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 := by
      simpa only [weight] using hendpoint
    _ = ∑ alpha ∈ scales,
        ∑ q ∈ Finset.Ioc 0 Q,
          weight q * ∑ chi : primitiveCharacters q,
            vaughanFourthDyadicBlockMaximum U V x q alpha chi.1 := hreorder
    _ = _ := by rfl

/-- Robust all-`Q` form of equation (6.15), conditional on an explicit
global Chebyshev constant. -/
theorem sum_weightedPrimitiveVaughanTwistedSumFourEndpointMaximum_le_of_psi
    {A U V : ℝ} {x Q : ℕ}
    (hA : 0 ≤ A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    (hx : 1 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanTwistedSumFourEndpointMaximum U V x q chi.1) ≤
      vaughanFourthBlockConstant A / Real.log 2 *
        ((x : ℝ) + (Q : ℝ) * (x : ℝ) / Real.sqrt V +
          Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U +
          (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
        (vaughanFourthScaleLog V x * Real.sqrt (vaughanFourthScaleLog V x)) *
        Real.log (Real.exp 3 * V) * Real.log (4 * (x : ℝ)) := by
  classical
  let scales := vaughanFourthDyadicExponents U V x
  let B : ℝ := (x : ℝ) + (Q : ℝ) * (x : ℝ) / Real.sqrt V +
    Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U +
    (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)
  let L : ℝ := vaughanFourthScaleLog V x
  let Vlog : ℝ := Real.log (Real.exp 3 * V)
  let Xlog : ℝ := Real.log (4 * (x : ℝ))
  let C : ℝ := vaughanFourthBlockConstant A * B * Real.sqrt L * Vlog * Xlog
  have hxReal : 0 < (x : ℝ) := by exact_mod_cast hx
  have hxOneReal : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hVpos : 0 < V := zero_lt_one.trans_le hV
  have hLnonneg : 0 ≤ L := by
    exact vaughanFourthScaleLog_nonneg V x
  have hVlogPos : 0 < Vlog := by
    dsimp only [Vlog]
    apply Real.log_pos
    have hExp : 1 < Real.exp (3 : ℝ) := (Real.one_lt_exp_iff).2 (by norm_num)
    nlinarith [mul_pos (Real.exp_pos 3) hVpos]
  have hXlogPos : 0 < Xlog := by
    dsimp only [Xlog]
    exact Real.log_pos (by nlinarith [hxOneReal])
  have hBnonneg : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hConstantNonneg : 0 ≤ vaughanFourthBlockConstant A := by
    unfold vaughanFourthBlockConstant
    positivity [akbaryHambrookC3_pos]
  have hCnonneg : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hbridge :=
    sum_weightedPrimitiveVaughanTwistedSumFourEndpointMaximum_le_sum_dyadicBlockMaximum
      (U := U) (V := V) (x := x) (Q := Q) hx hU hV
  have hsum :
      (∑ q ∈ Finset.Ioc 0 Q,
        (q : ℝ) / (q.totient : ℝ) *
          ∑ chi : primitiveCharacters q,
            vaughanTwistedSumFourEndpointMaximum U V x q chi.1) ≤
        ∑ _alpha ∈ scales, C := by
    apply hbridge.trans
    apply Finset.sum_le_sum
    intro alpha halpha
    let M : ℕ := 2 ^ alpha
    have hMpos : 0 < M := by positivity
    have hMreal : 0 < (M : ℝ) := by exact_mod_cast hMpos
    rcases Finset.mem_filter.mp halpha with
      ⟨_halphaRange, hMlower, hMupper⟩
    change U / 2 < (M : ℝ) at hMlower
    change (M : ℝ) < (x : ℝ) / V at hMupper
    have hRoot :
        Real.sqrt ((x : ℝ) * (M : ℝ)) ≤
          (x : ℝ) / Real.sqrt V := by
      have hroot' : Real.sqrt ((x : ℝ) * (M : ℝ)) ≤
          Real.sqrt ((x : ℝ) * ((x : ℝ) / V)) := by
        apply Real.sqrt_le_sqrt
        exact mul_le_mul_of_nonneg_left hMupper.le hxReal.le
      have heq : Real.sqrt ((x : ℝ) * ((x : ℝ) / V)) =
          (x : ℝ) / Real.sqrt V := by
        rw [Real.sqrt_mul hxReal.le, Real.sqrt_div hxReal.le]
        rw [← mul_div_assoc, Real.mul_self_sqrt hxReal.le]
      rwa [heq] at hroot'
    have hUtwoM : U ≤ 2 * (M : ℝ) := by linarith
    have hsqrtUle : Real.sqrt U ≤ Real.sqrt 2 * Real.sqrt (M : ℝ) := by
      calc
        Real.sqrt U ≤ Real.sqrt (2 * (M : ℝ)) :=
          Real.sqrt_le_sqrt hUtwoM
        _ = Real.sqrt 2 * Real.sqrt (M : ℝ) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hsqrtUpos : 0 < Real.sqrt U := Real.sqrt_pos.2 hUpos
    have hsqrtMpos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.2 hMreal
    have hInv : 1 / Real.sqrt (M : ℝ) ≤
        Real.sqrt 2 / Real.sqrt U := by
      apply (div_le_div_iff₀ hsqrtMpos hsqrtUpos).2
      simpa only [one_mul] using hsqrtUle
    have hRootTerm :
        (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) ≤
          (Q : ℝ) * (x : ℝ) / Real.sqrt V := by
      calc
        _ ≤ (Q : ℝ) * ((x : ℝ) / Real.sqrt V) :=
          mul_le_mul_of_nonneg_left hRoot (Nat.cast_nonneg Q)
        _ = _ := by ring
    have hInvTerm :
        (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) ≤
          Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U := by
      calc
        _ = ((Q : ℝ) * (x : ℝ)) * (1 / Real.sqrt (M : ℝ)) := by ring
        _ ≤ ((Q : ℝ) * (x : ℝ)) *
            (Real.sqrt 2 / Real.sqrt U) :=
          mul_le_mul_of_nonneg_left hInv (by positivity)
        _ = _ := by ring
    have hBlockLe :
        (x : ℝ) +
            (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) +
            (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) +
            (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ) ≤ B := by
      dsimp only [B]
      linarith
    have hLog : Real.log (2 * (M : ℝ)) ≤ L := by
      have hArg : 2 * (M : ℝ) ≤ 2 * (x : ℝ) / V := by
        calc
          2 * (M : ℝ) ≤ 2 * ((x : ℝ) / V) :=
            mul_le_mul_of_nonneg_left hMupper.le (by norm_num)
          _ = 2 * (x : ℝ) / V := by ring
      have hRaw := Real.log_le_log (by positivity) hArg
      dsimp only [L, vaughanFourthScaleLog]
      exact hRaw.trans (le_max_right _ _)
    have hSqrtLog : Real.sqrt (Real.log (2 * (M : ℝ))) ≤
        Real.sqrt L := Real.sqrt_le_sqrt hLog
    have hBlockNonneg : 0 ≤
        (x : ℝ) +
          (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) +
          (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) +
          (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ) := by positivity
    have hBlock :=
      sum_weighted_vaughanFourthDyadicBlockMaximum_le_of_psi
        (A := A) (U := U) (V := V) (x := x) (Q := Q) (alpha := alpha)
        hA hpsi hx hU hV halpha
    apply hBlock.trans
    dsimp only [C]
    calc
      vaughanFourthBlockConstant A *
          ((x : ℝ) +
            (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) +
            (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) +
            (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
          Real.sqrt (Real.log (2 * (M : ℝ))) * Vlog * Xlog ≤
          vaughanFourthBlockConstant A * B *
            Real.sqrt (Real.log (2 * (M : ℝ))) * Vlog * Xlog := by
        gcongr
      _ ≤ vaughanFourthBlockConstant A * B * Real.sqrt L * Vlog * Xlog := by
        gcongr
  have hcard := card_vaughanFourthDyadicExponents_le_scaleLog
    (U := U) hV x
  change ((scales.card : ℕ) : ℝ) ≤ L / Real.log 2 at hcard
  calc
    _ ≤ ∑ _alpha ∈ scales, C := hsum
    _ = (scales.card : ℝ) * C := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (L / Real.log 2) * C :=
      mul_le_mul_of_nonneg_right hcard hCnonneg
    _ = vaughanFourthBlockConstant A / Real.log 2 * B *
        (L * Real.sqrt L) * Vlog * Xlog := by ring
    _ = _ := by rfl

/-- Unconditional robust equation-(6.15) estimate using Mathlib's verified
global Chebyshev constant. -/
theorem sum_weightedPrimitiveVaughanTwistedSumFourEndpointMaximum_le
    {U V : ℝ} {x Q : ℕ}
    (hx : 1 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanTwistedSumFourEndpointMaximum U V x q chi.1) ≤
      vaughanFourthBlockConstant (Real.log 4 + 4) / Real.log 2 *
        ((x : ℝ) + (Q : ℝ) * (x : ℝ) / Real.sqrt V +
          Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U +
          (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
        (vaughanFourthScaleLog V x * Real.sqrt (vaughanFourthScaleLog V x)) *
        Real.log (Real.exp 3 * V) * Real.log (4 * (x : ℝ)) := by
  apply sum_weightedPrimitiveVaughanTwistedSumFourEndpointMaximum_le_of_psi
    (A := Real.log 4 + 4) (U := U) (V := V) (x := x) (Q := Q)
    (by positivity)
  · intro z hz
    exact Chebyshev.psi_le_const_mul_self hz
  · exact hx
  · exact hU
  · exact hV


end

end BoundedGaps.Maynard
