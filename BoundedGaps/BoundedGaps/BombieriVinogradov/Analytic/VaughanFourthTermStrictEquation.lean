import BoundedGaps.BombieriVinogradov.Analytic.VaughanFourthTermEquation

/-!
# Strict equation (6.15) for Vaughan's fourth term

This file exports the corrected strict source-context form of
Akbary--Hambrook equation (6.15).

Source: `AkbaryHambrook2013v2`, Section 6, printed p. 23, equation (6.15).
Semantic review: `SEM-458`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Corrected strict source-context form of Akbary--Hambrook equation (6.15).
The additional condition `V < 2*x` is necessary for the printed logarithmic
right side to be positive. -/
theorem sum_weightedPrimitiveVaughanTwistedSumFourEndpointMaximum_lt_of_psi
    {A U V : ℝ} {x Q : ℕ}
    (hA : 0 < A)
    (hpsi : ∀ z : ℝ, 0 ≤ z → Chebyshev.psi z ≤ A * z)
    (hx : 4 ≤ x) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hVx : V < 2 * (x : ℝ))
    (hQ : 2 ≤ Q) (_hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (∑ q ∈ Finset.Ioc 0 Q,
      (q : ℝ) / (q.totient : ℝ) *
        ∑ chi : primitiveCharacters q,
          vaughanTwistedSumFourEndpointMaximum U V x q chi.1) <
      vaughanFourthBlockConstant A / Real.log 2 *
        ((x : ℝ) + (Q : ℝ) * (x : ℝ) / Real.sqrt V +
          Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U +
          (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
        (Real.log (2 * (x : ℝ) / V) *
          Real.sqrt (Real.log (2 * (x : ℝ) / V))) *
        Real.log (Real.exp 3 * V) * Real.log (4 * (x : ℝ)) := by
  classical
  let scales := vaughanFourthDyadicExponents U V x
  let B : ℝ := (x : ℝ) + (Q : ℝ) * (x : ℝ) / Real.sqrt V +
    Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U +
    (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)
  let L : ℝ := Real.log (2 * (x : ℝ) / V)
  let Vlog : ℝ := Real.log (Real.exp 3 * V)
  let Xlog : ℝ := Real.log (4 * (x : ℝ))
  let C : ℝ := vaughanFourthBlockConstant A * B * Real.sqrt L * Vlog * Xlog
  have hxOne : 1 ≤ x := by omega
  have hxReal : 0 < (x : ℝ) := by
    exact_mod_cast (show 0 < x by omega)
  have hxFourReal : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hQReal : 0 < (Q : ℝ) := by
    exact_mod_cast (show 0 < Q by omega)
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hVpos : 0 < V := zero_lt_one.trans_le hV
  have hRatio : 1 < 2 * (x : ℝ) / V :=
    (lt_div_iff₀ hVpos).2 (by simpa only [one_mul] using hVx)
  have hLpos : 0 < L := by
    dsimp only [L]
    exact Real.log_pos hRatio
  have hScaleLog : vaughanFourthScaleLog V x = L := by
    rw [vaughanFourthScaleLog, max_eq_right]
    exact hLpos.le
  have hVlogPos : 0 < Vlog := by
    dsimp only [Vlog]
    apply Real.log_pos
    have hExp : 1 < Real.exp (3 : ℝ) := (Real.one_lt_exp_iff).2 (by norm_num)
    nlinarith [mul_pos (Real.exp_pos 3) hVpos]
  have hXlogPos : 0 < Xlog := by
    dsimp only [Xlog]
    exact Real.log_pos (by nlinarith [hxFourReal])
  have hBpos : 0 < B := by
    dsimp only [B]
    positivity
  have hConstantPos : 0 < vaughanFourthBlockConstant A := by
    unfold vaughanFourthBlockConstant
    positivity [akbaryHambrookC3_pos]
  have hCpos : 0 < C := by
    dsimp only [C]
    positivity
  have hbridge :=
    sum_weightedPrimitiveVaughanTwistedSumFourEndpointMaximum_le_sum_dyadicBlockMaximum
      (U := U) (V := V) (x := x) (Q := Q) hxOne hU hV
  by_cases hscales : scales = ∅
  · have hleft :
        (∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ chi : primitiveCharacters q,
              vaughanTwistedSumFourEndpointMaximum U V x q chi.1) ≤ 0 := by
      simpa only [scales, hscales, Finset.sum_empty] using hbridge
    have hright : 0 <
        vaughanFourthBlockConstant A / Real.log 2 * B *
          (L * Real.sqrt L) * Vlog * Xlog := by
      positivity
    exact hleft.trans_lt (by simpa only [B, L, Vlog, Xlog] using hright)
  have hscalesNonempty : scales.Nonempty := Finset.nonempty_iff_ne_empty.mpr hscales
  have hsumStrict :
      (∑ alpha ∈ scales,
        ∑ q ∈ Finset.Ioc 0 Q,
          (q : ℝ) / (q.totient : ℝ) *
            ∑ chi : primitiveCharacters q,
              vaughanFourthDyadicBlockMaximum U V x q alpha chi.1) <
        ∑ _alpha ∈ scales, C := by
    apply Finset.sum_lt_sum_of_nonempty hscalesNonempty
    intro alpha halpha
    let M : ℕ := 2 ^ alpha
    have hMpos : 0 < M := by positivity
    have hMreal : 0 < (M : ℝ) := by exact_mod_cast hMpos
    rcases Finset.mem_filter.mp halpha with
      ⟨_halphaRange, hMlower, hMupper⟩
    change U / 2 < (M : ℝ) at hMlower
    change (M : ℝ) < (x : ℝ) / V at hMupper
    have hRoot : Real.sqrt ((x : ℝ) * (M : ℝ)) ≤
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
    have hUtwoM : U < 2 * (M : ℝ) := by linarith
    have hsqrtUstrict : Real.sqrt U <
        Real.sqrt 2 * Real.sqrt (M : ℝ) := by
      calc
        Real.sqrt U < Real.sqrt (2 * (M : ℝ)) :=
          Real.sqrt_lt_sqrt hUpos.le hUtwoM
        _ = Real.sqrt 2 * Real.sqrt (M : ℝ) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hsqrtUpos : 0 < Real.sqrt U := Real.sqrt_pos.2 hUpos
    have hsqrtMpos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.2 hMreal
    have hInvStrict : 1 / Real.sqrt (M : ℝ) <
        Real.sqrt 2 / Real.sqrt U := by
      apply (div_lt_div_iff₀ hsqrtMpos hsqrtUpos).2
      simpa only [one_mul] using hsqrtUstrict
    have hRootTerm :
        (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) ≤
          (Q : ℝ) * (x : ℝ) / Real.sqrt V := by
      calc
        _ ≤ (Q : ℝ) * ((x : ℝ) / Real.sqrt V) :=
          mul_le_mul_of_nonneg_left hRoot hQReal.le
        _ = _ := by ring
    have hInvTerm :
        (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) <
          Real.sqrt 2 * (Q : ℝ) * (x : ℝ) / Real.sqrt U := by
      calc
        _ = ((Q : ℝ) * (x : ℝ)) * (1 / Real.sqrt (M : ℝ)) := by ring
        _ < ((Q : ℝ) * (x : ℝ)) *
            (Real.sqrt 2 / Real.sqrt U) :=
          mul_lt_mul_of_pos_left hInvStrict (mul_pos hQReal hxReal)
        _ = _ := by ring
    have hBlockStrict :
        (x : ℝ) +
            (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) +
            (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) +
            (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ) < B := by
      dsimp only [B]
      linarith
    have hLog : Real.log (2 * (M : ℝ)) ≤ L := by
      dsimp only [L]
      apply Real.log_le_log (by positivity)
      calc
        2 * (M : ℝ) ≤ 2 * ((x : ℝ) / V) :=
          mul_le_mul_of_nonneg_left hMupper.le (by norm_num)
        _ = 2 * (x : ℝ) / V := by ring
    have hSqrtLog : Real.sqrt (Real.log (2 * (M : ℝ))) ≤
        Real.sqrt L := Real.sqrt_le_sqrt hLog
    have hSqrtLogPos : 0 < Real.sqrt (Real.log (2 * (M : ℝ))) := by
      apply Real.sqrt_pos.2
      apply Real.log_pos
      exact_mod_cast (show 1 < 2 * M by omega)
    have hBlock :=
      sum_weighted_vaughanFourthDyadicBlockMaximum_le_of_psi
        (A := A) (U := U) (V := V) (x := x) (Q := Q) (alpha := alpha)
        hA.le hpsi hxOne hU hV halpha
    apply hBlock.trans_lt
    calc
      vaughanFourthBlockConstant A *
          ((x : ℝ) +
            (Q : ℝ) * Real.sqrt ((x : ℝ) * (M : ℝ)) +
            (Q : ℝ) * (x : ℝ) / Real.sqrt (M : ℝ) +
            (Q : ℝ) ^ 2 * Real.sqrt (x : ℝ)) *
          Real.sqrt (Real.log (2 * (M : ℝ))) * Vlog * Xlog <
          vaughanFourthBlockConstant A * B *
            Real.sqrt (Real.log (2 * (M : ℝ))) * Vlog * Xlog := by
        gcongr
      _ ≤ vaughanFourthBlockConstant A * B * Real.sqrt L * Vlog * Xlog := by
        gcongr
  have hcard := card_vaughanFourthDyadicExponents_le_scaleLog
    (U := U) hV x
  rw [hScaleLog] at hcard
  change ((scales.card : ℕ) : ℝ) ≤ L / Real.log 2 at hcard
  calc
    _ < ∑ _alpha ∈ scales, C := hbridge.trans_lt hsumStrict
    _ = (scales.card : ℝ) * C := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (L / Real.log 2) * C :=
      mul_le_mul_of_nonneg_right hcard hCpos.le
    _ = vaughanFourthBlockConstant A / Real.log 2 * B *
        (L * Real.sqrt L) * Vlog * Xlog := by ring
    _ = _ := by rfl

end

end BoundedGaps.Maynard
