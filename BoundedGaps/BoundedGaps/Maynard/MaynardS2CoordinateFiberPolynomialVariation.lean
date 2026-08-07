import BoundedGaps.Maynard.ConcreteS2PolynomialBound

set_option maxHeartbeats 800000
set_option maxRecDepth 5000

noncomputable section

namespace BoundedGaps.Maynard

open Finset MeasureTheory Real
open scoped BigOperators

/-!
# Uniform variation of the concrete S2 coordinate polynomial

SEM-390 supplies the endpoint-plus-variation envelope required after the
coordinate-fiber Abel transfer. Maynard2013v3, Section 6, Lemma 6.1 and
equations (6.10)--(6.14), uses the corresponding one-variable smooth-function
envelope. The concrete polynomial comes from Section 8, equation (8.1) and
Lemma 8.2. This file differentiates only the global polynomial representative
along the strict arithmetic path; it does not differentiate the simplex zero
extension across its boundary.
-/

theorem integral_abs_deriv_normalizedLog_comp
    {Q R : ℕ} (hQ : 1 < Q) (hR : 1 < R)
    {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) :
    (∫ t in Set.Ioc (1 : ℝ) Q,
      |deriv (fun z => G (Real.log z / Real.log R)) t|) =
      ∫ x in (0 : ℝ)..(Real.log Q / Real.log R), |deriv G x| := by
  have hQreal : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hRreal : (1 : ℝ) < R := by exact_mod_cast hR
  have hlogR : 0 < Real.log R := Real.log_pos hRreal
  let q : ℝ → ℝ := fun t => Real.log t / Real.log R
  let q' : ℝ → ℝ := fun t => t⁻¹ / Real.log R
  have hxPos : ∀ x ∈ Set.uIcc (1 : ℝ) Q, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hQreal.le] at hx
    exact zero_lt_one.trans_le hx.1
  have hq : ∀ x ∈ Set.uIcc (1 : ℝ) Q, HasDerivAt q (q' x) x := by
    intro x hx
    exact (Real.hasDerivAt_log (hxPos x hx).ne').div_const (Real.log R)
  have hq' : ContinuousOn q' (Set.uIcc (1 : ℝ) Q) := by
    exact (continuousOn_id.inv₀ fun x hx => (hxPos x hx).ne').div_const _
  have hGderiv : Continuous (fun x => |deriv G x|) :=
    (hG.continuous_deriv (by simp)).abs
  have hsub := intervalIntegral.integral_comp_mul_deriv hq hq' hGderiv
  change (∫ t in Set.Ioc (1 : ℝ) Q, |deriv (G ∘ q) t|) = _
  rw [← intervalIntegral.integral_of_le hQreal.le]
  calc
    (∫ t in (1 : ℝ)..Q, |deriv (G ∘ q) t|) =
        ∫ t in (1 : ℝ)..Q, ((fun x => |deriv G x|) ∘ q) t * q' t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htPos : 0 < t := hxPos t ht
      have hGdiff : DifferentiableAt ℝ G (q t) :=
        (hG.differentiable (by simp)).differentiableAt
      have hcomp : HasDerivAt (G ∘ q) (deriv G (q t) * q' t) t :=
        hGdiff.hasDerivAt.comp t (hq t ht)
      have hq'nonneg : 0 ≤ q' t := by
        dsimp [q']
        exact div_nonneg (inv_nonneg.mpr htPos.le) hlogR.le
      change |deriv (G ∘ q) t| = |deriv G (q t)| * q' t
      rw [hcomp.deriv, abs_mul, abs_of_nonneg hq'nonneg]
    _ = ∫ x in q 1..q Q, |deriv G x| := hsub
    _ = ∫ x in (0 : ℝ)..(Real.log Q / Real.log R), |deriv G x| := by
      simp [q]

theorem deriv_smallKRealPolynomial_update
    (t : Fin 105 → ℝ) (m : Fin 105) (x : ℝ) :
    deriv (fun z => smallKRealPolynomial (Function.update t m z)) x =
      ∑ i : Fin 42,
        smallKRealCoefficient i *
          ((-(smallKExponentB i : ℝ)) *
              (1 - smallKRealP1 (Function.update t m x)) ^
                (smallKExponentB i - 1) *
              smallKRealP2 (Function.update t m x) ^ smallKExponentC i +
            (1 - smallKRealP1 (Function.update t m x)) ^
                smallKExponentB i *
              ((smallKExponentC i : ℝ) *
                smallKRealP2 (Function.update t m x) ^
                  (smallKExponentC i - 1) * (2 * x))) := by
  have hP1fun : (fun z => smallKRealP1 (Function.update t m z)) =
      fun z => z + ∑ j ∈ (Finset.univ : Finset (Fin 105)) \ {m}, t j := by
    funext z
    unfold smallKRealP1
    rw [Finset.sum_update_of_mem (Finset.mem_univ m)]
  have hP2fun : (fun z => smallKRealP2 (Function.update t m z)) =
      fun z => z ^ 2 +
        ∑ j ∈ (Finset.univ : Finset (Fin 105)) \ {m}, (t j) ^ 2 := by
    funext z
    unfold smallKRealP2
    have heq : (fun j => Function.update t m z j ^ 2) =
        Function.update (fun j => t j ^ 2) m (z ^ 2) := by
      funext j
      by_cases hj : j = m <;> simp [hj]
    rw [heq, Finset.sum_update_of_mem (Finset.mem_univ m)]
  have hP1 : HasDerivAt
      (fun z => smallKRealP1 (Function.update t m z)) 1 x := by
    rw [hP1fun]
    simpa using (hasDerivAt_id x).add_const
      (∑ j ∈ (Finset.univ : Finset (Fin 105)) \ {m}, t j)
  have hP2 : HasDerivAt
      (fun z => smallKRealP2 (Function.update t m z)) (2 * x) x := by
    rw [hP2fun]
    simpa using (hasDerivAt_pow 2 x).add_const
      (∑ j ∈ (Finset.univ : Finset (Fin 105)) \ {m}, (t j) ^ 2)
  unfold smallKRealPolynomial
  apply (HasDerivAt.fun_sum (u := Finset.univ) (x := x) ?_).deriv
  intro i hi
  have hA : HasDerivAt
      (fun z => 1 - smallKRealP1 (Function.update t m z)) (-1) x := by
    simpa using hP1.const_sub (1 : ℝ)
  have hterm := (hA.pow (smallKExponentB i)).mul
    (hP2.pow (smallKExponentC i))
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    hterm.const_mul (smallKRealCoefficient i)

private theorem smallKMonomialDerivative_abs_le
    (a U V x : ℝ) (b c : ℕ)
    (hU : |U| ≤ 106) (hV : |V| ≤ 105) (hx : |x| ≤ 1)
    (hdeg : b + 2 * c ≤ 11) :
    |a * ((b : ℝ) * U ^ (b - 1) * (-1) * V ^ c +
      U ^ b * ((c : ℝ) * V ^ (c - 1) * (2 * x)))| ≤
      11 * (|a| * 106 ^ b * 105 ^ c) := by
  have hbabs : |(b : ℝ)| = (b : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg b)
  have hcabs : |(c : ℝ)| = (c : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg c)
  have h2abs : |(2 : ℝ)| = 2 := by norm_num
  have hUb : |U| ^ b ≤ (106 : ℝ) ^ b :=
    pow_le_pow_left₀ (abs_nonneg U) hU b
  have hUbPred : |U| ^ (b - 1) ≤ (106 : ℝ) ^ b :=
    (pow_le_pow_left₀ (abs_nonneg U) hU (b - 1)).trans
      (pow_le_pow_right₀ (by norm_num) (Nat.sub_le b 1))
  have hVc : |V| ^ c ≤ (105 : ℝ) ^ c :=
    pow_le_pow_left₀ (abs_nonneg V) hV c
  have hVcPred : |V| ^ (c - 1) ≤ (105 : ℝ) ^ c :=
    (pow_le_pow_left₀ (abs_nonneg V) hV (c - 1)).trans
      (pow_le_pow_right₀ (by norm_num) (Nat.sub_le c 1))
  have hfirst : |(b : ℝ) * U ^ (b - 1) * (-1) * V ^ c| ≤
      (b : ℝ) * 106 ^ b * 105 ^ c := by
    simp only [abs_mul, abs_pow, hbabs, abs_neg, abs_one, mul_one]
    gcongr
  have hsecond : |U ^ b * ((c : ℝ) * V ^ (c - 1) * (2 * x))| ≤
      ((2 * c : ℕ) : ℝ) * 106 ^ b * 105 ^ c := by
    simp only [abs_mul, abs_pow, hcabs, h2abs]
    calc
      |U| ^ b * ((c : ℝ) * |V| ^ (c - 1) * (2 * |x|)) ≤
          106 ^ b * ((c : ℝ) * 105 ^ c * (2 * 1)) := by gcongr
      _ = ((2 * c : ℕ) : ℝ) * 106 ^ b * 105 ^ c := by
        push_cast
        ring
  rw [abs_mul]
  calc
    |a| * |(b : ℝ) * U ^ (b - 1) * (-1) * V ^ c +
        U ^ b * ((c : ℝ) * V ^ (c - 1) * (2 * x))| ≤
      |a| * (|(b : ℝ) * U ^ (b - 1) * (-1) * V ^ c| +
        |U ^ b * ((c : ℝ) * V ^ (c - 1) * (2 * x))|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ |a| * (((b : ℝ) * 106 ^ b * 105 ^ c) +
        (((2 * c : ℕ) : ℝ) * 106 ^ b * 105 ^ c)) := by gcongr
    _ = ((b + 2 * c : ℕ) : ℝ) *
        (|a| * 106 ^ b * 105 ^ c) := by
      push_cast
      ring
    _ ≤ 11 * (|a| * 106 ^ b * 105 ^ c) := by
      gcongr
      exact_mod_cast hdeg

theorem abs_deriv_engelsmaS2CoordinateFiberPolynomialTest_le_of_cube
    (R : ℕ) (m : BoundedGaps.engelsmaTuple)
    (r : BoundedGaps.engelsmaTuple → ℕ) (x : ℝ)
    (hx : ∀ h : BoundedGaps.engelsmaTuple,
      (Function.update (fun h => Real.log (r h) / Real.log R) m x) h ∈
        Set.Icc (0 : ℝ) 1) :
    |deriv (engelsmaS2CoordinateFiberPolynomialTest R m r) x| ≤
      11 * smallKCandidateBound := by
  let base : Fin 105 → ℝ := fun i =>
    Real.log (r (engelsmaIndexEquiv.symm i)) / Real.log R
  let mi : Fin 105 := engelsmaIndexEquiv m
  let u : Fin 105 → ℝ := Function.update base mi x
  have hu : u ∈ maynardCube 105 := by
    rw [maynardCube, maynardCubeOf, Set.mem_pi]
    intro i hi
    have hupdate : u i =
        Function.update (fun h => Real.log (r h) / Real.log R) m x
          (engelsmaIndexEquiv.symm i) := by
      by_cases him : i = mi
      · subst i
        simp [u, mi, base]
      · have hsymm : engelsmaIndexEquiv.symm i ≠ m := by
          intro h
          apply him
          simpa [mi] using congrArg engelsmaIndexEquiv h
        simp [u, mi, base, him, hsymm]
    rw [hupdate]
    exact hx (engelsmaIndexEquiv.symm i)
  have hfun : engelsmaS2CoordinateFiberPolynomialTest R m r =
      fun z => smallKRealPolynomial (Function.update base mi z) := by
    funext z
    unfold engelsmaS2CoordinateFiberPolynomialTest
      maynardS2CoordinateFiberTest engelsmaSmallKPolynomial
    congr 1
    funext i
    by_cases him : i = mi
    · subst i
      simp [mi, base]
    · have hsymm : engelsmaIndexEquiv.symm i ≠ m := by
        intro h
        apply him
        simpa [mi] using congrArg engelsmaIndexEquiv h
      simp [mi, base, him, hsymm]
  have hU : |1 - smallKRealP1 u| ≤ 106 := by
    rw [← Real.norm_eq_abs]
    calc
      ‖1 - smallKRealP1 u‖ ≤ ‖(1 : ℝ)‖ + ‖smallKRealP1 u‖ :=
        norm_sub_le _ _
      _ = 1 + ‖smallKRealP1 u‖ := by norm_num
      _ ≤ 106 := by linarith [smallKRealP1_norm_le u hu]
  have hV : |smallKRealP2 u| ≤ 105 := by
    rw [abs_of_nonneg (smallKRealP2_nonneg u)]
    exact smallKRealP2_le u hu
  have hx' : |x| ≤ 1 := by
    have hm := hx m
    simpa using (abs_le.2 ⟨by linarith [hm.1], hm.2⟩)
  rw [hfun, deriv_smallKRealPolynomial_update]
  calc
    |∑ i : Fin 42,
        smallKRealCoefficient i *
          ((-(smallKExponentB i : ℝ)) *
              (1 - smallKRealP1 u) ^ (smallKExponentB i - 1) *
              smallKRealP2 u ^ smallKExponentC i +
            (1 - smallKRealP1 u) ^ smallKExponentB i *
              ((smallKExponentC i : ℝ) *
                smallKRealP2 u ^ (smallKExponentC i - 1) * (2 * x)))| ≤
      ∑ i : Fin 42,
        |smallKRealCoefficient i *
          ((-(smallKExponentB i : ℝ)) *
              (1 - smallKRealP1 u) ^ (smallKExponentB i - 1) *
              smallKRealP2 u ^ smallKExponentC i +
            (1 - smallKRealP1 u) ^ smallKExponentB i *
              ((smallKExponentC i : ℝ) *
                smallKRealP2 u ^ (smallKExponentC i - 1) * (2 * x)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 42,
        11 * (|smallKRealCoefficient i| *
          106 ^ smallKExponentB i * 105 ^ smallKExponentC i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hmono := smallKMonomialDerivative_abs_le
        (smallKRealCoefficient i) (1 - smallKRealP1 u)
          (smallKRealP2 u) x (smallKExponentB i) (smallKExponentC i)
          hU hV hx' (smallK_exponent_bound i)
      have heq :
          smallKRealCoefficient i *
              ((-(smallKExponentB i : ℝ)) *
                  (1 - smallKRealP1 u) ^ (smallKExponentB i - 1) *
                  smallKRealP2 u ^ smallKExponentC i +
                (1 - smallKRealP1 u) ^ smallKExponentB i *
                  ((smallKExponentC i : ℝ) *
                    smallKRealP2 u ^ (smallKExponentC i - 1) * (2 * x))) =
            smallKRealCoefficient i *
              ((smallKExponentB i : ℝ) *
                  (1 - smallKRealP1 u) ^ (smallKExponentB i - 1) * (-1) *
                  smallKRealP2 u ^ smallKExponentC i +
                (1 - smallKRealP1 u) ^ smallKExponentB i *
                  ((smallKExponentC i : ℝ) *
                    smallKRealP2 u ^ (smallKExponentC i - 1) * (2 * x))) := by
        ring
      rw [heq]
      exact hmono
    _ = 11 * smallKCandidateBound := by
      unfold smallKCandidateBound
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.norm_eq_abs]

theorem engelsmaS2CoordinateFiberPolynomial_endpoint_add_variation_le
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) r)
    (hR : 1 < R)
    (hQ : 1 < maynardS2CoordinateFiberEndpoint R
      (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) :
    |engelsmaS2CoordinateFiberPolynomialTest R m r
        (Real.log (maynardS2CoordinateFiberEndpoint R
          (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)) /
          Real.log R)| +
      ∫ t in Set.Ioc (1 : ℝ)
          (maynardS2CoordinateFiberEndpoint R
            (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)),
        |deriv (fun z =>
          engelsmaS2CoordinateFiberPolynomialTest R m r
            (Real.log z / Real.log R)) t| ≤
      12 * smallKCandidateBound := by
  let Q : ℕ := maynardS2CoordinateFiberEndpoint R
    (maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r)
  let a : ℝ := Real.log Q / Real.log R
  let G : ℝ → ℝ := engelsmaS2CoordinateFiberPolynomialTest R m r
  have hQreal : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hRreal : (1 : ℝ) < R := by exact_mod_cast hR
  have hlogR : 0 < Real.log R := Real.log_pos hRreal
  have hlogQ : 0 ≤ Real.log Q := (Real.log_pos hQreal).le
  have ha0 : 0 ≤ a := div_nonneg hlogQ hlogR.le
  have hQle : Q ≤ R := by
    unfold Q maynardS2CoordinateFiberEndpoint
    exact (Nat.div_le_self _ _).trans (by omega)
  have ha1 : a ≤ 1 := by
    apply (div_le_iff₀ hlogR).2
    have hQpos : (0 : ℝ) < Q := by exact_mod_cast (Nat.zero_lt_of_lt hQ)
    have hRpos : (0 : ℝ) < R := by exact_mod_cast (Nat.zero_lt_of_lt hR)
    have hlogle : Real.log Q ≤ Real.log R :=
      Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hQpos)
        (Set.mem_Ioi.mpr hRpos) (by exact_mod_cast hQle)
    simpa [a] using hlogle
  have hGsmooth : ContDiff ℝ (⊤ : ℕ∞) G := by
    dsimp [G]
    exact contDiff_engelsmaS2CoordinateFiberPolynomialTest R m r
  have hGone : ContDiff ℝ 1 G := hGsmooth.of_le (by simp)
  have hderivCont : Continuous (fun x => |deriv G x|) :=
    (hGone.continuous_deriv (by simp)).abs
  have hpoint : ∀ x ∈ Set.Icc (0 : ℝ) a,
      |deriv G x| ≤ 11 * smallKCandidateBound := by
    intro x hx
    have hxu : x ∈ Set.uIcc (0 : ℝ) a := by
      rw [Set.uIcc_of_le ha0]
      exact hx
    have hcube :=
      engelsmaS2CoordinateFiberPolynomialTest_mem_cube_on_endpoint_interval
        (m := m) (r := r) hr hR hQ x hxu
    simpa [G] using
      abs_deriv_engelsmaS2CoordinateFiberPolynomialTest_le_of_cube
        R m r x hcube
  have hC : 0 ≤ 11 * smallKCandidateBound :=
    mul_nonneg (by norm_num) smallKCandidateBound_nonneg
  have hvarX :
      (∫ x in (0 : ℝ)..a, |deriv G x|) ≤
        11 * smallKCandidateBound * a := by
    calc
      (∫ x in (0 : ℝ)..a, |deriv G x|) ≤
          ∫ _x in (0 : ℝ)..a, 11 * smallKCandidateBound :=
        intervalIntegral.integral_mono_on ha0
          (hderivCont.intervalIntegrable 0 a)
          (continuous_const.intervalIntegrable 0 a) hpoint
      _ = 11 * smallKCandidateBound * a := by
        simp
        ring
  have hvarXUniform :
      (∫ x in (0 : ℝ)..a, |deriv G x|) ≤
        11 * smallKCandidateBound := by
    apply hvarX.trans
    nlinarith
  have hvariation :
      (∫ t in Set.Ioc (1 : ℝ) Q,
        |deriv (fun z => G (Real.log z / Real.log R)) t|) ≤
          11 * smallKCandidateBound := by
    rw [integral_abs_deriv_normalizedLog_comp hQ hR hGone]
    simpa [a] using hvarXUniform
  have hendpoint :
      |G a| ≤ smallKCandidateBound := by
    have haMem : a ∈ Set.uIcc (0 : ℝ) a := by
      rw [Set.uIcc_of_le ha0]
      exact ⟨ha0, le_rfl⟩
    have hnorm :=
      engelsmaS2CoordinateFiberPolynomialTest_norm_le_on_endpoint_interval
        (m := m) (r := r) hr hR hQ a haMem
    simpa [G, a, Real.norm_eq_abs] using hnorm
  change |G a| +
      (∫ t in Set.Ioc (1 : ℝ) Q,
        |deriv (fun z => G (Real.log z / Real.log R)) t|) ≤ _
  calc
    |G a| +
        (∫ t in Set.Ioc (1 : ℝ) Q,
          |deriv (fun z => G (Real.log z / Real.log R)) t|) ≤
        smallKCandidateBound + 11 * smallKCandidateBound :=
      add_le_add hendpoint hvariation
    _ = 12 * smallKCandidateBound := by ring

end BoundedGaps.Maynard
