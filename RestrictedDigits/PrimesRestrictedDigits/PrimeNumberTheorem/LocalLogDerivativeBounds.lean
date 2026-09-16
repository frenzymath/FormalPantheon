import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import PrimesRestrictedDigits.PrimeNumberTheorem.LocalLogDerivativeCanonical

/-!
# Bounds for a local logarithmic derivative

This file proves the quantitative complex-analysis estimates used to assemble
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Lemma 6.3 at the fixed radii needed for
the zeta application.
-/

open Complex Metric Set
open MeromorphicOn

namespace PrimesRestrictedDigits

/-- A canonical zero product has norm one on its defining circle. -/
theorem norm_canonicalZeroProduct_eq_one_of_mem_sphere
    {f : Complex -> Complex} {A : Real}
    (hf : AnalyticOnNhd Complex f (closedBall 0 A))
    {z : Complex} (hz : z ∈ sphere (0 : Complex) A) :
    ‖canonicalZeroProduct f A z‖ = 1 := by
  let D := MeromorphicOn.divisor f (ball (0 : Complex) A)
  let fac : Complex -> Complex -> Complex := fun w =>
    (Complex.canonicalFactor A w) ^ (-D w)
  have hD : D.support.Finite := hf.meromorphicOn.divisor_ball_support_finite
  have hmul : Function.mulSupport fac ⊆ D.support := by
    intro w hw
    contrapose! hw
    have hDw : D w = 0 := by
      simpa [Function.mem_support] using hw
    simp [fac, hDw]
  rw [canonicalZeroProduct,
    finprod_eq_prod_of_mulSupport_subset_of_finite _ hmul hD]
  simp only [Finset.prod_apply, norm_prod]
  apply Finset.prod_eq_one
  intro w hw
  change ‖Complex.canonicalFactor A w z ^ (-D w)‖ = 1
  rw [norm_zpow, Complex.norm_canonicalFactor_eval_circle_eq_one
    (D.supportWithinDomain (hD.mem_toFinset.mp hw)) hz, one_zpow]

/-- At the origin, the reciprocal canonical product has norm at most one. -/
theorem norm_canonicalZeroProduct_zero_le_one
    {f : Complex -> Complex} {A : Real} (hA : 0 < A)
    (hf : AnalyticOnNhd Complex f (closedBall 0 A)) (hf0 : f 0 ≠ 0) :
    ‖canonicalZeroProduct f A 0‖ ≤ 1 := by
  let D := MeromorphicOn.divisor f (ball (0 : Complex) A)
  let fac : Complex -> Complex -> Complex := fun w =>
    (Complex.canonicalFactor A w) ^ (-D w)
  have hD : D.support.Finite := hf.meromorphicOn.divisor_ball_support_finite
  have hmul : Function.mulSupport fac ⊆ D.support := by
    intro w hw
    contrapose! hw
    have hDw : D w = 0 := by
      simpa [Function.mem_support] using hw
    simp [fac, hDw]
  have hfOpen := hf.mono ball_subset_closedBall
  have hD0 : D 0 = 0 := by
    rw [hfOpen.divisor_apply (by simp [hA]),
      (hf 0 (by simp [hA.le])).analyticOrderAt_eq_zero.mpr hf0]
    simp
  rw [canonicalZeroProduct,
    finprod_eq_prod_of_mulSupport_subset_of_finite _ hmul hD]
  simp only [Finset.prod_apply, norm_prod]
  apply Finset.prod_le_one
  · intro w hw
    exact norm_nonneg _
  · intro w hw
    have hwSupp := hD.mem_toFinset.mp hw
    have hwBall := D.supportWithinDomain hwSupp
    have hw0 : w ≠ 0 := by
      intro h
      subst w
      exact hwSupp (by simp [ hD0])
    have hbase : 1 ≤ ‖Complex.canonicalFactor A w 0‖ := by
      have hwNormPos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hwNorm : ‖w‖ < A := mem_ball_zero_iff.mp hwBall
      rw [Complex.canonicalFactor_apply, norm_div, norm_mul]
      simp only [mul_zero, sub_zero, zero_sub, norm_neg, norm_pow, norm_real,
        Real.norm_eq_abs, abs_of_pos hA]
      apply (le_div_iff₀ (mul_pos hA hwNormPos)).2
      nlinarith
    have hDnonneg : 0 ≤ D w := hfOpen.divisor_nonneg w
    change ‖Complex.canonicalFactor A w 0 ^ (-D w)‖ ≤ 1
    rw [norm_zpow]
    exact zpow_le_one_of_nonpos₀ hbase (neg_nonpos.mpr hDnonneg)

/-- A canonical residual inherits the boundary norm bound from the original
function by the maximum modulus principle. -/
theorem norm_canonicalResidual_le
    {f g : Complex -> Complex} {A M : Real} (hA : 0 < A)
    (hf : AnalyticOnNhd Complex f (closedBall 0 A))
    (hg : AnalyticOnNhd Complex g (closedBall 0 A))
    (hlocal : ∀ z ∈ closedBall (0 : Complex) A,
      f =ᶠ[nhds z] canonicalZeroProduct f A * g)
    (hM : ∀ z ∈ closedBall (0 : Complex) A, ‖f z‖ ≤ M) :
    ∀ z ∈ closedBall (0 : Complex) A, ‖g z‖ ≤ M := by
  have hgDiff : DiffContOnCl Complex g (ball (0 : Complex) A) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hA.ne']
    exact hg.differentiableOn
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    Metric.isBounded_ball hgDiff (z := z)
  · intro u hu
    rw [frontier_ball 0 hA.ne'] at hu
    have heq := (hlocal u (sphere_subset_closedBall hu)).eq_of_nhds
    have hnorm := congrArg norm heq
    simp only [Pi.mul_apply, norm_mul,
      norm_canonicalZeroProduct_eq_one_of_mem_sphere hf hu, one_mul] at hnorm
    rw [← hnorm]
    exact hM u (sphere_subset_closedBall hu)
  · rw [closure_ball 0 hA.ne']
    exact hz

/-- A fixed-radius Borel--Caratheodory and Cauchy estimate for a zero-free
analytic function. -/
theorem norm_logDeriv_canonicalResidual_le
    {g : Complex -> Complex} {M m : Real}
    (hg : AnalyticOnNhd Complex g (closedBall 0 (7 / 8 : Real)))
    (hg0 : ∀ u ∈ ball (0 : Complex) (7 / 8 : Real), g u ≠ 0)
    (hM : ∀ u ∈ closedBall (0 : Complex) (7 / 8 : Real), ‖g u‖ ≤ M)
    (hm : 0 < m) (hmg0 : m ≤ ‖g 0‖) (hratio : 1 < M / m)
    {z : Complex} (hz : ‖z‖ ≤ (2 / 3 : Real)) :
    ‖logDeriv g z‖ ≤ 144 * Real.log (M / m) := by
  let L : Real := Real.log (M / m)
  have hLpos : 0 < L := Real.log_pos hratio
  have hMpos : 0 < M := by
    have := (lt_div_iff₀ hm).1 hratio
    nlinarith
  have hgOpen : AnalyticOnNhd Complex g (ball 0 (7 / 8 : Real)) :=
    hg.mono ball_subset_closedBall
  have hqAn : AnalyticOnNhd Complex (logDeriv g)
      (ball 0 (7 / 8 : Real)) := by
    show AnalyticOnNhd Complex (deriv g / g) (ball 0 (7 / 8 : Real))
    exact hgOpen.deriv.div hgOpen hg0
  obtain ⟨h, hh0, hh⟩ :=
    hqAn.differentiableOn.isExactOn_ball.with_val_at
      (0 : Complex) (0 : Complex)
  have hhDiff : DifferentiableOn Complex h (ball 0 (7 / 8 : Real)) :=
    fun u hu => (hh u hu).differentiableAt.differentiableWithinAt
  let F : Complex -> Complex := (fun u => Complex.exp (-h u)) * g
  have hFDiff : DifferentiableOn Complex F (ball 0 (7 / 8 : Real)) := by
    intro u hu
    exact (((hh u hu).neg.cexp).mul
      (hgOpen u hu).differentiableAt.hasDerivAt).differentiableAt
        |>.differentiableWithinAt
  have hFDeriv : EqOn (deriv F) 0 (ball 0 (7 / 8 : Real)) := by
    intro u hu
    have hder := ((hh u hu).neg.cexp).mul
      (hgOpen u hu).differentiableAt.hasDerivAt
    simp only [Pi.neg_apply] at hder
    change deriv ((fun v => Complex.exp (-h v)) * g) u = (0 : Complex)
    rw [hder.deriv, logDeriv_apply]
    field_simp [hg0 u hu]
    ring
  have hFConst : ∀ u ∈ ball (0 : Complex) (7 / 8 : Real), F u = F 0 := by
    intro u hu
    exact isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball (0 : Complex) (7 / 8)).isPreconnected hFDiff hFDeriv
      hu (by norm_num)
  have hExp : ∀ u ∈ ball (0 : Complex) (7 / 8 : Real),
      Complex.exp (h u) * g 0 = g u := by
    intro u hu
    have hconst := hFConst u hu
    dsimp [F] at hconst ⊢
    rw [hh0, neg_zero, Complex.exp_zero, one_mul] at hconst
    rw [← hconst, ← mul_assoc, ← Complex.exp_add]
    simp
  have hG0 : g 0 ≠ 0 := hg0 0 (by norm_num)
  have hRe : MapsTo h (ball (0 : Complex) (7 / 8 : Real))
      {u | u.re ≤ L} := by
    intro u hu
    have hnorm := congrArg norm (hExp u hu)
    simp only [norm_mul, norm_exp] at hnorm
    have hratioEq : Real.exp (h u).re = ‖g u‖ / ‖g 0‖ := by
      apply (eq_div_iff (norm_ne_zero_iff.mpr hG0)).2
      exact hnorm
    have hratioLe : ‖g u‖ / ‖g 0‖ ≤ M / m :=
      div_le_div₀ hMpos.le (hM u (ball_subset_closedBall hu)) hm hmg0
    have hratioPos : 0 < ‖g u‖ / ‖g 0‖ :=
      div_pos (norm_pos_iff.mpr (hg0 u hu)) (norm_pos_iff.mpr hG0)
    change (h u).re ≤ L
    rw [show (h u).re = Real.log (‖g u‖ / ‖g 0‖) by
      rw [← hratioEq, Real.log_exp]]
    exact Real.log_le_log hratioPos hratioLe
  have hBorel {u : Complex} (hu : ‖u‖ ≤ (3 / 4 : Real)) :
      ‖h u‖ ≤ 12 * L := by
    have huBall : u ∈ ball (0 : Complex) (7 / 8 : Real) := by
      simpa [mem_ball_zero_iff] using
        hu.trans_lt (by norm_num : (3 / 4 : Real) < 7 / 8)
    have hb := Complex.borelCaratheodory_zero hLpos hhDiff hRe
      (by norm_num : (0 : Real) < 7 / 8) huBall hh0
    have hden : 0 < (7 / 8 : Real) - ‖u‖ := by
      have := hu.trans_lt (by norm_num : (3 / 4 : Real) < 7 / 8)
      linarith
    calc
      ‖h u‖ ≤ 2 * L * ‖u‖ / ((7 / 8 : Real) - ‖u‖) := hb
      _ ≤ 12 * L := by
        apply (div_le_iff₀ hden).2
        have hp := mul_nonneg hLpos.le (sub_nonneg.mpr hu)
        nlinarith
  have hzBall : z ∈ ball (0 : Complex) (7 / 8 : Real) := by
    simpa [mem_ball_zero_iff] using
      hz.trans_lt (by norm_num : (2 / 3 : Real) < 7 / 8)
  have hClosed : DifferentiableOn Complex h
      (closedBall z (1 / 12 : Real)) := by
    intro u hu
    have hdist : ‖u - z‖ ≤ (1 / 12 : Real) := by
      simpa [mem_closedBall, dist_eq_norm] using hu
    have huNorm : ‖u‖ ≤ (3 / 4 : Real) := by
      calc
        ‖u‖ = ‖(u - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖u - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ 1 / 12 + 2 / 3 := add_le_add hdist hz
        _ = 3 / 4 := by norm_num
    exact (hh u (by
      simpa [mem_ball_zero_iff] using
        huNorm.trans_lt (by norm_num : (3 / 4 : Real) < 7 / 8)))
          |>.differentiableAt.differentiableWithinAt
  have hDiffCl : DiffContOnCl Complex h (ball z (1 / 12 : Real)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z (by norm_num : (1 / 12 : Real) ≠ 0)]
    exact hClosed
  have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := h) (c := z) (R := (1 / 12 : Real)) (C := 12 * L)
    (by norm_num) hDiffCl (fun u hu => by
      apply hBorel
      have hdist : ‖u - z‖ = (1 / 12 : Real) := by
        simpa [mem_sphere, dist_eq_norm] using hu
      calc
        ‖u‖ = ‖(u - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖u - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ 1 / 12 + 2 / 3 := by rw [hdist]; gcongr
        _ = 3 / 4 := by norm_num)
  rw [← (hh z hzBall).deriv]
  calc
    ‖deriv h z‖ ≤ 12 * L / (1 / 12) := hCauchy
    _ = 144 * Real.log (M / m) := by dsimp [L]; ring

/-- Jensen's inequality with an explicit denominator estimate at radius
`7 / 8`. -/
theorem sum_divisor_seven_eighths_le
    {f : Complex -> Complex} {M m : Real}
    (hf : AnalyticOnNhd Complex f (closedBall 0 1))
    (hM : 1 ≤ M) (hm : 0 < m) (hf0 : f 0 ≠ 0) (hmf : m ≤ ‖f 0‖)
    (hbound : ∀ z ∈ closedBall (0 : Complex) 1, ‖f z‖ ≤ M) :
    ∑ᶠ u, (MeromorphicOn.divisor f
      (closedBall (0 : Complex) (7 / 8 : Real)) u : Real) ≤
      8 * Real.log (M / m) := by
  have hf' : AnalyticOnNhd Complex f (closedBall 0 |(1 : Real)|) := by
    simpa using hf
  have hJ := hf'.sum_divisor_le
    (r := (7 / 8 : Real)) (R := (1 : Real)) (M := M)
    (by norm_num) (by norm_num) hM hf0
    (fun z hz => hbound z (by simpa using sphere_subset_closedBall hz))
  have habs : |(7 / 8 : Real)| = 7 / 8 := abs_of_pos (by norm_num)
  rw [habs] at hJ
  have hden : (1 : Real) / (7 / 8) = 8 / 7 := by norm_num
  rw [hden] at hJ
  have hmap := map_finsum (Int.castRingHom Real)
    ((MeromorphicOn.divisor f
      (closedBall (0 : Complex) (7 / 8 : Real))).finiteSupport
        (isCompact_closedBall 0 (7 / 8 : Real)))
  norm_num at hmap
  rw [hmap] at hJ
  have hnorm0 : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hratio : M / ‖f 0‖ ≤ M / m :=
    div_le_div_of_nonneg_left hMpos.le hm hmf
  have hlogNumerator :
      Real.log (M / ‖f 0‖) ≤ Real.log (M / m) :=
    Real.log_le_log (div_pos hMpos hnorm0) hratio
  have hlogDenom : (1 / 8 : Real) ≤ Real.log (8 / 7) := by
    have h := Real.one_sub_inv_le_log_of_pos
      (x := (8 / 7 : Real)) (by norm_num)
    norm_num at h ⊢
    exact h
  have hlogDenomPos : 0 < Real.log (8 / 7) :=
    Real.log_pos (by norm_num)
  have hMgeM : m ≤ M := hmf.trans (hbound 0 (by norm_num))
  have hlogRatioNonneg : 0 ≤ Real.log (M / m) :=
    Real.log_nonneg ((one_le_div hm).2 hMgeM)
  calc
    ∑ᶠ u, (MeromorphicOn.divisor f
        (closedBall (0 : Complex) (7 / 8 : Real)) u : Real) ≤
        Real.log (M / ‖f 0‖) / Real.log (8 / 7) := hJ
    _ ≤ Real.log (M / m) / Real.log (8 / 7) :=
      div_le_div_of_nonneg_right hlogNumerator hlogDenomPos.le
    _ ≤ 8 * Real.log (M / m) := by
      apply (div_le_iff₀ hlogDenomPos).2
      nlinarith

/-- The open extraction-disk divisor count is at most its closed-disk
counterpart. -/
theorem sum_open_divisor_le_closed
    {f : Complex -> Complex} {A : Real}
    (hf : AnalyticOnNhd Complex f (closedBall 0 A)) :
    ∑ᶠ u, (MeromorphicOn.divisor f (ball (0 : Complex) A) u : Real) ≤
      ∑ᶠ u, (MeromorphicOn.divisor f
        (closedBall (0 : Complex) A) u : Real) := by
  have hOpen := hf.meromorphicOn.divisor_ball_support_finite
  have hClosed :=
    (MeromorphicOn.divisor f (closedBall (0 : Complex) A)).finiteSupport
      (isCompact_closedBall 0 A)
  apply finsum_le_finsum'
  · exact hOpen.subset fun u hu => Int.cast_ne_zero.mp hu
  · exact hClosed.subset fun u hu => Int.cast_ne_zero.mp hu
  intro u
  change ((MeromorphicOn.divisor f (ball (0 : Complex) A) u : Int) : Real) ≤
    ((MeromorphicOn.divisor f (closedBall (0 : Complex) A) u : Int) : Real)
  by_cases hu : u ∈ ball (0 : Complex) A
  · have hu' : u ∈ closedBall (0 : Complex) A := ball_subset_closedBall hu
    rw [hf.mono ball_subset_closedBall |>.divisor_apply hu,
      hf.divisor_apply hu']
  · rw [(MeromorphicOn.divisor f
      (ball (0 : Complex) A)).apply_eq_zero_of_notMem hu]
    exact_mod_cast hf.divisor_nonneg u

/-- The reflected pole of a canonical factor is uniformly separated from the
evaluation disk. -/
theorem norm_reflectedCanonicalTerm_le
    {w z : Complex} (hw : w ∈ ball (0 : Complex) (7 / 8 : Real))
    (hz : ‖z‖ ≤ (2 / 3 : Real)) :
    ‖(starRingEnd Complex) w /
      (((7 / 8 : Real) : Complex) ^ 2 - (starRingEnd Complex) w * z)‖ ≤
      (24 / 5 : Real) := by
  have hw' : ‖w‖ ≤ (7 / 8 : Real) := (mem_ball_zero_iff.mp hw).le
  have hprod : ‖(starRingEnd Complex) w * z‖ ≤
      (7 / 8 : Real) * (2 / 3 : Real) := by
    rw [norm_mul]
    simpa using mul_le_mul hw' hz (norm_nonneg z)
      (by positivity : (0 : Real) ≤ 7 / 8)
  have hconst : ‖(((7 / 8 : Real) : Complex) ^ 2)‖ =
      (7 / 8 : Real) ^ 2 := by norm_num
  have hden : (35 / 192 : Real) ≤
      ‖(((7 / 8 : Real) : Complex) ^ 2 -
        (starRingEnd Complex) w * z)‖ := by
    calc
      (35 / 192 : Real) =
          (7 / 8 : Real) ^ 2 - (7 / 8 : Real) * (2 / 3 : Real) := by
        norm_num
      _ ≤ ‖(((7 / 8 : Real) : Complex) ^ 2)‖ -
          ‖(starRingEnd Complex) w * z‖ := by
        rw [hconst]
        linarith
      _ ≤ ‖(((7 / 8 : Real) : Complex) ^ 2 -
          (starRingEnd Complex) w * z)‖ := norm_sub_norm_le _ _
  rw [norm_div]
  calc
    ‖(starRingEnd Complex) w‖ /
        ‖(((7 / 8 : Real) : Complex) ^ 2 -
          (starRingEnd Complex) w * z)‖ ≤
        (7 / 8 : Real) / (35 / 192 : Real) :=
      div_le_div₀ (by norm_num) (by simpa using hw') (by norm_num) hden
    _ = 24 / 5 := by norm_num

/-- A zero in the extraction annulus is at least `1 / 6` from the evaluation
disk. -/
theorem norm_one_div_sub_le_of_mem_extractionAnnulus
    {w z : Complex}
    (_hw : w ∈ ball (0 : Complex) (7 / 8 : Real))
    (hwout : w ∉ closedBall (0 : Complex) (5 / 6 : Real))
    (hz : ‖z‖ ≤ (2 / 3 : Real)) :
    ‖(1 : Complex) / (z - w)‖ ≤ (6 : Real) := by
  have hwLower : (5 / 6 : Real) < ‖w‖ := by
    simpa [mem_closedBall, dist_zero_right, not_le] using hwout
  have hden : (1 / 6 : Real) ≤ ‖z - w‖ := by
    have hrev := norm_sub_norm_le w z
    rw [norm_sub_rev] at hrev
    linarith
  have hdenPos : 0 < ‖z - w‖ := by positivity
  rw [norm_div, norm_one]
  apply (div_le_iff₀ hdenPos).2
  nlinarith

end PrimesRestrictedDigits
