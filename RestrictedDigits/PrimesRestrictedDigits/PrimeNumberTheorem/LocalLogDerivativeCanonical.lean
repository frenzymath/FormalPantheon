import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Canonical products for local logarithmic derivatives

This file supplies the finite canonical-product decomposition used in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Lemma 6.3.  The extraction radius is
open in the divisor, while the residual and the local equality extend to the
closed disk.  This distinction is needed later to retain zeros on the boundary
of a smaller target disk.
-/

open Filter Function Metric Set
open scoped Topology

namespace PrimesRestrictedDigits

/-- The reciprocal canonical product whose zeros cancel the divisor of `f`
inside the open disk of radius `A`. -/
noncomputable def canonicalZeroProduct (f : Complex -> Complex) (A : Real) :
    Complex -> Complex :=
  ∏ᶠ w, (Complex.canonicalFactor A w) ^
    (-MeromorphicOn.divisor f (ball 0 A) w)

/-- An analytic function that is not identically zero has finite meromorphic
order at every point of a connected closed disk containing a nonzero value. -/
private lemma meromorphicOrderAt_ne_top_on_closedBall
    {f : Complex -> Complex} {A : Real} (hA : 0 < A)
    (hf : AnalyticOnNhd Complex f (closedBall 0 A)) (hf0 : f 0 ≠ 0) :
    ∀ u : (closedBall (0 : Complex) A), meromorphicOrderAt f u ≠ ⊤ := by
  intro u
  have h0 : analyticOrderAt f 0 ≠ ⊤ := by
    rw [(hf 0 (by simp [hA.le])).analyticOrderAt_eq_zero.mpr hf0]
    exact ENat.zero_ne_top
  have hu := hf.analyticOrderAt_ne_top_of_isPreconnected
    Metric.isPreconnected_closedBall (by simp [hA.le]) u.property h0
  rw [(hf u u.property).meromorphicOrderAt_eq]
  simpa using hu

/-- The factors defining `canonicalZeroProduct` have finite multiplicative
support. -/
private lemma canonicalFactorFamily_hasFiniteMulSupport
    {f : Complex -> Complex} {A : Real}
    (hf : MeromorphicOn f (closedBall 0 A)) :
    Function.HasFiniteMulSupport fun w =>
      (Complex.canonicalFactor A w) ^
        (-MeromorphicOn.divisor f (ball 0 A) w) := by
  let D := MeromorphicOn.divisor f (ball 0 A)
  rw [Function.HasFiniteMulSupport]
  apply hf.divisor_ball_support_finite.subset
  intro w hw
  contrapose! hw
  have hDw : D w = 0 := by
    simpa [Function.mem_support] using hw
  simp [D, hDw]

/-- The canonical zero product is meromorphic in normal form throughout the
closed extraction disk. -/
private lemma meromorphicNFOn_canonicalZeroProduct
    {f : Complex -> Complex} {A : Real} :
    MeromorphicNFOn (canonicalZeroProduct f A) (closedBall 0 A) := by
  let D := MeromorphicOn.divisor f (ball 0 A)
  dsimp only [canonicalZeroProduct]
  apply meromorphicNFOn_finprod
  · intro w
    by_cases hw : w ∈ ball (0 : Complex) A
    · intro z hz
      exact (Complex.meromorphicNFOn_canonicalFactor hw (mem_univ z)).zpow
    · intro z hz
      simp only [ hw, not_false_eq_true,
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem, neg_zero, zpow_zero]
      rw [meromorphicNFAt_iff_analyticAt_or]
      exact Or.inl analyticAt_const
  · intro z hz a ha b hb
    change Complex.canonicalFactor A a z ^ (-D a) = 0 at ha
    change Complex.canonicalFactor A b z ^ (-D b) = 0 at hb
    have haA : a ∈ ball (0 : Complex) A := by
      by_contra h
      simp [D, h] at ha
    have hbA : b ∈ ball (0 : Complex) A := by
      by_contra h
      simp [D, h] at hb
    have hza : z = a := by
      apply not_ne_iff.mp
      intro hza
      exact (Complex.canonicalFactor_ne_zero haA hz hza)
        (eq_zero_of_zpow_eq_zero ha)
    have hzb : z = b := by
      apply not_ne_iff.mp
      intro hzb
      exact (Complex.canonicalFactor_ne_zero hbA hz hzb)
        (eq_zero_of_zpow_eq_zero hb)
    exact hza.symm.trans hzb

/-- Away from the open extraction disk, the canonical zero product is
analytic and nonzero on the boundary of the closed disk. -/
private lemma canonicalZeroProduct_analyticAt_ne_zero_of_not_mem_ball
    {f : Complex -> Complex} {A : Real}
    (hf : MeromorphicOn f (closedBall 0 A)) {z : Complex}
    (hz : z ∈ closedBall 0 A) (hz' : z ∉ ball 0 A) :
    AnalyticAt Complex (canonicalZeroProduct f A) z ∧
      canonicalZeroProduct f A z ≠ 0 := by
  let D := MeromorphicOn.divisor f (ball 0 A)
  let fac : Complex -> Complex -> Complex := fun w =>
    (Complex.canonicalFactor A w) ^ (-D w)
  have hfac : Function.HasFiniteMulSupport fac := by
    simpa [fac, D] using canonicalFactorFamily_hasFiniteMulSupport hf
  constructor
  · dsimp only [canonicalZeroProduct]
    apply analyticAt_finprod
    intro w
    by_cases hw : w ∈ ball (0 : Complex) A
    · have hzw : z ≠ w := fun h => hz' (h ▸ hw)
      exact (Complex.analyticOnNhd_canonicalFactor A w z hzw).zpow
        (Complex.canonicalFactor_ne_zero hw hz hzw)
    · simp only [hw, not_false_eq_true,
        Function.locallyFinsuppWithin.apply_eq_zero_of_notMem, neg_zero, zpow_zero]
      exact analyticAt_const
  · change (∏ᶠ w, fac w) z ≠ 0
    rw [finprod_apply hfac z]
    apply finprod_ne_zero
    intro w
    dsimp only [fac]
    by_cases hw : w ∈ ball (0 : Complex) A
    · have hzw : z ≠ w := fun h => hz' (h ▸ hw)
      exact zpow_ne_zero _ (Complex.canonicalFactor_ne_zero hw hz hzw)
    · simp [D, hw]

/-- Canonical decomposition with a residual that is analytic on the closed
disk, nonzero in its interior, and locally equal to the original function
after multiplication by the canonical zero product. -/
theorem exists_canonicalResidual {f : Complex -> Complex} {A : Real}
    (hA : 0 < A)
    (hf : AnalyticOnNhd Complex f (closedBall 0 A))
    (hf0 : f 0 ≠ 0) :
    ∃ g : Complex -> Complex,
      AnalyticOnNhd Complex g (closedBall 0 A) ∧
      (∀ z ∈ ball 0 A, g z ≠ 0) ∧
      (∀ z ∈ closedBall 0 A,
        f =ᶠ[nhds z] canonicalZeroProduct f A * g) := by
  obtain ⟨g, hdec⟩ := hf.meromorphicOn.exists_canonicalDecomp
    (meromorphicOrderAt_ne_top_on_closedBall hA hf hf0)
  have hgAnalytic : AnalyticOnNhd Complex g (ball 0 A) := by
    intro z hz
    have hzNF := hdec.meromorphicNFOn (ball_subset_closedBall hz)
    rw [meromorphicNFAt_iff_analyticAt_or] at hzNF
    exact hzNF.resolve_right fun h => hdec.ne_zero z hz h.2.2
  have hRhsNF :
      MeromorphicNFOn (canonicalZeroProduct f A * g) (closedBall 0 A) := by
    intro z hz
    by_cases hz' : z ∈ ball (0 : Complex) A
    · exact (meromorphicNFAt_mul_iff_left (hgAnalytic z hz')
        (hdec.ne_zero z hz')).2 (meromorphicNFOn_canonicalZeroProduct hz)
    · obtain ⟨hPAnalytic, hPne⟩ :=
        canonicalZeroProduct_analyticAt_ne_zero_of_not_mem_ball
          hf.meromorphicOn hz hz'
      exact (meromorphicNFAt_mul_iff_right hPAnalytic hPne).2
        (hdec.meromorphicNFOn hz)
  have hcod : f =ᶠ[codiscreteWithin (closedBall 0 A)]
      canonicalZeroProduct f A * g := by
    simpa [canonicalZeroProduct, Pi.smul_apply, smul_eq_mul] using hdec.eventuallyEq
  have hpre : Preperfect (closedBall (0 : Complex) A) := by
    have hn : (closedBall (0 : Complex) A).Nontrivial := by
      refine ⟨0, by simp [hA.le], (A : Complex), by simp [abs_of_pos hA], ?_⟩
      exact_mod_cast hA.ne'.symm
    exact IsPreconnected.preperfect_of_nontrivial hn Metric.isPreconnected_closedBall
  have hlocal : ∀ z ∈ closedBall (0 : Complex) A,
      f =ᶠ[nhds z] canonicalZeroProduct f A * g := by
    intro z hz
    have hpunc := (hf z hz).meromorphicAt
      |>.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
        (hRhsNF hz).meromorphicAt hz hpre hcod
    exact ((hf z hz).meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
      (hRhsNF hz)).mp hpunc
  have hgAnalyticClosed : AnalyticOnNhd Complex g (closedBall 0 A) := by
    intro z hz
    by_cases hz' : z ∈ ball (0 : Complex) A
    · exact hgAnalytic z hz'
    · obtain ⟨hPAnalytic, hPne⟩ :=
        canonicalZeroProduct_analyticAt_ne_zero_of_not_mem_ball
          hf.meromorphicOn hz hz'
      apply (analyticAt_iff_analytic_mul hPAnalytic hPne).2
      exact (hf z hz).congr (hlocal z hz)
  exact ⟨g, hgAnalyticClosed, hdec.ne_zero, hlocal⟩

/-- The logarithmic derivative of one canonical factor, written as the sum
of its reflected-zero and pole contributions. -/
private lemma logDeriv_canonicalFactor
    {A : Real} {w z : Complex} (hA : 0 < A)
    (hw : w ∈ ball 0 A) (hz : z ∈ closedBall 0 A) (hzw : z ≠ w) :
    logDeriv (Complex.canonicalFactor A w) z =
      -(starRingEnd Complex) w /
          ((A : Complex) ^ 2 - (starRingEnd Complex) w * z) -
        1 / (z - w) := by
  let n : Complex -> Complex := fun x =>
    (A : Complex) ^ 2 - (starRingEnd Complex) w * x
  let d : Complex -> Complex := fun x => (A : Complex) * (x - w)
  have hAc : (A : Complex) ≠ 0 := by
    exact_mod_cast hA.ne'
  have hcf := Complex.canonicalFactor_ne_zero hw hz hzw
  have hn : n z ≠ 0 := by
    intro h
    apply hcf
    simp [Complex.canonicalFactor_apply, n, h]
  have hd : d z ≠ 0 := by
    dsimp only [d]
    exact mul_ne_zero hAc (sub_ne_zero.mpr hzw)
  have hnDiff : DifferentiableAt Complex n z := by
    dsimp only [n]
    fun_prop
  have hdDiff : DifferentiableAt Complex d z := by
    dsimp only [d]
    fun_prop
  have hnDeriv : deriv n z = -(starRingEnd Complex) w := by
    dsimp only [n]
    rw [deriv_fun_sub (by fun_prop) (by fun_prop), deriv_const,
      deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const, deriv_id'']
    simp
  have hdDeriv : deriv d z = (A : Complex) := by
    dsimp only [d]
    rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_const,
      deriv_fun_sub (by fun_prop) (by fun_prop), deriv_id'', deriv_const]
    simp
  rw [Complex.canonicalFactor_def]
  change logDeriv (fun x => n x / d x) z = _
  rw [logDeriv_div z hn hd hnDiff hdDiff]
  simp only [logDeriv_apply, hnDeriv, hdDeriv, n, d]
  field_simp

/-- The exact logarithmic-derivative identity associated to a canonical
residual.  Divisor coefficients retain the multiplicities of the zeros. -/
theorem logDeriv_eq_canonicalResidual_add_finsum
    {f g : Complex -> Complex} {A : Real} (hA : 0 < A)
    (hf : AnalyticOnNhd Complex f (closedBall 0 A))
    (hg : AnalyticOnNhd Complex g (closedBall 0 A))
    (hg0 : ∀ z ∈ ball 0 A, g z ≠ 0)
    (hlocal : ∀ z ∈ closedBall 0 A,
      f =ᶠ[nhds z] canonicalZeroProduct f A * g)
    {z : Complex} (hz : z ∈ ball 0 A) (hfz : f z ≠ 0) :
    logDeriv f z = logDeriv g z +
      ∑ᶠ w, (MeromorphicOn.divisor f (ball 0 A) w : Complex) *
        (1 / (z - w) + (starRingEnd Complex) w /
          ((A : Complex) ^ 2 - (starRingEnd Complex) w * z)) := by
  let D := MeromorphicOn.divisor f (ball 0 A)
  let fac : Complex -> Complex -> Complex := fun w =>
    (Complex.canonicalFactor A w) ^ (-D w)
  let P : Complex -> Complex := ∏ᶠ w, fac w
  have hD : D.support.Finite := hf.meromorphicOn.divisor_ball_support_finite
  have hmul : Function.mulSupport fac ⊆ D.support := by
    intro w hw
    contrapose! hw
    have hDw : D w = 0 := by
      simpa [Function.mem_support] using hw
    simp [fac, hDw]
  have hPeq : P = ∏ w ∈ hD.toFinset, fac w :=
    finprod_eq_prod_of_mulSupport_subset_of_finite fac hmul hD
  have hprodEq : (∏ w ∈ hD.toFinset, fac w) =
      (fun x => ∏ w ∈ hD.toFinset, fac w x) := by
    funext x
    simp
  have hEqNhd : f =ᶠ[nhds z] P * g := by
    simpa [P, fac, D, canonicalZeroProduct] using
      hlocal z (ball_subset_closedBall hz)
  have hEq : f z = (P * g) z := hEqNhd.eq_of_nhds
  have hgz : g z ≠ 0 := hg0 z hz
  have hPz : P z ≠ 0 := by
    intro h
    apply hfz
    rw [hEq]
    simp [h]
  have hprodNe : (∏ w ∈ hD.toFinset, fac w) z ≠ 0 := by
    rw [← hPeq]
    exact hPz
  simp only [Finset.prod_apply] at hprodNe
  have hfacNe : ∀ w ∈ hD.toFinset, fac w z ≠ 0 := by
    simpa only [Finset.prod_ne_zero_iff] using hprodNe
  have hwBall {w : Complex} (hw : w ∈ hD.toFinset) :
      w ∈ ball (0 : Complex) A :=
    D.supportWithinDomain (hD.mem_toFinset.mp hw)
  have hzw {w : Complex} (hw : w ∈ hD.toFinset) : z ≠ w := by
    intro h
    have hDw : D w ≠ 0 := by
      simpa [Function.mem_support] using hD.mem_toFinset.mp hw
    apply hfacNe w hw
    rw [h]
    change Complex.canonicalFactor A w w ^ (-D w) = 0
    rw [Complex.canonicalFactor_apply_self]
    exact zero_zpow _ (neg_ne_zero.mpr hDw)
  have hfacDiff : ∀ w ∈ hD.toFinset, DifferentiableAt Complex (fac w) z := by
    intro w hw
    exact ((Complex.analyticOnNhd_canonicalFactor A w z (hzw hw)).zpow
      (Complex.canonicalFactor_ne_zero (hwBall hw)
        (ball_subset_closedBall hz) (hzw hw))).differentiableAt
  have hPdiff : DifferentiableAt Complex P z := by
    rw [hPeq, hprodEq]
    exact .fun_finsetProd hfacDiff
  have hlogP : logDeriv P z =
      ∑ w ∈ hD.toFinset, logDeriv (fac w) z := by
    rw [hPeq, hprodEq]
    exact logDeriv_prod hfacNe hfacDiff
  have hlogFac {w : Complex} (hw : w ∈ hD.toFinset) :
      logDeriv (fac w) z = (D w : Complex) *
        (1 / (z - w) + (starRingEnd Complex) w /
          ((A : Complex) ^ 2 - (starRingEnd Complex) w * z)) := by
    change logDeriv
      (fun x => Complex.canonicalFactor A w x ^ (-D w)) z = _
    rw [logDeriv_fun_zpow
      (Complex.analyticOnNhd_canonicalFactor A w z (hzw hw)).differentiableAt]
    rw [logDeriv_canonicalFactor hA (hwBall hw)
      (ball_subset_closedBall hz) (hzw hw)]
    push_cast
    ring
  have hsum : logDeriv P z = ∑ w ∈ hD.toFinset, (D w : Complex) *
      (1 / (z - w) + (starRingEnd Complex) w /
        ((A : Complex) ^ 2 - (starRingEnd Complex) w * z)) := by
    rw [hlogP]
    exact Finset.sum_congr rfl fun w hw => hlogFac hw
  have hgOpen : AnalyticOnNhd Complex g (ball 0 A) :=
    hg.mono ball_subset_closedBall
  calc
    logDeriv f z = logDeriv (P * g) z := by
      simp only [logDeriv_apply, hEqNhd.deriv_eq, hEq]
    _ = logDeriv P z + logDeriv g z :=
      logDeriv_mul z hPz hgz hPdiff (hgOpen z hz).differentiableAt
    _ = logDeriv g z + ∑ w ∈ hD.toFinset, (D w : Complex) *
        (1 / (z - w) + (starRingEnd Complex) w /
          ((A : Complex) ^ 2 - (starRingEnd Complex) w * z)) := by
      rw [hsum, add_comm]
    _ = logDeriv g z + ∑ᶠ w, (D w : Complex) *
        (1 / (z - w) + (starRingEnd Complex) w /
          ((A : Complex) ^ 2 - (starRingEnd Complex) w * z)) := by
      congr 1
      symm
      apply finsum_eq_sum_of_support_subset
      intro w hw
      contrapose! hw
      have hDw : D w = 0 := by
        simpa [Function.mem_support] using hw
      simp [hDw]

end PrimesRestrictedDigits
