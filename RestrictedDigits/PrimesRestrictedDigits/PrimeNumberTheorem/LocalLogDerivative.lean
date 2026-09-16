import PrimesRestrictedDigits.PrimeNumberTheorem.LocalLogDerivativeBounds

/-!
# A fixed-radius local logarithmic-derivative expansion

This file assembles the Jensen, canonical-product, Borel--Caratheodory, and
Cauchy estimates into the fixed-radius form of
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Lemma 6.3 used for zeta.
-/

open Complex Metric Set
open MeromorphicOn

namespace PrimesRestrictedDigits

/-- Lemma 6.3 at extraction radius `7 / 8`, target radius `5 / 6`, and
evaluation radius `2 / 3`. The target sum uses the closed-disk divisor, so
zeros on its boundary retain their multiplicities. -/
theorem norm_logDeriv_sub_localZeroSum_le
    {f : Complex -> Complex} {M m : Real}
    (hf : AnalyticOnNhd Complex f (closedBall 0 1))
    (hM : 1 ≤ M) (hm : 0 < m) (hf0 : f 0 ≠ 0) (hmf : m ≤ ‖f 0‖)
    (hbound : ∀ u ∈ closedBall (0 : Complex) 1, ‖f u‖ ≤ M)
    (hratio : 1 < M / m)
    {z : Complex} (hz : ‖z‖ ≤ (2 / 3 : Real)) (hfz : f z ≠ 0) :
    ‖logDeriv f z -
      ∑ᶠ w, (MeromorphicOn.divisor f
        (closedBall (0 : Complex) (5 / 6 : Real)) w : Complex) /
          (z - w)‖ ≤
      232 * Real.log (M / m) := by
  let A : Real := 7 / 8
  let D := MeromorphicOn.divisor f (ball (0 : Complex) A)
  let E := MeromorphicOn.divisor f
    (closedBall (0 : Complex) (5 / 6 : Real))
  let L : Real := Real.log (M / m)
  have hA : 0 < A := by norm_num [A]
  have hfA : AnalyticOnNhd Complex f (closedBall 0 A) := by
    apply hf.mono
    exact closedBall_subset_closedBall (by norm_num [A])
  obtain ⟨g, hg, hg0, hlocal⟩ :=
    exists_canonicalResidual hA hfA hf0
  have hgBound : ∀ u ∈ closedBall (0 : Complex) A, ‖g u‖ ≤ M :=
    norm_canonicalResidual_le hA hfA hg hlocal fun u hu =>
      hbound u (closedBall_subset_closedBall (by norm_num [A]) hu)
  have hgCenter : m ≤ ‖g 0‖ := by
    have heq := (hlocal 0 (by simp [hA.le])).eq_of_nhds
    have hnorm := congrArg norm heq
    simp only [Pi.mul_apply, norm_mul] at hnorm
    calc
      m ≤ ‖f 0‖ := hmf
      _ = ‖canonicalZeroProduct f A 0‖ * ‖g 0‖ := hnorm
      _ ≤ 1 * ‖g 0‖ := mul_le_mul_of_nonneg_right
        (norm_canonicalZeroProduct_zero_le_one hA hfA hf0) (norm_nonneg _)
      _ = ‖g 0‖ := one_mul _
  have hzA : z ∈ ball (0 : Complex) A := by
    simpa [A, mem_ball_zero_iff] using
      hz.trans_lt (by norm_num : (2 / 3 : Real) < 7 / 8)
  have hgLog : ‖logDeriv g z‖ ≤ 144 * L := by
    apply norm_logDeriv_canonicalResidual_le
      (M := M) (m := m) (by simpa [A] using hg)
      (by simpa [A] using hg0) (by simpa [A] using hgBound)
      hm hgCenter hratio hz
  have hdecomp := logDeriv_eq_canonicalResidual_add_finsum
    hA hfA hg hg0 hlocal hzA hfz
  have hD : D.support.Finite := hfA.meromorphicOn.divisor_ball_support_finite
  have hfTarget : AnalyticOnNhd Complex f
      (closedBall 0 (5 / 6 : Real)) := by
    apply hf.mono
    exact closedBall_subset_closedBall (by norm_num)
  have hE : E.support.Finite :=
    E.finiteSupport (isCompact_closedBall 0 (5 / 6 : Real))
  have hEsupp : E.support ⊆ D.support := by
    intro w hw
    have hwTarget := E.supportWithinDomain hw
    have hwA : w ∈ ball (0 : Complex) A := by
      have hwNorm : ‖w‖ ≤ (5 / 6 : Real) := by
        simpa [mem_closedBall, dist_zero_right] using hwTarget
      simpa [A, mem_ball_zero_iff] using
        hwNorm.trans_lt (by norm_num : (5 / 6 : Real) < 7 / 8)
    have hDE : D w = E w := by
      rw [hfA.mono ball_subset_closedBall |>.divisor_apply hwA,
        hfTarget.divisor_apply hwTarget]
    rw [Function.mem_support] at hw ⊢
    rwa [hDE]
  let phi : Complex -> Complex := fun w => (D w : Complex) *
    (1 / (z - w) + (starRingEnd Complex) w /
      ((A : Complex) ^ 2 - (starRingEnd Complex) w * z))
  let psi : Complex -> Complex := fun w => (E w : Complex) / (z - w)
  have hPhiSupp : phi.support ⊆ D.support := by
    intro w hw
    contrapose! hw
    have hDw : D w = 0 := by
      simpa [Function.mem_support] using hw
    simp [phi, hDw]
  have hPsiSupp : psi.support ⊆ D.support := by
    intro w hw
    apply hEsupp
    contrapose! hw
    have hEw : E w = 0 := by
      simpa [Function.mem_support] using hw
    simp [psi, hEw]
  have hDtoFinset : D.support ⊆ (hD.toFinset : Set Complex) := by
    intro w hw
    exact hD.mem_toFinset.mpr hw
  have hPhi : (∑ᶠ w, phi w) = ∑ w ∈ hD.toFinset, phi w :=
    finsum_eq_sum_of_support_subset _ (hPhiSupp.trans hDtoFinset)
  have hPsi : (∑ᶠ w, psi w) = ∑ w ∈ hD.toFinset, psi w :=
    finsum_eq_sum_of_support_subset _ (hPsiSupp.trans hDtoFinset)
  have hCount : ∑ᶠ w, (D w : Real) ≤ 8 * L := by
    calc
      ∑ᶠ w, (D w : Real) ≤
          ∑ᶠ w, (MeromorphicOn.divisor f
            (closedBall (0 : Complex) A) w : Real) :=
        sum_open_divisor_le_closed hfA
      _ ≤ 8 * L := by
        simpa [A, L] using
          sum_divisor_seven_eighths_le hf hM hm hf0 hmf hbound
  have hCastSupp : (fun w => (D w : Real)).support ⊆ D.support := by
    intro w hw
    exact Int.cast_ne_zero.mp hw
  have hCast : ∑ w ∈ hD.toFinset, (D w : Real) = ∑ᶠ w, (D w : Real) := by
    symm
    exact finsum_eq_sum_of_support_subset _ (hCastSupp.trans hDtoFinset)
  have hTerm : ∀ w ∈ hD.toFinset,
      ‖phi w - psi w‖ ≤ (54 / 5 : Real) * (D w : Real) := by
    intro w hw
    have hwSupp := hD.mem_toFinset.mp hw
    have hwA := D.supportWithinDomain hwSupp
    have hDnonneg : 0 ≤ D w :=
      (hfA.mono ball_subset_closedBall).divisor_nonneg w
    have hDnorm : ‖(D w : Complex)‖ = (D w : Real) := by
      rw [Complex.norm_intCast, ← Int.cast_abs, abs_of_nonneg hDnonneg]
    have hreflect := norm_reflectedCanonicalTerm_le
      (by simpa [A] using hwA) hz
    by_cases hwTarget : w ∈ closedBall (0 : Complex) (5 / 6 : Real)
    · have hDE : D w = E w := by
        rw [hfA.mono ball_subset_closedBall |>.divisor_apply hwA,
          hfTarget.divisor_apply hwTarget]
      have hrewrite : phi w - psi w =
          (D w : Complex) * ((starRingEnd Complex) w /
            ((A : Complex) ^ 2 - (starRingEnd Complex) w * z)) := by
        simp only [phi, psi, hDE]
        ring
      rw [hrewrite, norm_mul, hDnorm]
      calc
        (D w : Real) *
            ‖(starRingEnd Complex) w /
              ((A : Complex) ^ 2 - (starRingEnd Complex) w * z)‖ ≤
            (D w : Real) * (24 / 5 : Real) :=
          mul_le_mul_of_nonneg_left (by simpa [A] using hreflect)
            (by exact_mod_cast hDnonneg)
        _ ≤ (54 / 5 : Real) * (D w : Real) := by
          have : (0 : Real) ≤ (D w : Real) := by exact_mod_cast hDnonneg
          nlinarith
    · have hEw : E w = 0 := E.apply_eq_zero_of_notMem hwTarget
      have hone := norm_one_div_sub_le_of_mem_extractionAnnulus
        (by simpa [A] using hwA) hwTarget hz
      have hrewrite : phi w - psi w = (D w : Complex) *
          (1 / (z - w) + (starRingEnd Complex) w /
            ((A : Complex) ^ 2 - (starRingEnd Complex) w * z)) := by
        simp [phi, psi, hEw]
      rw [hrewrite, norm_mul, hDnorm]
      calc
        (D w : Real) *
            ‖1 / (z - w) + (starRingEnd Complex) w /
              ((A : Complex) ^ 2 - (starRingEnd Complex) w * z)‖ ≤
            (D w : Real) *
              (‖(1 : Complex) / (z - w)‖ +
                ‖(starRingEnd Complex) w /
                  ((A : Complex) ^ 2 - (starRingEnd Complex) w * z)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _)
            (by exact_mod_cast hDnonneg)
        _ ≤ (D w : Real) * (54 / 5 : Real) := by
          have hDreal : (0 : Real) ≤ (D w : Real) := by
            exact_mod_cast hDnonneg
          gcongr
          nlinarith [hone, (by simpa [A] using hreflect)]
        _ = (54 / 5 : Real) * (D w : Real) := by ring
  have hError : ‖∑ w ∈ hD.toFinset, (phi w - psi w)‖ ≤
      (54 / 5 : Real) * ∑ᶠ w, (D w : Real) := by
    calc
      ‖∑ w ∈ hD.toFinset, (phi w - psi w)‖ ≤
          ∑ w ∈ hD.toFinset, (54 / 5 : Real) * (D w : Real) :=
        norm_sum_le_of_le _ hTerm
      _ = (54 / 5 : Real) * ∑ w ∈ hD.toFinset, (D w : Real) := by
        rw [Finset.mul_sum]
      _ = (54 / 5 : Real) * ∑ᶠ w, (D w : Real) := by rw [hCast]
  have hError' : ‖∑ w ∈ hD.toFinset, (phi w - psi w)‖ ≤
      (432 / 5 : Real) * L := by
    calc
      ‖∑ w ∈ hD.toFinset, (phi w - psi w)‖ ≤
          (54 / 5 : Real) * ∑ᶠ w, (D w : Real) := hError
      _ ≤ (54 / 5 : Real) * (8 * L) :=
        mul_le_mul_of_nonneg_left hCount (by norm_num)
      _ = (432 / 5 : Real) * L := by ring
  change ‖logDeriv f z - ∑ᶠ w, psi w‖ ≤ 232 * L
  rw [show logDeriv f z = logDeriv g z + ∑ᶠ w, phi w by
    simpa [A, D, phi] using hdecomp, hPhi, hPsi]
  rw [show logDeriv g z + ∑ w ∈ hD.toFinset, phi w -
      ∑ w ∈ hD.toFinset, psi w =
      logDeriv g z +
        (∑ w ∈ hD.toFinset, phi w - ∑ w ∈ hD.toFinset, psi w) by
    abel]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖logDeriv g z + ∑ w ∈ hD.toFinset, (phi w - psi w)‖ ≤
        ‖logDeriv g z‖ +
          ‖∑ w ∈ hD.toFinset, (phi w - psi w)‖ := norm_add_le _ _
    _ ≤ 144 * L + (432 / 5 : Real) * L := add_le_add hgLog hError'
    _ ≤ 232 * L := by
      have hL : 0 ≤ L := (Real.log_pos hratio).le
      nlinarith

end PrimesRestrictedDigits
