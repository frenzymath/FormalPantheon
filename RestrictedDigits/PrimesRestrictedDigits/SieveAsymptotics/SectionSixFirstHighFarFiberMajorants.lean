import PrimesRestrictedDigits.BasicEstimates.BuchstabShortMiddleEnvelope
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabInverseFiberIntegral
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighFarFiberReduction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstHighFarFiberMajorants -/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

private theorem highFar_invSq_strict {C u l h : Real}
    (hu : 0 < u) (hl : 0 < l) (hlh : l < h) :
    (∫ t in l..h, C / (u * t ^ 2)) =
      C / u * (1 / l - 1 / h) := by
  let K : Real := C / u
  have hderiv : ∀ t : Real, t ∈ uIcc l h →
      HasDerivAt (fun s => -K * s⁻¹) (C / (u * t ^ 2)) t := by
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    dsimp only [K]
    convert (hasDerivAt_inv htPos.ne').const_mul (-(C / u)) using 1 <;>
      first | rfl | field_simp
  have hint : IntervalIntegrable (fun t : Real => C / (u * t ^ 2)) volume l h := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    fun_prop (disch := positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [K]
  field_simp [hu.ne', hl.ne', (hl.trans hlh).ne']
  ring

private theorem highFar_invSq {C u l h : Real}
    (hu : 0 < u) (hl : 0 < l) (hlh : l ≤ h) :
    (∫ t in l..h, C / (u * t ^ 2)) =
      C / u * (1 / l - 1 / h) := by
  rcases hlh.eq_or_lt with rfl | hlt
  · simp
  · exact highFar_invSq_strict hu hl hlt

private theorem highFar_buchstab_integrable {u l h : Real}
    (hu : 0 < u) (hl : 0 < l) (hlh : l ≤ h) (hthree : 3 * h ≤ 1 - u) :
    IntervalIntegrable
      (fun t : Real => buchstabFunction ((1 - u - t) / t) / (u * t ^ 2))
      volume l h := by
  rcases hlh.eq_or_lt with rfl | hlh
  · simp
  · have hratio : ContinuousOn (fun t : Real => (1 - u - t) / t) (uIcc l h) := by
      apply (continuousOn_const.sub continuousOn_id).div continuousOn_id
      intro t ht
      rw [uIcc_of_le hlh.le] at ht
      exact (hl.trans_le ht.1).ne'
    have hrange : MapsTo (fun t : Real => (1 - u - t) / t)
        (uIcc l h) (Ici 1) := by
      intro t ht
      rw [uIcc_of_le hlh.le] at ht
      rw [mem_Ici, le_div_iff₀ (hl.trans_le ht.1)]
      linarith [ht.2]
    apply ContinuousOn.intervalIntegrable
    apply (continuousOn_buchstabFunction.comp hratio hrange).div
      (by fun_prop (disch := positivity))
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    positivity

theorem sectionSixFirstHighFarCertificateTail_le {u : Real}
    (hu : u ∈ sectionSixFirstHighFarCertificateOuter 1) :
    (∫ v in sectionSixFirstHighFarCertificateLower u..
        (1 - u) / 3,
      sectionSixFirstHighFarCertificateTransposedKernel (u, v)) ≤
      sectionSixFirstHighFarCertificateEnvelope / u *
        (1 / sectionSixFirstHighFarCertificateLower u -
          3 / (1 - u)) := by
  have hu' : u ∈ Icc (459997 / 1000000 : Real) (1 / 2) := by
    change (459997 / 1000000 : Real) ≤ u ∧ u ≤ 1 / 2 at hu
    exact hu
  have huPos : 0 < u := by norm_num at hu' ⊢; linarith [hu'.1]
  have hB : 0 < 1 - u := by norm_num at hu' ⊢; linarith [hu'.2]
  let l : Real := sectionSixFirstHighFarCertificateLower u
  let h : Real := (1 - u) / 3
  have hl : 0 < l := by
    change 0 < (319999 / 500000 : Real) - u
    norm_num [sectionSixFirstHighFarCertificateA] at hu' ⊢
    linarith [hu'.2]
  have hlh : l ≤ h := by
    change (319999 / 500000 : Real) - u ≤ (1 - u) / 3
    norm_num [sectionSixFirstHighFarCertificateA] at hu' ⊢
    linarith [hu'.1]
  have hthree : 3 * h ≤ 1 - u := by
    dsimp [h]
    have heq : 3 * ((1 - u) / 3) = 1 - u := by ring
    rw [heq]
  have hcap : (1 - u - l) / l ≤ (180001 / 69999 : Real) := by
    change (1 - u - ((319999 / 500000 : Real) - u)) /
      ((319999 / 500000 : Real) - u) ≤ (180001 / 69999 : Real)
    have hden : 0 < (319999 / 500000 : Real) - u := by
      norm_num at hu' ⊢
      linarith [hu'.2]
    rw [div_le_iff₀ hden]
    norm_num at hu' ⊢
    nlinarith
  have hfun := highFar_buchstab_integrable huPos hl hlh hthree
  have hconst : IntervalIntegrable
      (fun t : Real => sectionSixFirstHighFarCertificateEnvelope / (u * t ^ 2))
      volume l h := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [uIcc_of_le hlh] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    fun_prop (disch := positivity)
  calc
    _ = ∫ t in l..h,
        buchstabFunction ((1 - u - t) / t) / (u * t ^ 2) := by
      rfl
    _ ≤ ∫ t in l..h,
        sectionSixFirstHighFarCertificateEnvelope / (u * t ^ 2) := by
      apply intervalIntegral.integral_mono_on hlh hfun hconst
      intro t ht
      have htPos : 0 < t := hl.trans_le ht.1
      have htwo : 2 ≤ (1 - u - t) / t := by
        rw [le_div_iff₀ htPos]
        linarith [ht.2]
      have htop : (1 - u - t) / t ≤ (180001 / 69999 : Real) := by
        rw [div_le_iff₀ htPos]
        have hnum : 1 - u - t ≤ 1 - u - l := by linarith [ht.1]
        have hcap' : 1 - u - l ≤ (180001 / 69999 : Real) * l :=
          (div_le_iff₀ hl).mp hcap
        nlinarith [hnum, hcap', ht.1]
      have hden : 0 < u * t ^ 2 := by positivity
      exact (div_le_div_iff_of_pos_right hden).2
        (buchstabFunction_le_shortMiddleEnvelope htwo htop)
    _ = sectionSixFirstHighFarCertificateEnvelope / u *
        (1 / l - 1 / h) := highFar_invSq huPos hl hlh
    _ = _ := by
      dsimp [h, l]
      field_simp [huPos.ne', hB.ne', hl.ne']

end
end PrimesRestrictedDigits
