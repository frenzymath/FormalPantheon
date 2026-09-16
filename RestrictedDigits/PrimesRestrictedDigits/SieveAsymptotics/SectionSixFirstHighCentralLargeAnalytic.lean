import PrimesRestrictedDigits.BasicEstimates.CayleyLogUpper
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabFiberIntegrals
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralLargeFiberReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstHighCentralLargeAnalytic -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstHighCentralLargeCertificateTailConstant : Real :=
  564383 / 1000000

def sectionSixFirstHighCentralLargeCertificateMiddleConstant : Real :=
  70893 / 125000

def sectionSixFirstHighCentralLargeCertificateMixedTailMajorant (u : Real) : Real :=
  sectionSixFirstHighCentralLargeCertificateTailConstant / u *
      (1 / sectionSixFirstHighCentralLargeCertificateLower u -
        1 / sectionSixFirstHighCentralLargeCertificateMiddle u)

def sectionSixFirstHighCentralLargeCertificateMixedMiddleMajorant (u : Real) : Real :=
  sectionSixFirstHighCentralLargeCertificateMiddleConstant / u *
      (1 / sectionSixFirstHighCentralLargeCertificateMiddle u -
        1 / sectionSixFirstHighCentralLargeCertificateUpper u)

def sectionSixFirstHighCentralLargeCertificateTailMajorant (u : Real) : Real :=
  sectionSixFirstHighCentralLargeCertificateTailConstant / u *
    (1 / sectionSixFirstHighCentralLargeCertificateLower u -
      1 / sectionSixFirstHighCentralLargeCertificateUpper u)

private theorem i8_buchstab_intervalIntegrable
    {u B l h : Real} (hu : 0 < u) (hl : 0 < l) (hlh : l < h)
    (hupper : 2 * h ≤ B) :
    IntervalIntegrable
      (fun t : Real => buchstabFunction ((B - t) / t) / (u * t ^ 2))
      volume l h := by
  have hratio : ContinuousOn (fun t : Real => (B - t) / t)
      (uIcc l h) := by
    apply (continuousOn_const.sub continuousOn_id).div continuousOn_id
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    exact (hl.trans_le ht.1).ne'
  have hmaps : MapsTo (fun t : Real => (B - t) / t)
      (uIcc l h) (Ici 1) := by
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    rw [mem_Ici, le_div_iff₀ (hl.trans_le ht.1)]
    linarith [ht.2, hupper]
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_buchstabFunction.comp hratio hmaps).div (by fun_prop)
  intro t ht
  rw [uIcc_of_le hlh.le] at ht
  have htPos : 0 < t := hl.trans_le ht.1
  positivity

theorem sectionSixFirstHighCentralLargeCertificate_buchstab_intervalIntegrable
    {u B l h : Real} (hu : 0 < u) (hl : 0 < l) (hlh : l < h)
    (hupper : 2 * h ≤ B) :
    IntervalIntegrable
      (fun t : Real => buchstabFunction ((B - t) / t) / (u * t ^ 2))
      volume l h := by
  exact i8_buchstab_intervalIntegrable hu hl hlh hupper

private theorem intervalIntegral_twoPole_strict
    {X a b : Real} (hX : 0 < X) (ha : 0 < a)
    (hab : a < b) (hbX : b < X) :
    (∫ t in a..b, 1 / (t * (X - t))) =
      1 / X * Real.log (b * (X - a) / (a * (X - b))) := by
  let F : Real → Real := fun t =>
    1 / X * (Real.log t - Real.log (X - t))
  have hderiv : ∀ t : Real, t ∈ uIcc a b →
      HasDerivAt F (1 / (t * (X - t))) t := by
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    have htPos : 0 < t := ha.trans_le ht.1
    have hXtPos : 0 < X - t := sub_pos.mpr (ht.2.trans_lt hbX)
    have hsub : HasDerivAt (fun s : Real => X - s) (-1) t :=
      (hasDerivAt_id t).const_sub X
    dsimp [F]
    convert (Real.hasDerivAt_log htPos.ne').sub
      ((Real.hasDerivAt_log hXtPos.ne').comp t hsub) |>.const_mul (1 / X)
      using 1 <;> first | rfl | (field_simp [hX.ne']; ring)
  have hint : IntervalIntegrable
      (fun t : Real => 1 / (t * (X - t))) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    have htPos : 0 < t := ha.trans_le ht.1
    have hXtPos : 0 < X - t := sub_pos.mpr (ht.2.trans_lt hbX)
    fun_prop (disch := positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hXa : 0 < X - a := sub_pos.mpr (hab.trans hbX)
  have hXb : 0 < X - b := sub_pos.mpr hbX
  dsimp [F]
  rw [Real.log_div (mul_pos (by linarith) hXa).ne'
      (mul_pos ha hXb).ne',
    Real.log_mul (ne_of_gt (by linarith : 0 < b)) hXa.ne',
    Real.log_mul ha.ne' hXb.ne']
  ring

private theorem intervalIntegral_twoPole_eq
    {X a b : Real} (hX : 0 < X) (ha : 0 < a)
    (hab : a ≤ b) (hbX : b < X) :
    (∫ t in a..b, 1 / (t * (X - t))) =
      1 / X * Real.log (b * (X - a) / (a * (X - b))) := by
  rcases hab.eq_or_lt with rfl | hab
  · have hXa : X - a ≠ 0 := (sub_pos.mpr hbX).ne'
    simp [ha.ne', hXa]
  · exact intervalIntegral_twoPole_strict hX ha hab hbX

theorem sectionSixFirstHighCentralLargeCertificate_twoPole
    {X a b : Real} (hX : 0 < X) (ha : 0 < a)
    (hab : a ≤ b) (hbX : b < X) :
    (∫ t in a..b, 1 / (t * (X - t))) =
      1 / X * Real.log (b * (X - a) / (a * (X - b))) := by
  exact intervalIntegral_twoPole_eq hX ha hab hbX

theorem sectionSixFirstHighCentralLargeCertificate_twoPole_integrable
    {X a b : Real} (_hX : 0 < X) (ha : 0 < a)
    (hab : a ≤ b) (hbX : b < X) :
    IntervalIntegrable (fun t : Real => 1 / (t * (X - t))) volume a b := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    have htPos : 0 < t := ha.trans_le ht.1
    have hXtPos : 0 < X - t := sub_pos.mpr (ht.2.trans_lt hbX)
    fun_prop (disch := positivity)

theorem sectionSixFirstHighCentralLargeCertificate_mixed_tail_inner_le
    {u : Real}
    (hu : u ∈ sectionSixFirstHighCentralLargeCertificateOuter 0) :
    (∫ v in sectionSixFirstHighCentralLargeCertificateLower u..
        sectionSixFirstHighCentralLargeCertificateMiddle u,
      sectionSixFirstHighCentralLargeCertificateTransposedKernel (u, v)) ≤
      sectionSixFirstHighCentralLargeCertificateMixedTailMajorant u := by
  have ho := sectionSixFirstHighCentralLargeCertificate_outer_facts 0 hu
  rcases ho with ⟨hbeta, hhalf, huPos, hLPos, hLH, hLM, hMH, hHcap⟩
  have hMH' : sectionSixFirstHighCentralLargeCertificateMiddle u ≤
      sectionSixFirstHighCentralLargeCertificateUpper u := by
    simpa using hMH
  have hbound := integral_sectionSixBuchstabTailBranch_le
    (u := u) (v := 1) (w := 1) (B := 1 - u)
    (l := sectionSixFirstHighCentralLargeCertificateLower u)
    (h := sectionSixFirstHighCentralLargeCertificateMiddle u)
    huPos (by norm_num) (by norm_num) hLPos hLM (by
      dsimp [sectionSixFirstHighCentralLargeCertificateMiddle]
      ring_nf
      exact le_rfl)
  simpa [sectionSixFirstHighCentralLargeCertificateTransposedKernel,
    sectionSixFirstPairBuchstabKernel,
    sectionSixFirstHighCentralLargeCertificateTailConstant,
    sectionSixFirstHighCentralLargeCertificateMixedTailMajorant] using hbound

theorem sectionSixFirstHighCentralLargeCertificate_mixed_middle_inner_le
    {u : Real}
    (hu : u ∈ sectionSixFirstHighCentralLargeCertificateOuter 0) :
    (∫ v in sectionSixFirstHighCentralLargeCertificateMiddle u..
        sectionSixFirstHighCentralLargeCertificateUpper u,
      sectionSixFirstHighCentralLargeCertificateTransposedKernel (u, v)) ≤
      sectionSixFirstHighCentralLargeCertificateMixedMiddleMajorant u := by
  have ho := sectionSixFirstHighCentralLargeCertificate_outer_facts 0 hu
  rcases ho with ⟨hbeta, hhalf, huPos, hLPos, hLH, hLM, hMH, hHcap⟩
  have hMH' : sectionSixFirstHighCentralLargeCertificateMiddle u ≤
      sectionSixFirstHighCentralLargeCertificateUpper u := by
    simpa using hMH
  have hthird := sectionSixFirstHighCentralLargeCertificate_upper_le_third 0 hu
  have hMPos : 0 < sectionSixFirstHighCentralLargeCertificateMiddle u := by
    simp [sectionSixFirstHighCentralLargeCertificateMiddle]
    linarith
  have hbound := integral_sectionSixBuchstabMiddleBranch_le
    (u := u) (v := 1) (w := 1) (B := 1 - u)
    (l := sectionSixFirstHighCentralLargeCertificateMiddle u)
    (h := sectionSixFirstHighCentralLargeCertificateUpper u)
    huPos (by norm_num) (by norm_num) hMPos hMH'
    (by linarith [hthird]) (by
      dsimp [sectionSixFirstHighCentralLargeCertificateMiddle]
      linarith)
  simpa [sectionSixFirstHighCentralLargeCertificateTransposedKernel,
    sectionSixFirstPairBuchstabKernel,
    sectionSixFirstHighCentralLargeCertificateMiddleConstant,
    sectionSixFirstHighCentralLargeCertificateMixedMiddleMajorant] using hbound

theorem sectionSixFirstHighCentralLargeCertificate_tail_inner_le
    {u : Real}
    (hu : u ∈ sectionSixFirstHighCentralLargeCertificateOuter 1) :
    (∫ v in sectionSixFirstHighCentralLargeCertificateLower u..
        sectionSixFirstHighCentralLargeCertificateUpper u,
      sectionSixFirstHighCentralLargeCertificateTransposedKernel (u, v)) ≤
      sectionSixFirstHighCentralLargeCertificateTailMajorant u := by
  have ho := sectionSixFirstHighCentralLargeCertificate_outer_facts 1 hu
  rcases ho with ⟨hbeta, hhalf, huPos, hLPos, hLH, hLM, hHM, hHcap⟩
  have hHM' : sectionSixFirstHighCentralLargeCertificateUpper u ≤
      sectionSixFirstHighCentralLargeCertificateMiddle u := by
    simpa using hHM
  have hbound := integral_sectionSixBuchstabTailBranch_le
    (u := u) (v := 1) (w := 1) (B := 1 - u)
    (l := sectionSixFirstHighCentralLargeCertificateLower u)
    (h := sectionSixFirstHighCentralLargeCertificateUpper u)
    huPos (by norm_num) (by norm_num) hLPos hLH (by
      have := hHM'
      simp [sectionSixFirstHighCentralLargeCertificateMiddle] at this
      linarith)
  simpa [sectionSixFirstHighCentralLargeCertificateTransposedKernel,
    sectionSixFirstPairBuchstabKernel,
    sectionSixFirstHighCentralLargeCertificateTailConstant,
    sectionSixFirstHighCentralLargeCertificateTailMajorant] using hbound

theorem sectionSixFirstHighCentralLargeCertificate_mixed_tail_partial_fraction {u : Real}
    (hu : u ∈ sectionSixFirstHighCentralLargeCertificateOuter 0) :
    sectionSixFirstHighCentralLargeCertificateMixedTailMajorant u =
      2 * sectionSixFirstHighCentralLargeCertificateTailConstant /
          (u * (sectionSixFirstHighCentralLargeCertificateA - u)) -
        4 * sectionSixFirstHighCentralLargeCertificateTailConstant /
          (u * (1 - u)) := by
  have ho := sectionSixFirstHighCentralLargeCertificate_outer_facts 0 hu
  rcases ho with ⟨hbeta, hhalf, huPos, hLPos, hLH, hLM, hMH, hHcap⟩
  have hApos : 0 < sectionSixFirstHighCentralLargeCertificateA - u := by
    simp [sectionSixFirstHighCentralLargeCertificateLower] at hLPos
    linarith
  have hden : 0 < u * (sectionSixFirstHighCentralLargeCertificateA - u) :=
    mul_pos huPos hApos
  have hden1 : 0 < u * (1 - u) := by
    exact mul_pos huPos (by linarith [hhalf])
  simp [sectionSixFirstHighCentralLargeCertificateMixedTailMajorant,
    sectionSixFirstHighCentralLargeCertificateTailConstant,
    sectionSixFirstHighCentralLargeCertificateLower,
    sectionSixFirstHighCentralLargeCertificateMiddle]
  field_simp [hden.ne', hden1.ne']

theorem sectionSixFirstHighCentralLargeCertificate_mixed_middle_partial_fraction {u : Real}
    (hu : u ∈ sectionSixFirstHighCentralLargeCertificateOuter 0) :
    sectionSixFirstHighCentralLargeCertificateMixedMiddleMajorant u =
      4 * sectionSixFirstHighCentralLargeCertificateMiddleConstant /
          (u * (1 - u)) -
        sectionSixFirstHighCentralLargeCertificateMiddleConstant /
          (u * (sectionSixFirstHighCentralLargeCertificateC - u)) := by
  have ho := sectionSixFirstHighCentralLargeCertificate_outer_facts 0 hu
  rcases ho with ⟨hbeta, hhalf, huPos, hLPos, hLH, hLM, hMH, hHcap⟩
  have hden1 : 0 < u * (1 - u) := by
    exact mul_pos huPos (by linarith [hhalf])
  have hCpos : 0 < sectionSixFirstHighCentralLargeCertificateC - u := by
    simp [sectionSixFirstHighCentralLargeCertificateUpper] at hLH
    linarith
  have hdenC : 0 < u *
      (sectionSixFirstHighCentralLargeCertificateC - u) :=
    mul_pos huPos hCpos
  simp [sectionSixFirstHighCentralLargeCertificateMixedMiddleMajorant,
    sectionSixFirstHighCentralLargeCertificateMiddleConstant,
    sectionSixFirstHighCentralLargeCertificateMiddle,
    sectionSixFirstHighCentralLargeCertificateUpper]
  field_simp [hden1.ne', hdenC.ne']

theorem sectionSixFirstHighCentralLargeCertificate_tail_partial_fraction {u : Real}
    (hu : u ∈ sectionSixFirstHighCentralLargeCertificateOuter 1) :
    sectionSixFirstHighCentralLargeCertificateTailMajorant u =
      2 * sectionSixFirstHighCentralLargeCertificateTailConstant /
          (u * (sectionSixFirstHighCentralLargeCertificateA - u)) -
        sectionSixFirstHighCentralLargeCertificateTailConstant /
          (u * (sectionSixFirstHighCentralLargeCertificateC - u)) := by
  have ho := sectionSixFirstHighCentralLargeCertificate_outer_facts 1 hu
  rcases ho with ⟨hbeta, hhalf, huPos, hLPos, hLH, hLM, hHM, hHcap⟩
  have hApos : 0 < sectionSixFirstHighCentralLargeCertificateA - u := by
    simp [sectionSixFirstHighCentralLargeCertificateLower] at hLPos
    linarith
  have hdenA : 0 < u *
      (sectionSixFirstHighCentralLargeCertificateA - u) :=
    mul_pos huPos hApos
  have hCpos : 0 < sectionSixFirstHighCentralLargeCertificateC - u := by
    simp [sectionSixFirstHighCentralLargeCertificateUpper] at hLH
    linarith
  have hdenC : 0 < u *
      (sectionSixFirstHighCentralLargeCertificateC - u) :=
    mul_pos huPos hCpos
  simp [sectionSixFirstHighCentralLargeCertificateTailMajorant,
    sectionSixFirstHighCentralLargeCertificateTailConstant,
    sectionSixFirstHighCentralLargeCertificateLower,
    sectionSixFirstHighCentralLargeCertificateUpper]
  field_simp [hdenA.ne', hdenC.ne']

theorem sectionSixFirstHighCentralLargeCertificate_intervalIntegral_twoPole
    {X a b : Real} (hX : 0 < X) (ha : 0 < a)
    (hab : a ≤ b) (hbX : b < X) :
    (∫ u in a..b, 1 / (u * (X - u))) =
      1 / X * Real.log (b * (X - a) / (a * (X - b))) :=
  intervalIntegral_twoPole_eq hX ha hab hbX

theorem sectionSixFirstHighCentralLargeCertificate_intervalIntegral_twoPole_integrable
    {X a b : Real} (_hX : 0 < X) (ha : 0 < a)
    (hab : a ≤ b) (hbX : b < X) :
    IntervalIntegrable (fun u : Real => 1 / (u * (X - u))) volume a b := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro u hu
    rw [uIcc_of_le hab.le] at hu
    have huPos : 0 < u := ha.trans_le hu.1
    have hXuPos : 0 < X - u := sub_pos.mpr (hu.2.trans_lt hbX)
    fun_prop (disch := positivity)

end

end PrimesRestrictedDigits
