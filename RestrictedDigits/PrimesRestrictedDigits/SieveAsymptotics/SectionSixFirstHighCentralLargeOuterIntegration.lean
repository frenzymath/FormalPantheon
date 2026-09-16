import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralLargeAnalytic
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralLargeLogCertificate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # SectionSixFirstHighCentralLargeOuterIntegration -/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

private theorem log_prod_div_prod {x y z w : Real}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w) :
    Real.log (x * y / (z * w)) = Real.log (x / z) + Real.log (y / w) := by
  have hEq : x * y / (z * w) = (x / z) * (y / w) := by
    field_simp
  rw [hEq, Real.log_mul (div_pos hx hz).ne' (div_pos hy hw).ne',
    Real.log_div hx.ne' hz.ne', Real.log_div hy.ne' hw.ne']

private theorem const_twoPole_integral {X a b k : Real}
    (hX : 0 < X) (ha : 0 < a) (hab : a ≤ b) (hbX : b < X) :
    (∫ t in a..b, k / (t * (X - t))) =
      k / X * Real.log (b * (X - a) / (a * (X - b))) := by
  have h := sectionSixFirstHighCentralLargeCertificate_twoPole hX ha hab hbX
  calc
    (∫ t in a..b, k / (t * (X - t))) =
        ∫ t in a..b, k * (1 / (t * (X - t))) := by
      apply intervalIntegral.integral_congr
      intro t ht
      ring
    _ = k * (∫ t in a..b, 1 / (t * (X - t))) :=
      intervalIntegral.integral_const_mul k _
    _ = k / X * Real.log (b * (X - a) / (a * (X - b))) := by
      rw [h]
      ring

private theorem const_twoPole_product_integral {X a b k : Real}
    (hX : 0 < X) (ha : 0 < a) (hab : a ≤ b) (hbX : b < X) :
    (∫ t in a..b, k * (1 / (t * (X - t)))) =
      k / X * Real.log (b * (X - a) / (a * (X - b))) := by
  simpa [div_eq_mul_inv] using
    (const_twoPole_integral (X := X) (a := a) (b := b) (k := k)
      hX ha hab hbX)

private theorem twoPole_integrable {X a b : Real}
    (hX : 0 < X) (ha : 0 < a) (hab : a ≤ b) (hbX : b < X) :
    IntervalIntegrable (fun t : Real => 1 / (t * (X - t))) volume a b :=
  sectionSixFirstHighCentralLargeCertificate_twoPole_integrable hX ha hab hbX

private theorem endpoint_facts :
    0 < sectionSixFirstHighCentralLargeCertificateBeta ∧
    sectionSixFirstHighCentralLargeCertificateBeta ≤
      sectionSixFirstHighCentralLargeCertificateU3 ∧
    sectionSixFirstHighCentralLargeCertificateU3 <
      sectionSixFirstHighCentralLargeCertificateA ∧
    sectionSixFirstHighCentralLargeCertificateU3 < (1 : Real) ∧
    sectionSixFirstHighCentralLargeCertificateU3 ≤ (1 / 2 : Real) ∧
    (1 / 2 : Real) < sectionSixFirstHighCentralLargeCertificateA ∧
    sectionSixFirstHighCentralLargeCertificateU3 <
      sectionSixFirstHighCentralLargeCertificateC ∧
    (1 / 2 : Real) < sectionSixFirstHighCentralLargeCertificateC := by
  norm_num [sectionSixFirstHighCentralLargeCertificateBeta,
    sectionSixFirstHighCentralLargeCertificateU3,
    sectionSixFirstHighCentralLargeCertificateA,
    sectionSixFirstHighCentralLargeCertificateC]

theorem sectionSixFirstHighCentralLargeCertificate_mixedTail_outer_eq :
    (∫ u in sectionSixFirstHighCentralLargeCertificateOuter 0,
      sectionSixFirstHighCentralLargeCertificateMixedTailMajorant u) =
      (564383 / 1000000 : Real) *
        ((2 / sectionSixFirstHighCentralLargeCertificateA - 4) *
            Real.log sectionSixFirstHighCentralLargeCertificateRatioU3Beta +
          (2 / sectionSixFirstHighCentralLargeCertificateA) *
            Real.log sectionSixFirstHighCentralLargeCertificateRatioABetaAU3 -
          4 * Real.log sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3) := by
  rcases endpoint_facts with ⟨hβ, hβs, hsA, hs1, hsHalf, hHalfA, hsC, hHalfC⟩
  have hA := twoPole_integrable (X := sectionSixFirstHighCentralLargeCertificateA)
    (by norm_num [sectionSixFirstHighCentralLargeCertificateA]) hβ hβs hsA
  have h1 := twoPole_integrable (X := (1 : Real)) (by norm_num) hβ hβs hs1
  have hsub := hA.const_mul (2 * sectionSixFirstHighCentralLargeCertificateTailConstant)
  have hsub1 := h1.const_mul (4 * sectionSixFirstHighCentralLargeCertificateTailConstant)
  have hsubDiv : IntervalIntegrable (fun u : Real =>
      2 * sectionSixFirstHighCentralLargeCertificateTailConstant /
        (u * (sectionSixFirstHighCentralLargeCertificateA - u))) volume
      sectionSixFirstHighCentralLargeCertificateBeta
        sectionSixFirstHighCentralLargeCertificateU3 := by
    simpa [div_eq_mul_inv] using hsub
  have hsub1Div : IntervalIntegrable (fun u : Real =>
      4 * sectionSixFirstHighCentralLargeCertificateTailConstant /
        (u * (1 - u))) volume
      sectionSixFirstHighCentralLargeCertificateBeta
        sectionSixFirstHighCentralLargeCertificateU3 := by
    simpa [div_eq_mul_inv] using hsub1
  change (∫ u in Icc sectionSixFirstHighCentralLargeCertificateBeta
      sectionSixFirstHighCentralLargeCertificateU3,
      sectionSixFirstHighCentralLargeCertificateMixedTailMajorant u) = _
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hβs]
  rw [intervalIntegral.integral_congr (fun u hu => by
    have hu' : u ∈ sectionSixFirstHighCentralLargeCertificateOuter 0 := by
      change u ∈ Icc sectionSixFirstHighCentralLargeCertificateBeta
        sectionSixFirstHighCentralLargeCertificateU3
      rw [uIcc_of_le hβs] at hu
      exact hu
    exact sectionSixFirstHighCentralLargeCertificate_mixed_tail_partial_fraction hu')]
  rw [intervalIntegral.integral_sub hsubDiv hsub1Div,
    const_twoPole_integral (X := sectionSixFirstHighCentralLargeCertificateA)
      (by norm_num [sectionSixFirstHighCentralLargeCertificateA]) hβ hβs hsA,
    const_twoPole_integral (X := (1 : Real)) (by norm_num) hβ hβs hs1]
  have hlog := log_prod_div_prod
    (x := sectionSixFirstHighCentralLargeCertificateU3)
    (y := sectionSixFirstHighCentralLargeCertificateA -
      sectionSixFirstHighCentralLargeCertificateBeta)
    (z := sectionSixFirstHighCentralLargeCertificateBeta)
    (w := sectionSixFirstHighCentralLargeCertificateA -
      sectionSixFirstHighCentralLargeCertificateU3)
    (by norm_num [sectionSixFirstHighCentralLargeCertificateU3])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateA,
      sectionSixFirstHighCentralLargeCertificateBeta])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateBeta])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateA,
      sectionSixFirstHighCentralLargeCertificateU3])
  have hlog1 := log_prod_div_prod
    (x := sectionSixFirstHighCentralLargeCertificateU3)
    (y := 1 - sectionSixFirstHighCentralLargeCertificateBeta)
    (z := sectionSixFirstHighCentralLargeCertificateBeta)
    (w := 1 - sectionSixFirstHighCentralLargeCertificateU3)
    (by norm_num [sectionSixFirstHighCentralLargeCertificateU3])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateBeta])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateBeta])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateU3])
  rw [hlog, hlog1]
  have hq0 :
      sectionSixFirstHighCentralLargeCertificateU3 /
          sectionSixFirstHighCentralLargeCertificateBeta =
        sectionSixFirstHighCentralLargeCertificateRatioU3Beta := by
    rfl
  have hqA :
      (sectionSixFirstHighCentralLargeCertificateA -
          sectionSixFirstHighCentralLargeCertificateBeta) /
          (sectionSixFirstHighCentralLargeCertificateA -
            sectionSixFirstHighCentralLargeCertificateU3) =
        sectionSixFirstHighCentralLargeCertificateRatioABetaAU3 := by
    rfl
  have hq1 :
      (1 - sectionSixFirstHighCentralLargeCertificateBeta) /
          (1 - sectionSixFirstHighCentralLargeCertificateU3) =
        sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3 := by
    rfl
  rw [hq0, hqA, hq1]
  simp only [sectionSixFirstHighCentralLargeCertificateTailConstant]
  ring

theorem sectionSixFirstHighCentralLargeCertificate_mixedMiddle_outer_eq :
    (∫ u in sectionSixFirstHighCentralLargeCertificateOuter 0,
      sectionSixFirstHighCentralLargeCertificateMixedMiddleMajorant u) =
      (70893 / 125000 : Real) *
        (((4 * sectionSixFirstHighCentralLargeCertificateC - 1) /
          sectionSixFirstHighCentralLargeCertificateC) *
          Real.log sectionSixFirstHighCentralLargeCertificateRatioU3Beta +
        4 * Real.log sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3 -
        (1 / sectionSixFirstHighCentralLargeCertificateC) *
          Real.log sectionSixFirstHighCentralLargeCertificateRatioCBetaCU3) := by
  rcases endpoint_facts with ⟨hβ, hβs, hsA, hs1, hsHalf, hHalfA, hsC, hHalfC⟩
  have h1 := twoPole_integrable (X := (1 : Real)) (by norm_num) hβ hβs hs1
  have hC := twoPole_integrable (X := sectionSixFirstHighCentralLargeCertificateC)
    (by norm_num [sectionSixFirstHighCentralLargeCertificateC]) hβ hβs hsC
  have h1Div : IntervalIntegrable (fun u : Real =>
      4 * sectionSixFirstHighCentralLargeCertificateMiddleConstant /
        (u * (1 - u))) volume
      sectionSixFirstHighCentralLargeCertificateBeta
        sectionSixFirstHighCentralLargeCertificateU3 := by
    simpa [div_eq_mul_inv] using
      (h1.const_mul (4 * sectionSixFirstHighCentralLargeCertificateMiddleConstant))
  have hCDiv : IntervalIntegrable (fun u : Real =>
      sectionSixFirstHighCentralLargeCertificateMiddleConstant /
        (u * (sectionSixFirstHighCentralLargeCertificateC - u))) volume
      sectionSixFirstHighCentralLargeCertificateBeta
        sectionSixFirstHighCentralLargeCertificateU3 := by
    simpa [div_eq_mul_inv] using
      (hC.const_mul sectionSixFirstHighCentralLargeCertificateMiddleConstant)
  change (∫ u in Icc sectionSixFirstHighCentralLargeCertificateBeta
      sectionSixFirstHighCentralLargeCertificateU3,
      sectionSixFirstHighCentralLargeCertificateMixedMiddleMajorant u) = _
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hβs]
  rw [intervalIntegral.integral_congr (fun u hu => by
    have hu' : u ∈ sectionSixFirstHighCentralLargeCertificateOuter 0 := by
      change u ∈ Icc sectionSixFirstHighCentralLargeCertificateBeta
        sectionSixFirstHighCentralLargeCertificateU3
      rw [uIcc_of_le hβs] at hu
      exact hu
    exact sectionSixFirstHighCentralLargeCertificate_mixed_middle_partial_fraction hu')]
  rw [intervalIntegral.integral_sub h1Div hCDiv,
    const_twoPole_integral (X := (1 : Real)) (by norm_num) hβ hβs hs1,
    const_twoPole_integral (X := sectionSixFirstHighCentralLargeCertificateC)
      (by norm_num [sectionSixFirstHighCentralLargeCertificateC]) hβ hβs hsC]
  have hlog1 := log_prod_div_prod
    (x := sectionSixFirstHighCentralLargeCertificateU3)
    (y := 1 - sectionSixFirstHighCentralLargeCertificateBeta)
    (z := sectionSixFirstHighCentralLargeCertificateBeta)
    (w := 1 - sectionSixFirstHighCentralLargeCertificateU3)
    (by norm_num [sectionSixFirstHighCentralLargeCertificateU3])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateBeta])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateBeta])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateU3])
  have hlogC := log_prod_div_prod
    (x := sectionSixFirstHighCentralLargeCertificateU3)
    (y := sectionSixFirstHighCentralLargeCertificateC -
      sectionSixFirstHighCentralLargeCertificateBeta)
    (z := sectionSixFirstHighCentralLargeCertificateBeta)
    (w := sectionSixFirstHighCentralLargeCertificateC -
      sectionSixFirstHighCentralLargeCertificateU3)
    (by norm_num [sectionSixFirstHighCentralLargeCertificateU3])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateC,
      sectionSixFirstHighCentralLargeCertificateBeta])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateBeta])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateC,
      sectionSixFirstHighCentralLargeCertificateU3])
  rw [hlog1, hlogC]
  have hq0 :
      sectionSixFirstHighCentralLargeCertificateU3 /
          sectionSixFirstHighCentralLargeCertificateBeta =
        sectionSixFirstHighCentralLargeCertificateRatioU3Beta := by
    rfl
  have hq1 :
      (1 - sectionSixFirstHighCentralLargeCertificateBeta) /
          (1 - sectionSixFirstHighCentralLargeCertificateU3) =
        sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3 := by
    rfl
  have hqC :
      (sectionSixFirstHighCentralLargeCertificateC -
          sectionSixFirstHighCentralLargeCertificateBeta) /
          (sectionSixFirstHighCentralLargeCertificateC -
            sectionSixFirstHighCentralLargeCertificateU3) =
        sectionSixFirstHighCentralLargeCertificateRatioCBetaCU3 := by
    rfl
  rw [hq0, hq1, hqC]
  simp only [sectionSixFirstHighCentralLargeCertificateMiddleConstant]
  field_simp [sectionSixFirstHighCentralLargeCertificateC]; ring

theorem sectionSixFirstHighCentralLargeCertificate_tail_outer_eq :
    (∫ u in sectionSixFirstHighCentralLargeCertificateOuter 1,
      sectionSixFirstHighCentralLargeCertificateTailMajorant u) =
      (564383 / 1000000 : Real) *
        (((2 * sectionSixFirstHighCentralLargeCertificateC -
          sectionSixFirstHighCentralLargeCertificateA) /
          (sectionSixFirstHighCentralLargeCertificateA *
            sectionSixFirstHighCentralLargeCertificateC)) *
          Real.log sectionSixFirstHighCentralLargeCertificateRatioHalfU3 +
        (2 / sectionSixFirstHighCentralLargeCertificateA) *
          Real.log sectionSixFirstHighCentralLargeCertificateRatioAU3AHalf -
        (1 / sectionSixFirstHighCentralLargeCertificateC) *
          Real.log sectionSixFirstHighCentralLargeCertificateRatioCU3CHalf) := by
  rcases endpoint_facts with ⟨hβ, hβs, hsA, hs1, hsHalf, hHalfA, hsC, hHalfC⟩
  have hA := twoPole_integrable (X := sectionSixFirstHighCentralLargeCertificateA)
    (a := sectionSixFirstHighCentralLargeCertificateU3) (b := (1 / 2 : Real))
    (by norm_num [sectionSixFirstHighCentralLargeCertificateA])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateU3]) hsHalf hHalfA
  have hC := twoPole_integrable (X := sectionSixFirstHighCentralLargeCertificateC)
    (a := sectionSixFirstHighCentralLargeCertificateU3) (b := (1 / 2 : Real))
    (by norm_num [sectionSixFirstHighCentralLargeCertificateC])
      (by norm_num [sectionSixFirstHighCentralLargeCertificateU3]) hsHalf hHalfC
  have hADiv : IntervalIntegrable (fun u : Real =>
      2 * sectionSixFirstHighCentralLargeCertificateTailConstant /
        (u * (sectionSixFirstHighCentralLargeCertificateA - u))) volume
      sectionSixFirstHighCentralLargeCertificateU3 (1 / 2) := by
    simpa [div_eq_mul_inv] using
      (hA.const_mul (2 * sectionSixFirstHighCentralLargeCertificateTailConstant))
  have hCDiv : IntervalIntegrable (fun u : Real =>
      sectionSixFirstHighCentralLargeCertificateTailConstant /
        (u * (sectionSixFirstHighCentralLargeCertificateC - u))) volume
      sectionSixFirstHighCentralLargeCertificateU3 (1 / 2) := by
    simpa [div_eq_mul_inv] using
      (hC.const_mul sectionSixFirstHighCentralLargeCertificateTailConstant)
  change (∫ u in Icc sectionSixFirstHighCentralLargeCertificateU3 (1 / 2),
      sectionSixFirstHighCentralLargeCertificateTailMajorant u) = _
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hsHalf]
  rw [intervalIntegral.integral_congr (fun u hu => by
    have hu' : u ∈ sectionSixFirstHighCentralLargeCertificateOuter 1 := by
      change u ∈ Icc sectionSixFirstHighCentralLargeCertificateU3 (1 / 2)
      rw [uIcc_of_le hsHalf] at hu
      exact hu
    exact sectionSixFirstHighCentralLargeCertificate_tail_partial_fraction hu')]
  rw [intervalIntegral.integral_sub hADiv hCDiv,
    const_twoPole_integral (X := sectionSixFirstHighCentralLargeCertificateA)
      (by norm_num [sectionSixFirstHighCentralLargeCertificateA])
      (by norm_num [sectionSixFirstHighCentralLargeCertificateU3]) hsHalf hHalfA,
    const_twoPole_integral (X := sectionSixFirstHighCentralLargeCertificateC)
      (by norm_num [sectionSixFirstHighCentralLargeCertificateC])
      (by norm_num [sectionSixFirstHighCentralLargeCertificateU3]) hsHalf hHalfC]
  have hlogA := log_prod_div_prod
    (x := (1 / 2 : Real))
    (y := sectionSixFirstHighCentralLargeCertificateA -
      sectionSixFirstHighCentralLargeCertificateU3)
    (z := sectionSixFirstHighCentralLargeCertificateU3)
    (w := sectionSixFirstHighCentralLargeCertificateA - (1 / 2 : Real))
    (by norm_num)
    (by norm_num [sectionSixFirstHighCentralLargeCertificateA,
      sectionSixFirstHighCentralLargeCertificateU3])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateU3])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateA])
  have hlogC := log_prod_div_prod
    (x := (1 / 2 : Real))
    (y := sectionSixFirstHighCentralLargeCertificateC -
      sectionSixFirstHighCentralLargeCertificateU3)
    (z := sectionSixFirstHighCentralLargeCertificateU3)
    (w := sectionSixFirstHighCentralLargeCertificateC - (1 / 2 : Real))
    (by norm_num)
    (by norm_num [sectionSixFirstHighCentralLargeCertificateC,
      sectionSixFirstHighCentralLargeCertificateU3])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateU3])
    (by norm_num [sectionSixFirstHighCentralLargeCertificateC])
  rw [hlogA, hlogC]
  have hqHalf :
      (1 / 2 : Real) /
          sectionSixFirstHighCentralLargeCertificateU3 =
        sectionSixFirstHighCentralLargeCertificateRatioHalfU3 := by
    rfl
  have hqA :
      (sectionSixFirstHighCentralLargeCertificateA -
          sectionSixFirstHighCentralLargeCertificateU3) /
          (sectionSixFirstHighCentralLargeCertificateA - (1 / 2 : Real)) =
        sectionSixFirstHighCentralLargeCertificateRatioAU3AHalf := by
    rfl
  have hqC :
      (sectionSixFirstHighCentralLargeCertificateC -
          sectionSixFirstHighCentralLargeCertificateU3) /
          (sectionSixFirstHighCentralLargeCertificateC - (1 / 2 : Real)) =
        sectionSixFirstHighCentralLargeCertificateRatioCU3CHalf := by
    rfl
  rw [hqHalf, hqA, hqC]
  simp only [sectionSixFirstHighCentralLargeCertificateTailConstant]
  field_simp [sectionSixFirstHighCentralLargeCertificateA,
    sectionSixFirstHighCentralLargeCertificateC]; ring

end
end PrimesRestrictedDigits
