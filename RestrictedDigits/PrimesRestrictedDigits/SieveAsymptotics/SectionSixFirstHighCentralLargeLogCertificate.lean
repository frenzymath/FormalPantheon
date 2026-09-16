import PrimesRestrictedDigits.BasicEstimates.CayleyLogUpper
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighCentralLargeFiberReduction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstHighCentralLargeLogCertificate -/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/- The complementary constants are kept here alongside the fiber module. -/
def sectionSixFirstHighCentralLargeCertificateAlphaValue : Real :=
  180000001 / 500000000

def sectionSixFirstHighCentralLargeCertificateGapValue : Real :=
  16249999 / 250000000

def sectionSixFirstHighCentralLargeCertificateRatioU3Beta : Real :=
  sectionSixFirstHighCentralLargeCertificateU3 /
    sectionSixFirstHighCentralLargeCertificateBeta

def sectionSixFirstHighCentralLargeCertificateRatioABetaAU3 : Real :=
  (sectionSixFirstHighCentralLargeCertificateA -
      sectionSixFirstHighCentralLargeCertificateBeta) /
    (sectionSixFirstHighCentralLargeCertificateA -
      sectionSixFirstHighCentralLargeCertificateU3)

def sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3 : Real :=
  (1 - sectionSixFirstHighCentralLargeCertificateBeta) /
    (1 - sectionSixFirstHighCentralLargeCertificateU3)

def sectionSixFirstHighCentralLargeCertificateRatioCBetaCU3 : Real :=
  (sectionSixFirstHighCentralLargeCertificateC -
      sectionSixFirstHighCentralLargeCertificateBeta) /
    (sectionSixFirstHighCentralLargeCertificateC -
      sectionSixFirstHighCentralLargeCertificateU3)

def sectionSixFirstHighCentralLargeCertificateRatioHalfU3 : Real :=
  (1 / 2 : Real) / sectionSixFirstHighCentralLargeCertificateU3

def sectionSixFirstHighCentralLargeCertificateRatioAU3AHalf : Real :=
  (sectionSixFirstHighCentralLargeCertificateA -
      sectionSixFirstHighCentralLargeCertificateU3) /
    (sectionSixFirstHighCentralLargeCertificateA - (1 / 2 : Real))

def sectionSixFirstHighCentralLargeCertificateRatioCU3CHalf : Real :=
  (sectionSixFirstHighCentralLargeCertificateC -
      sectionSixFirstHighCentralLargeCertificateU3) /
    (sectionSixFirstHighCentralLargeCertificateC - (1 / 2 : Real))

def sectionSixFirstHighCentralLargeCertificateLogLower (q : Real) : Real :=
  2 * ∑ i ∈ Finset.range 10,
    ((q - 1) / (q + 1)) ^ (2 * i + 1) / (2 * i + 1)

def sectionSixFirstHighCentralLargeCertificateLogUpper (q : Real) : Real :=
  sectionSixFirstHighCentralLargeCertificateLogLower q +
    2 * ((q - 1) / (q + 1)) ^ 21 /
      (1 - ((q - 1) / (q + 1)) ^ 2)

theorem sectionSixFirstHighCentralLargeCertificateLogLower_le_log
    {q : Real} (hq : 1 ≤ q) :
    sectionSixFirstHighCentralLargeCertificateLogLower q ≤ Real.log q := by
  let x : Real := (q - 1) / (q + 1)
  have hq1 : 0 < q + 1 := by linarith
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (by linarith) hq1.le
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one hq1]
    linarith
  have hratio : (1 + x) / (1 - x) = q := by
    dsimp [x]
    field_simp
    ring
  have hlow := Real.sum_range_le_log_div hx0 hx1 10
  change 2 * ∑ i ∈ Finset.range 10,
      x ^ (2 * i + 1) / (2 * i + 1) ≤ Real.log q
  calc
    _ ≤ Real.log ((1 + x) / (1 - x)) := by linarith
    _ = Real.log q := by rw [hratio]

theorem sectionSixFirstHighCentralLargeCertificate_log_le_LogUpper
    {q : Real} (hq : 1 ≤ q) :
    Real.log q ≤ sectionSixFirstHighCentralLargeCertificateLogUpper q := by
  let x : Real := (q - 1) / (q + 1)
  have hq1 : 0 < q + 1 := by linarith
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (by linarith) hq1.le
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one hq1]
    linarith
  have hratio : (1 + x) / (1 - x) = q := by
    dsimp [x]
    field_simp
    ring
  have hupp := log_cayley_le_cayleyLogSeriesUpper hx0 hx1 10
  change Real.log q ≤
    2 * ∑ i ∈ Finset.range 10,
      x ^ (2 * i + 1) / (2 * i + 1) +
      2 * x ^ 21 / (1 - x ^ 2)
  calc
    Real.log q = Real.log ((1 + x) / (1 - x)) := by rw [hratio]
    _ ≤ 2 * ∑ i ∈ Finset.range 10,
      x ^ (2 * i + 1) / (2 * i + 1) +
        2 * x ^ 21 / (1 - x ^ 2) := by
      unfold cayleyLogSeriesUpper at hupp
      have hupp' : Real.log ((1 + x) / (1 - x)) ≤
          2 * ∑ i ∈ Finset.range 10,
            x ^ (2 * i + 1) / (2 * i + 1) +
            2 * x ^ 21 / (1 - x ^ 2) := by
        calc
          _ ≤ 2 * ∑ i ∈ Finset.range 10,
              x ^ (2 * i + 1) / (2 * i + 1) +
              2 * (x ^ 21 / (1 - x ^ 2)) := by
                simpa only [show 2 * 10 + 1 = 21 by norm_num, mul_add] using hupp
          _ = _ := by ring
      exact hupp'

theorem sectionSixFirstHighCentralLargeCertificate_log_bounds
    {q : Real} (hq : 1 ≤ q) :
    sectionSixFirstHighCentralLargeCertificateLogLower q ≤ Real.log q ∧
      Real.log q ≤ sectionSixFirstHighCentralLargeCertificateLogUpper q :=
  ⟨sectionSixFirstHighCentralLargeCertificateLogLower_le_log hq,
    sectionSixFirstHighCentralLargeCertificate_log_le_LogUpper hq⟩

theorem sectionSixFirstHighCentralLargeCertificate_endpointRatios_gt_one :
    1 < sectionSixFirstHighCentralLargeCertificateRatioU3Beta ∧
    1 < sectionSixFirstHighCentralLargeCertificateRatioABetaAU3 ∧
    1 < sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3 ∧
    1 < sectionSixFirstHighCentralLargeCertificateRatioCBetaCU3 ∧
    1 < sectionSixFirstHighCentralLargeCertificateRatioHalfU3 ∧
    1 < sectionSixFirstHighCentralLargeCertificateRatioAU3AHalf ∧
    1 < sectionSixFirstHighCentralLargeCertificateRatioCU3CHalf := by
  norm_num [sectionSixFirstHighCentralLargeCertificateRatioU3Beta,
    sectionSixFirstHighCentralLargeCertificateRatioABetaAU3,
    sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3,
    sectionSixFirstHighCentralLargeCertificateRatioCBetaCU3,
    sectionSixFirstHighCentralLargeCertificateRatioHalfU3,
    sectionSixFirstHighCentralLargeCertificateRatioAU3AHalf,
    sectionSixFirstHighCentralLargeCertificateRatioCU3CHalf,
    sectionSixFirstHighCentralLargeCertificateA,
    sectionSixFirstHighCentralLargeCertificateBeta,
    sectionSixFirstHighCentralLargeCertificateC,
    sectionSixFirstHighCentralLargeCertificateU3]

def sectionSixFirstHighCentralLargeCertificateLogCombination : Real :=
  (564383 / 1000000 : Real) *
      ((2 / sectionSixFirstHighCentralLargeCertificateA - 4) *
          Real.log sectionSixFirstHighCentralLargeCertificateRatioU3Beta +
        (2 / sectionSixFirstHighCentralLargeCertificateA) *
          Real.log sectionSixFirstHighCentralLargeCertificateRatioABetaAU3 -
        4 * Real.log sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3) +
    (70893 / 125000 : Real) *
      (((4 * sectionSixFirstHighCentralLargeCertificateC - 1) /
          sectionSixFirstHighCentralLargeCertificateC) *
          Real.log sectionSixFirstHighCentralLargeCertificateRatioU3Beta +
        4 * Real.log sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3 -
        (1 / sectionSixFirstHighCentralLargeCertificateC) *
          Real.log sectionSixFirstHighCentralLargeCertificateRatioCBetaCU3) +
    (564383 / 1000000 : Real) *
      (((2 * sectionSixFirstHighCentralLargeCertificateC -
          sectionSixFirstHighCentralLargeCertificateA) /
          (sectionSixFirstHighCentralLargeCertificateA *
            sectionSixFirstHighCentralLargeCertificateC)) *
          Real.log sectionSixFirstHighCentralLargeCertificateRatioHalfU3 +
        (2 / sectionSixFirstHighCentralLargeCertificateA) *
          Real.log sectionSixFirstHighCentralLargeCertificateRatioAU3AHalf -
        (1 / sectionSixFirstHighCentralLargeCertificateC) *
          Real.log sectionSixFirstHighCentralLargeCertificateRatioCU3CHalf)

def sectionSixFirstHighCentralLargeCertificateDirectedAggregate : Real :=
  (564383 / 1000000 : Real) *
      ((2 / sectionSixFirstHighCentralLargeCertificateA - 4) *
          sectionSixFirstHighCentralLargeCertificateLogLower
            sectionSixFirstHighCentralLargeCertificateRatioU3Beta +
        (2 / sectionSixFirstHighCentralLargeCertificateA) *
          sectionSixFirstHighCentralLargeCertificateLogUpper
            sectionSixFirstHighCentralLargeCertificateRatioABetaAU3 -
        4 * sectionSixFirstHighCentralLargeCertificateLogLower
          sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3) +
    (70893 / 125000 : Real) *
      (((4 * sectionSixFirstHighCentralLargeCertificateC - 1) /
          sectionSixFirstHighCentralLargeCertificateC) *
          sectionSixFirstHighCentralLargeCertificateLogUpper
            sectionSixFirstHighCentralLargeCertificateRatioU3Beta +
        4 * sectionSixFirstHighCentralLargeCertificateLogUpper
          sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3 -
        (1 / sectionSixFirstHighCentralLargeCertificateC) *
          sectionSixFirstHighCentralLargeCertificateLogLower
            sectionSixFirstHighCentralLargeCertificateRatioCBetaCU3) +
    (564383 / 1000000 : Real) *
      (((2 * sectionSixFirstHighCentralLargeCertificateC -
          sectionSixFirstHighCentralLargeCertificateA) /
          (sectionSixFirstHighCentralLargeCertificateA *
            sectionSixFirstHighCentralLargeCertificateC)) *
          sectionSixFirstHighCentralLargeCertificateLogUpper
            sectionSixFirstHighCentralLargeCertificateRatioHalfU3 +
        (2 / sectionSixFirstHighCentralLargeCertificateA) *
          sectionSixFirstHighCentralLargeCertificateLogUpper
            sectionSixFirstHighCentralLargeCertificateRatioAU3AHalf -
        (1 / sectionSixFirstHighCentralLargeCertificateC) *
          sectionSixFirstHighCentralLargeCertificateLogLower
            sectionSixFirstHighCentralLargeCertificateRatioCU3CHalf)

theorem sectionSixFirstHighCentralLargeCertificateDirectedAggregate_lt :
    sectionSixFirstHighCentralLargeCertificateDirectedAggregate <
      (203394 : Real) / 1000000 := by
  norm_num [sectionSixFirstHighCentralLargeCertificateDirectedAggregate,
    sectionSixFirstHighCentralLargeCertificateLogLower,
    sectionSixFirstHighCentralLargeCertificateLogUpper,
    sectionSixFirstHighCentralLargeCertificateRatioU3Beta,
    sectionSixFirstHighCentralLargeCertificateRatioABetaAU3,
    sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3,
    sectionSixFirstHighCentralLargeCertificateRatioCBetaCU3,
    sectionSixFirstHighCentralLargeCertificateRatioHalfU3,
    sectionSixFirstHighCentralLargeCertificateRatioAU3AHalf,
    sectionSixFirstHighCentralLargeCertificateRatioCU3CHalf,
    sectionSixFirstHighCentralLargeCertificateA,
    sectionSixFirstHighCentralLargeCertificateBeta,
    sectionSixFirstHighCentralLargeCertificateC,
    sectionSixFirstHighCentralLargeCertificateU3,
    Finset.sum_range_succ]

theorem sectionSixFirstHighCentralLargeCertificateLogCombination_lt :
    sectionSixFirstHighCentralLargeCertificateLogCombination <
      (203394 : Real) / 1000000 := by
  have hr := sectionSixFirstHighCentralLargeCertificate_endpointRatios_gt_one
  have h1L := sectionSixFirstHighCentralLargeCertificateLogLower_le_log hr.1.le
  have h1U := sectionSixFirstHighCentralLargeCertificate_log_le_LogUpper hr.1.le
  have h2L := sectionSixFirstHighCentralLargeCertificateLogLower_le_log hr.2.1.le
  have h2U := sectionSixFirstHighCentralLargeCertificate_log_le_LogUpper hr.2.1.le
  have h3L := sectionSixFirstHighCentralLargeCertificateLogLower_le_log hr.2.2.1.le
  have h3U := sectionSixFirstHighCentralLargeCertificate_log_le_LogUpper hr.2.2.1.le
  have h4L := sectionSixFirstHighCentralLargeCertificateLogLower_le_log hr.2.2.2.1.le
  have h4U := sectionSixFirstHighCentralLargeCertificate_log_le_LogUpper hr.2.2.2.1.le
  have h5L := sectionSixFirstHighCentralLargeCertificateLogLower_le_log hr.2.2.2.2.1.le
  have h5U := sectionSixFirstHighCentralLargeCertificate_log_le_LogUpper hr.2.2.2.2.1.le
  have h6L := sectionSixFirstHighCentralLargeCertificateLogLower_le_log hr.2.2.2.2.2.1.le
  have h6U := sectionSixFirstHighCentralLargeCertificate_log_le_LogUpper hr.2.2.2.2.2.1.le
  have h7L := sectionSixFirstHighCentralLargeCertificateLogLower_le_log hr.2.2.2.2.2.2.le
  have h7U := sectionSixFirstHighCentralLargeCertificate_log_le_LogUpper hr.2.2.2.2.2.2.le
  have hc1 : 2 / sectionSixFirstHighCentralLargeCertificateA - 4 ≤ 0 := by
    norm_num [sectionSixFirstHighCentralLargeCertificateA]
  have hc2 : 0 ≤ 2 / sectionSixFirstHighCentralLargeCertificateA := by
    norm_num [sectionSixFirstHighCentralLargeCertificateA]
  have hc3 : 0 ≤
      (4 * sectionSixFirstHighCentralLargeCertificateC - 1) /
        sectionSixFirstHighCentralLargeCertificateC := by
    norm_num [sectionSixFirstHighCentralLargeCertificateC]
  have hc5 : 0 ≤
      (2 * sectionSixFirstHighCentralLargeCertificateC -
        sectionSixFirstHighCentralLargeCertificateA) /
        (sectionSixFirstHighCentralLargeCertificateA *
          sectionSixFirstHighCentralLargeCertificateC) := by
    norm_num [sectionSixFirstHighCentralLargeCertificateA,
      sectionSixFirstHighCentralLargeCertificateC]
  have hc7 : -(1 / sectionSixFirstHighCentralLargeCertificateC) ≤ 0 := by
    norm_num [sectionSixFirstHighCentralLargeCertificateC]
  have hMT1 := mul_le_mul_of_nonpos_left h1L hc1
  have hMT2 := mul_le_mul_of_nonneg_left h2U hc2
  have hMT3 := mul_le_mul_of_nonpos_left h3L (by norm_num : (-(4 : Real)) ≤ 0)
  have hMM1 := mul_le_mul_of_nonneg_left h1U hc3
  have hMM2 := mul_le_mul_of_nonneg_left h3U (by norm_num : (0 : Real) ≤ 4)
  have hMM3 := mul_le_mul_of_nonpos_left h4L hc7
  have hAT1 := mul_le_mul_of_nonneg_left h5U hc5
  have hAT2 := mul_le_mul_of_nonneg_left h6U hc2
  have hAT3 := mul_le_mul_of_nonpos_left h7L hc7
  have hMT :
      (564383 / 1000000 : Real) *
          ((2 / sectionSixFirstHighCentralLargeCertificateA - 4) *
              Real.log sectionSixFirstHighCentralLargeCertificateRatioU3Beta +
            (2 / sectionSixFirstHighCentralLargeCertificateA) *
              Real.log sectionSixFirstHighCentralLargeCertificateRatioABetaAU3 -
            4 * Real.log sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3) ≤
        (564383 / 1000000 : Real) *
          ((2 / sectionSixFirstHighCentralLargeCertificateA - 4) *
              sectionSixFirstHighCentralLargeCertificateLogLower
                sectionSixFirstHighCentralLargeCertificateRatioU3Beta +
            (2 / sectionSixFirstHighCentralLargeCertificateA) *
              sectionSixFirstHighCentralLargeCertificateLogUpper
                sectionSixFirstHighCentralLargeCertificateRatioABetaAU3 -
            4 * sectionSixFirstHighCentralLargeCertificateLogLower
              sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3) := by
    apply mul_le_mul_of_nonneg_left
    · linarith [hMT1, hMT2, hMT3]
    · norm_num
  have hMM :
      (70893 / 125000 : Real) *
          (((4 * sectionSixFirstHighCentralLargeCertificateC - 1) /
              sectionSixFirstHighCentralLargeCertificateC) *
              Real.log sectionSixFirstHighCentralLargeCertificateRatioU3Beta +
            4 * Real.log sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3 -
            (1 / sectionSixFirstHighCentralLargeCertificateC) *
              Real.log sectionSixFirstHighCentralLargeCertificateRatioCBetaCU3) ≤
        (70893 / 125000 : Real) *
          (((4 * sectionSixFirstHighCentralLargeCertificateC - 1) /
              sectionSixFirstHighCentralLargeCertificateC) *
              sectionSixFirstHighCentralLargeCertificateLogUpper
                sectionSixFirstHighCentralLargeCertificateRatioU3Beta +
            4 * sectionSixFirstHighCentralLargeCertificateLogUpper
              sectionSixFirstHighCentralLargeCertificateRatioOneBetaOneU3 -
            (1 / sectionSixFirstHighCentralLargeCertificateC) *
              sectionSixFirstHighCentralLargeCertificateLogLower
                sectionSixFirstHighCentralLargeCertificateRatioCBetaCU3) := by
    apply mul_le_mul_of_nonneg_left
    · linarith [hMM1, hMM2, hMM3]
    · norm_num
  have hAT :
      (564383 / 1000000 : Real) *
          (((2 * sectionSixFirstHighCentralLargeCertificateC -
              sectionSixFirstHighCentralLargeCertificateA) /
              (sectionSixFirstHighCentralLargeCertificateA *
                sectionSixFirstHighCentralLargeCertificateC)) *
              Real.log sectionSixFirstHighCentralLargeCertificateRatioHalfU3 +
            (2 / sectionSixFirstHighCentralLargeCertificateA) *
              Real.log sectionSixFirstHighCentralLargeCertificateRatioAU3AHalf -
            (1 / sectionSixFirstHighCentralLargeCertificateC) *
              Real.log sectionSixFirstHighCentralLargeCertificateRatioCU3CHalf) ≤
        (564383 / 1000000 : Real) *
          (((2 * sectionSixFirstHighCentralLargeCertificateC -
              sectionSixFirstHighCentralLargeCertificateA) /
              (sectionSixFirstHighCentralLargeCertificateA *
                sectionSixFirstHighCentralLargeCertificateC)) *
              sectionSixFirstHighCentralLargeCertificateLogUpper
                sectionSixFirstHighCentralLargeCertificateRatioHalfU3 +
            (2 / sectionSixFirstHighCentralLargeCertificateA) *
              sectionSixFirstHighCentralLargeCertificateLogUpper
                sectionSixFirstHighCentralLargeCertificateRatioAU3AHalf -
            (1 / sectionSixFirstHighCentralLargeCertificateC) *
              sectionSixFirstHighCentralLargeCertificateLogLower
                sectionSixFirstHighCentralLargeCertificateRatioCU3CHalf) := by
    apply mul_le_mul_of_nonneg_left
    · linarith [hAT1, hAT2, hAT3]
    · norm_num
  have hsum :
      sectionSixFirstHighCentralLargeCertificateLogCombination ≤
        sectionSixFirstHighCentralLargeCertificateDirectedAggregate := by
    dsimp [sectionSixFirstHighCentralLargeCertificateLogCombination,
      sectionSixFirstHighCentralLargeCertificateDirectedAggregate]
    linarith [hMT, hMM, hAT]
  exact lt_of_le_of_lt hsum
    sectionSixFirstHighCentralLargeCertificateDirectedAggregate_lt

end
end PrimesRestrictedDigits
