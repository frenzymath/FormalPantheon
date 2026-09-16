import Waring.Certificate.FifthPowerCoverage
import Waring.Dickson.ChenNumerics
import Waring.Dickson.FiniteIntervalAscent
import Waring.Dickson.IteratedAscent

/-!
# Chen's finite range

This file proves the nonnegative-summand form of Lemma 1 in
[CHEN1964-EN, p. 1547; CHEN1964-ZH, p. 715].
-/

namespace Waring

open Statement Certificate

/-- Three exact instances of Dickson's Theorem 10 extend the twelve-slot
certificate to a fifteen-slot interval beyond Chen's initial endpoint. -/
theorem twelvePowerCoverage_extended :
    RepresentsOn 5 15 2103307 1936185987 := by
  have hthirteen : RepresentsOn 5 13 2103307 16100435 := by
    simpa [fifthPowerCertificateCap] using
      representsOn_succ_of_powerGap (k := 5) (slots := 12) (lower := 2103307)
        (upper := fifthPowerCertificateCap) (m := 25) (by norm_num)
        (by norm_num [fifthPowerCertificateCap]) twelvePowerBaseCoverage
        (by norm_num [fifthPowerCertificateCap])
  have hfourteen : RepresentsOn 5 14 2103307 131956636 := by
    simpa using
      representsOn_succ_of_powerGap (k := 5) (slots := 13) (lower := 2103307)
        (upper := 16100435) (m := 40) (by norm_num) (by norm_num) hthirteen
        (by norm_num)
  simpa using
    representsOn_succ_of_powerGap (k := 5) (slots := 14) (lower := 2103307)
      (upper := 131956636) (m := 70) (by norm_num) (by norm_num) hfourteen
      (by norm_num)

/-- The kernel certificate and finite ascents cover Chen's complete initial
15-slot interval. -/
theorem chen_fifteenPowerBaseInterval :
    RepresentsOn 5 15 470348 1934000000 := by
  intro target hlower hupper
  by_cases hcap : target ≤ fifthPowerCertificateCap
  · exact fifteenPowerBaseCoverage target hlower hcap
  · apply twelvePowerCoverage_extended target
    · have hcapTarget : fifthPowerCertificateCap < target := Nat.lt_of_not_ge hcap
      norm_num [fifthPowerCertificateCap] at hcapTarget ⊢
      omega
    · omega

/-- Dickson's 22 ascent steps give 37-slot coverage from 470348 through the
real endpoint used in Chen's finite-range calculation. -/
theorem chen_thirtySeven_recurrenceInterval :
    RepresentsThrough 5 37 470348
      (dicksonLength 5 chenDicksonNu chenInitialLength 22) := by
  have hascent := dickson_iterated_ascent (n := 5) (slots := 15) (lower := 470348)
    (baseUpper := 1934000000) (nu := chenDicksonNu)
    (initial := chenInitialLength) (by norm_num) chenDicksonNu_pos
    (by norm_num [chenInitialLength]) (by norm_num [chenInitialLength]) rfl
    chen_dicksonLength_one_ge (by norm_num [chenInitialLength])
    chen_fifteenPowerBaseInterval 22
  simpa using hascent

/-- Every positive target through `10^785` is a sum of 37 fifth powers of
naturals. This is the coherent nonnegative-summand reading of Chen's Lemma 1. -/
theorem chen_finite_range {target : Nat} (hpositive : 0 < target)
    (hupper : target ≤ 10 ^ 785) :
    HasPowerSumRepresentation 5 37 target := by
  by_cases hsmall : target < 470348
  · exact thirtySevenSmallCoverage target (Nat.zero_le target) (by omega)
  · apply chen_thirtySeven_recurrenceInterval target (by omega)
    have htargetTen : (target : Real) ≤ (10 : Real) ^ 785 := by
      exact_mod_cast hupper
    exact htargetTen.trans chen_dicksonLength_twentyTwo_ge

end Waring
