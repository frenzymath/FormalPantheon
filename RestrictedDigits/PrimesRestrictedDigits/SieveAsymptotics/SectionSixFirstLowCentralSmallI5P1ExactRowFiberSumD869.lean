import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Case1WeightedSectionD830
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1GenericRowOuterComparisonD853
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1RowWeightIntegrabilityD854
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1ExactRowFiberSumD869 -/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-!
# exact Piece1 all-row fiber-sum sharpening

This module evaluates the exact area polynomial on all 256 rows, transports the rational
certificate through the row comparison, and exports only the relaxed row-fiber sum bound. It
makes no row-set, Piece1 set-integral, source, image, Jacobian, or full-I5 claim.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6.
-/

private def ratDs : Rat := 29 / 200
private def ratDr : Rat := 84167 / 500000
private def ratBeta : Rat := 212499 / 500000
private def ratGap : Rat := 16249 / 250000

private def ratLower (i : Nat) : Rat :=
  ratDs + (i : Rat) * (ratDr - ratDs) / 256

private def ratUpper (i : Nat) : Rat :=
  ratDs + ((i + 1 : Nat) : Rat) * (ratDr - ratDs) / 256

private def ratFactor (i : Nat) : Rat :=
  (70893 / 125000 : Rat) / (ratBeta - ratUpper i) *
    (1 / ratGap - 1 / (ratUpper i - ratGap))

private def ratAreaCoeff (a : Rat) : Fin 11 -> Rat := ![
  (1043965001 / 2000000000000 : Rat) / a ^ 2 +
    (6102255942782497 / 6000000000000000000 : Rat) / a ^ 3 +
    (-7942362859115732769989 / 24000000000000000000000000 : Rat) / a ^ 4 +
    (190662734916127953646962499 / 2400000000000000000000000000000 : Rat) / a ^ 5 +
    (-6215838130198815030518838067884863 /
      360000000000000000000000000000000000000 : Rat) / a ^ 6 +
    (296295264276911647510945771376120269141 /
      140000000000000000000000000000000000000000000 : Rat) / a ^ 7 +
    (-823475809860508523734554597501364526542059671 /
      3360000000000000000000000000000000000000000000000000 : Rat) / a ^ 8 +
    (32282924952085988599562168216486673954473614047437 /
      1260000000000000000000000000000000000000000000000000000000 : Rat) / a ^ 9 +
    (-6437059323731048778112474761681198440303028795151024937 /
      3150000000000000000000000000000000000000000000000000000000000000 : Rat) / a ^ 10,
  (37499 / 2000000 : Rat) / a ^ 2 +
    (-90756184997 / 4000000000000 : Rat) / a ^ 3 +
    (101911356842812489 / 12000000000000000000 : Rat) / a ^ 4 +
    (-2330819551141274348399 / 960000000000000000000000 : Rat) / a ^ 5 +
    (74313033489739061014157362363 /
      120000000000000000000000000000000 : Rat) / a ^ 6 +
    (-3466127952728129262569135005461641 /
      40000000000000000000000000000000000000 : Rat) / a ^ 7 +
    (9505058521573556772778407341507928877171 /
      840000000000000000000000000000000000000000000 : Rat) / a ^ 8 +
    (-369334357588681924357524760214954573011419937 /
      280000000000000000000000000000000000000000000000000 : Rat) / a ^ 9 +
    (73201719551490856429506197406013080899620659722437 /
      630000000000000000000000000000000000000000000000000000000 : Rat) / a ^ 10,
  (-1 / 8 : Rat) / a ^ 2 +
    (1267501 / 8000000 : Rat) / a ^ 3 +
    (-1285388425001 / 16000000000000 : Rat) / a ^ 4 +
    (707130186426807499 / 24000000000000000000 : Rat) / a ^ 5 +
    (-885124137857500894389983 / 96000000000000000000000000 : Rat) / a ^ 6 +
    (121323943169885994960555112503 /
      80000000000000000000000000000000 : Rat) / a ^ 7 +
    (-109490507503332391374454105552645031 /
      480000000000000000000000000000000000000 : Rat) / a ^ 8 +
    (4218596051351794146286713936328728617507 /
      140000000000000000000000000000000000000000000 : Rat) / a ^ 9 +
    (-831374451055577936483703079637647667443420007 /
      280000000000000000000000000000000000000000000000000 : Rat) / a ^ 10,
  (-17 / 48 : Rat) / a ^ 3 +
    (15997549 / 48000000 : Rat) / a ^ 4 +
    (-1705831419019 / 9600000000000 : Rat) / a ^ 5 +
    (10508891223977467963 / 144000000000000000000 : Rat) / a ^ 6 +
    (-470722754526130143263441 / 32000000000000000000000000 : Rat) / a ^ 7 +
    (1258841061599192341341029663971 /
      480000000000000000000000000000000 : Rat) / a ^ 8 +
    (-48112056302871091629198051764915287 /
      120000000000000000000000000000000000000 : Rat) / a ^ 9 +
    (9430612009133983304407197312444218442787 /
      210000000000000000000000000000000000000000000 : Rat) / a ^ 10,
  (-197 / 384 : Rat) / a ^ 4 +
    (102352891 / 192000000 : Rat) / a ^ 5 +
    (-124428964696943 / 384000000000000 : Rat) / a ^ 6 +
    (5466992211100606261 / 64000000000000000000 : Rat) / a ^ 7 +
    (-14447308481391347983435751 /
      768000000000000000000000000 : Rat) / a ^ 8 +
    (547912243539444513848820888617 /
      160000000000000000000000000000000 : Rat) / a ^ 9 +
    (-106850233468650927259222569691316117 /
      240000000000000000000000000000000000000 : Rat) / a ^ 10,
  (-1223 / 1920 : Rat) / a ^ 5 +
    (1469818603 / 1920000000 : Rat) / a ^ 6 +
    (-190093920678843 / 640000000000000 : Rat) / a ^ 7 +
    (165526756567240704451 / 1920000000000000000000 : Rat) / a ^ 8 +
    (-6231175950580603531353277 /
      320000000000000000000000000 : Rat) / a ^ 9 +
    (1209279407345197652827586065777 /
      400000000000000000000000000000000 : Rat) / a ^ 10,
  (-17327 / 23040 : Rat) / a ^ 6 +
    (733030909 / 1280000000 : Rat) / a ^ 7 +
    (-1893449796299159 / 7680000000000000 : Rat) / a ^ 8 +
    (70771692337520385983 / 960000000000000000000 : Rat) / a ^ 9 +
    (-13671476108950702739678483 /
      960000000000000000000000000 : Rat) / a ^ 10,
  (-1693 / 3584 : Rat) / a ^ 7 +
    (865045579 / 2150400000 : Rat) / a ^ 8 +
    (-160559669605079 / 896000000000000 : Rat) / a ^ 9 +
    (30881092704676280579 / 672000000000000000000 : Rat) / a ^ 10,
  (-246647 / 860160 : Rat) / a ^ 8 +
    (9095694149 / 35840000000 : Rat) / a ^ 9 +
    (-1742161635091649 / 17920000000000000 : Rat) / a ^ 10,
  (-102937 / 645120 : Rat) / a ^ 9 +
    (19638665437 / 161280000000 : Rat) / a ^ 10,
  (-221183 / 3225600 : Rat) / a ^ 10
]

private def ratAreaIntegral (i : Nat) : Rat :=
  ∑ n : Fin 11,
    ratAreaCoeff (ratLower i) n *
      (ratUpper i ^ ((n : Nat) + 1) - ratLower i ^ ((n : Nat) + 1)) /
        ((n : Nat) + 1 : Nat)

private def ratRowTerm (i : Nat) : Rat :=
  ratFactor i * ratAreaIntegral i

private def realAreaPoly (a : Rat) (d : Real) : Real :=
  ∑ n : Fin 11, (ratAreaCoeff a n : Real) * d ^ (n : Nat)

private theorem d869_area_eq_realAreaPoly (a : Rat) (ha : a ≠ 0) (d : Real) :
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
        (a : Real) d =
      realAreaPoly a d := by
  have haR : (a : Real) ≠ 0 := by exact_mod_cast ha
  unfold PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
  rw [PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D830_p1Case1_upper_integral_eq_sum]
  unfold realAreaPoly
  simp [ratAreaCoeff, Fin.sum_univ_succ, Finset.sum_range_succ,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D814Q4Primitive,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D828QCoeff,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807L,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807H,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807A,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Beta,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Square,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Delta,
    PrimesRestrictedDigits.sectionSixThetaOne,
    PrimesRestrictedDigits.sectionSixThetaTwo,
    Nat.choose]
  field_simp [haR]
  ring

private abbrev RowLower (i : Fin 256) : Real :=
  PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D849RowLower i

private abbrev RowUpper (i : Fin 256) : Real :=
  PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D849RowUpper i

private abbrev RowFactor (i : Fin 256) : Real :=
  PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D853P1RowFactor i

private abbrev Area (i : Fin 256) (d : Real) : Real :=
  PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D830P1Case1Area
    (RowLower i) d

private abbrev RowFiber (i : Fin 256) (d : Real) : Real :=
  PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D852P1RowFiber i d

private theorem realAreaPoly_integral_eq_cast (a lo hi : Rat) :
    (∫ d in (lo : Real)..(hi : Real), realAreaPoly a d) =
      ((∑ n : Fin 11,
        ratAreaCoeff a n *
          (hi ^ ((n : Nat) + 1) - lo ^ ((n : Nat) + 1)) /
            ((n : Nat) + 1 : Nat) : Rat) : Real) := by
  unfold realAreaPoly
  rw [intervalIntegral.integral_finsetSum]
  · rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    ring
  · intro n hn
    exact (continuous_const.mul (continuous_id.pow (n : Nat))).intervalIntegrable _ _

private theorem rowLower_eq_cast (i : Fin 256) :
    RowLower i = (ratLower i.1 : Real) := by
  simp only [RowLower, ratLower, ratDs, ratDr,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D849RowLower]
  norm_num [PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Ds,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Dr,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807A,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Beta,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Square,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Delta,
    PrimesRestrictedDigits.sectionSixThetaOne,
    PrimesRestrictedDigits.sectionSixThetaTwo]

private theorem rowUpper_eq_cast (i : Fin 256) :
    RowUpper i = (ratUpper i.1 : Real) := by
  simp only [RowUpper, ratUpper, ratDs, ratDr,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D849RowUpper]
  norm_num [PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Ds,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Dr,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807A,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Beta,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Square,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Delta,
    PrimesRestrictedDigits.sectionSixThetaOne,
    PrimesRestrictedDigits.sectionSixThetaTwo]

private theorem ratLower_ne_zero (i : Fin 256) : ratLower i.1 ≠ 0 := by
  have hi : (0 : Rat) ≤ i.1 := by positivity
  unfold ratLower ratDs ratDr
  norm_num
  positivity

private theorem rowFactor_eq_cast (i : Fin 256) :
    RowFactor i = (ratFactor i.1 : Real) := by
  simp only [RowFactor, ratFactor, ratUpper, ratDs, ratDr, ratBeta, ratGap,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D853P1RowFactor,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D849RowUpper]
  norm_num [PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Ds,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Dr,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807A,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Beta,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Square,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Delta,
    PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D807Gap,
    PrimesRestrictedDigits.sectionSixThetaOne,
    PrimesRestrictedDigits.sectionSixThetaTwo]

private theorem rowAreaIntegral_eq_cast (i : Fin 256) :
    (∫ d in RowLower i..RowUpper i, Area i d) =
      (ratAreaIntegral i.1 : Real) := by
  unfold Area
  rw [rowLower_eq_cast, rowUpper_eq_cast]
  rw [intervalIntegral.integral_congr (fun d hd =>
    d869_area_eq_realAreaPoly (ratLower i.1) (ratLower_ne_zero i) d)]
  exact realAreaPoly_integral_eq_cast (ratLower i.1) (ratLower i.1) (ratUpper i.1)

private def realRowTerm (i : Fin 256) : Real :=
  RowFactor i * (∫ d in RowLower i..RowUpper i, Area i d)

private theorem realRowTerm_eq_cast (i : Fin 256) :
    realRowTerm i = (ratRowTerm i.1 : Real) := by
  rw [realRowTerm, rowFactor_eq_cast, rowAreaIntegral_eq_cast]
  unfold ratRowTerm
  norm_num

private theorem ratRowSum_lt_exactCap :
    (Finset.sum (Finset.range 256) ratRowTerm) <
      (68741 / 25000000 : Rat) := by
  norm_num [ratRowTerm, ratAreaIntegral, ratAreaCoeff, ratFactor,
    ratLower, ratUpper, ratDs, ratDr, ratBeta, ratGap,
    Fin.sum_univ_succ, Finset.sum_range_succ]

private theorem realRowSum_eq_cast :
    (∑ i : Fin 256, realRowTerm i) =
      ((Finset.sum (Finset.range 256) ratRowTerm : Rat) : Real) := by
  calc
    (∑ i : Fin 256, realRowTerm i) =
        ∑ i : Fin 256, (ratRowTerm i.1 : Real) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact realRowTerm_eq_cast i
    _ = ((∑ i : Fin 256, ratRowTerm i.1 : Rat) : Real) := by
      symm
      exact Rat.cast_sum (Finset.univ : Finset (Fin 256))
        (fun i : Fin 256 => ratRowTerm i.1)
    _ = ((Finset.sum (Finset.range 256) ratRowTerm : Rat) : Real) := by
      congr 1

private theorem realRowSum_lt_exactCap :
    (∑ i : Fin 256, realRowTerm i) < (68741 / 25000000 : Real) := by
  rw [realRowSum_eq_cast]
  calc
    ((Finset.sum (Finset.range 256) ratRowTerm : Rat) : Real) <
        ((68741 / 25000000 : Rat) : Real) :=
      (Rat.cast_lt (K := Real)).mpr ratRowSum_lt_exactCap
    _ = (68741 / 25000000 : Real) := by norm_num

private theorem rowFiberIntegral_le_realRowTerm (i : Fin 256) :
    (∫ d in RowLower i..RowUpper i, RowFiber i d) ≤
      realRowTerm i := by
  calc
    (∫ d in RowLower i..RowUpper i, RowFiber i d) ≤
        ∫ d in RowLower i..RowUpper i, RowFactor i * Area i d := by
      exact
        PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D853_p1Row_integral_le_scaled_area
          i (PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D854_p1Row_area_intervalIntegrable i)
    _ = realRowTerm i := by
      rw [intervalIntegral.integral_const_mul]
      rfl

private theorem d869_p1RowFiber_sum_lt_exactCap :
    (∑ i : Fin 256,
      ∫ d in
        PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D849RowLower i..
        PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D849RowUpper i,
        PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D852P1RowFiber i d) <
      (68741 / 25000000 : Real) := by
  calc
    (∑ i : Fin 256, ∫ d in RowLower i..RowUpper i, RowFiber i d) ≤
        ∑ i : Fin 256, realRowTerm i := by
      apply Finset.sum_le_sum
      intro i hi
      exact rowFiberIntegral_le_realRowTerm i
    _ < (68741 / 25000000 : Real) := realRowSum_lt_exactCap

theorem sectionSixFirstLowCentralSmallI5P1D869_p1RowFiber_sum_lt :
    (∑ i : Fin 256,
      ∫ d in
        PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D849RowLower i..
        PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D849RowUpper i,
        PrimesRestrictedDigits.sectionSixFirstLowCentralSmallI5P1D852P1RowFiber i d) <
      (11 / 4000 : Real) := by
  exact lt_trans d869_p1RowFiber_sum_lt_exactCap (by norm_num)

end
end PrimesRestrictedDigits
