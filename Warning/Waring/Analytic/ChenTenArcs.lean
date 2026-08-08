import Waring.Analytic.ChenTenArcGeometry
import Waring.Analytic.ChenTenRepresentation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Reduced major arcs in Chen's Lemma 10

This file constructs Chen's finite reduced major-arc family, proves its arcs
pairwise disjoint, places them inside the translated length-one fundamental
interval, and gives the corresponding exact integral split
[CHEN1964-EN, p. 1561; CHEN1964-ZH, p. 728].
-/

namespace Waring.Analytic

open Function MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

/-- Reduced numerator-denominator pairs under Chen's squared denominator
cutoff.  The ambient product of finite types makes the index finite. -/
def ChenTenArcIndex (P : Nat) :=
  {aq : Fin (P + 1) × Fin (P + 1) //
    0 < aq.2.val ∧ aq.1.val < aq.2.val ∧
      Nat.Coprime aq.1.val aq.2.val ∧ aq.2.val ^ 2 ≤ P}

/-- The finite reduced-arc index type has a finite enumeration. -/
instance (P : Nat) : Fintype (ChenTenArcIndex P) := by
  dsimp [ChenTenArcIndex]
  infer_instance

/-- Equality of reduced-arc indices is decidable. -/
instance (P : Nat) : DecidableEq (ChenTenArcIndex P) := by
  dsimp [ChenTenArcIndex]
  infer_instance

namespace ChenTenArcIndex

/-- The numerator of a reduced major-arc index. -/
def numerator {P : Nat} (i : ChenTenArcIndex P) : Nat :=
  i.1.1.val

/-- The denominator of a reduced major-arc index. -/
def denominator {P : Nat} (i : ChenTenArcIndex P) : Nat :=
  i.1.2.val

/-- An indexed denominator is positive. -/
theorem denominator_pos {P : Nat} (i : ChenTenArcIndex P) :
    0 < i.denominator :=
  i.property.1

/-- The chosen numerator is the canonical representative below its
denominator. -/
theorem numerator_lt_denominator {P : Nat} (i : ChenTenArcIndex P) :
    i.numerator < i.denominator :=
  i.property.2.1

/-- The numerator and denominator of an index are coprime. -/
theorem coprime {P : Nat} (i : ChenTenArcIndex P) :
    Nat.Coprime i.numerator i.denominator :=
  i.property.2.2.1

/-- The denominator obeys Chen's squared cutoff in the natural numbers. -/
theorem denominator_sq_le {P : Nat} (i : ChenTenArcIndex P) :
    i.denominator ^ 2 ≤ P :=
  i.property.2.2.2

/-- Equality of numerator and denominator determines an arc index. -/
@[ext]
theorem ext {P : Nat} {i j : ChenTenArcIndex P}
    (ha : i.numerator = j.numerator)
    (hq : i.denominator = j.denominator) : i = j := by
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact ha
  · apply Fin.ext
    exact hq

/-- Distinct reduced indices have unequal rational cross-products. -/
theorem crossProduct_ne_of_ne {P : Nat} (i j : ChenTenArcIndex P)
    (hij : i ≠ j) :
    i.numerator * j.denominator ≠ j.numerator * i.denominator := by
  intro hcross
  have hqDvdR : i.denominator ∣ j.denominator := by
    apply i.coprime.symm.dvd_mul_right.mp
    refine ⟨j.numerator, ?_⟩
    calc
      j.denominator * i.numerator = i.numerator * j.denominator :=
        Nat.mul_comm _ _
      _ = j.numerator * i.denominator := hcross
      _ = i.denominator * j.numerator := Nat.mul_comm _ _
  have hrDvdQ : j.denominator ∣ i.denominator := by
    apply j.coprime.symm.dvd_mul_right.mp
    refine ⟨i.numerator, ?_⟩
    calc
      i.denominator * j.numerator = j.numerator * i.denominator :=
        Nat.mul_comm _ _
      _ = i.numerator * j.denominator := hcross.symm
      _ = j.denominator * i.numerator := Nat.mul_comm _ _
  have hdenominator : i.denominator = j.denominator :=
    Nat.dvd_antisymm hqDvdR hrDvdQ
  have hnumerator : i.numerator = j.numerator := by
    apply Nat.eq_of_mul_eq_mul_right j.denominator_pos
    simpa [hdenominator] using hcross
  exact hij (ext hnumerator hdenominator)

/-- The natural squared cutoff, cast to the real form used by the arc geometry
module. -/
theorem denominator_sq_le_real {P : Nat} (i : ChenTenArcIndex P) :
    (i.denominator : Real) ^ 2 ≤ P := by
  exact_mod_cast i.denominator_sq_le

end ChenTenArcIndex

/-- Chen's common major-arc scale `10*P^4`. -/
def chenTenArcScale (P : Nat) : Real :=
  10 * (P : Real) ^ 4

/-- The closed major arc indexed by a reduced pair. -/
def chenTenArc (P : Nat) (i : ChenTenArcIndex P) : Set Real :=
  rationalArc i.numerator i.denominator
    (1 / ((i.denominator : Real) * chenTenArcScale P))

/-- The scale `10*P^4` is positive for positive `P`. -/
theorem chenTenArcScale_pos {P : Nat} (hP : 0 < P) :
    0 < chenTenArcScale P := by
  have hPReal : (0 : Real) < P := by exact_mod_cast hP
  unfold chenTenArcScale
  positivity

/-- The closed major arcs attached to distinct reduced indices are disjoint. -/
theorem chenTenArc_pairwise_disjoint {P : Nat} (hP : 0 < P) :
    Pairwise (Disjoint on chenTenArc P) := by
  intro i j hij
  change Disjoint (chenTenArc P i) (chenTenArc P j)
  simpa [chenTenArc, chenTenArcScale] using
    disjoint_chenTenRationalArcs_of_sq_le P
      i.numerator j.numerator i.denominator j.denominator
      hP i.denominator_pos j.denominator_pos
      i.denominator_sq_le_real j.denominator_sq_le_real
      (ChenTenArcIndex.crossProduct_ne_of_ne i j hij)

/-- The left endpoint of Chen's translated unit interval. -/
def chenTenArcLeftEndpoint (P : Nat) : Real :=
  -(chenTenArcScale P)⁻¹

/-- The right endpoint of Chen's translated unit interval. -/
def chenTenArcRightEndpoint (P : Nat) : Real :=
  1 - (chenTenArcScale P)⁻¹

/-- The half-open real representative of Chen's translated length-one
fundamental interval. -/
def chenTenArcFundamentalInterval (P : Nat) : Set Real :=
  Set.Ico (chenTenArcLeftEndpoint P) (chenTenArcRightEndpoint P)

/-- The union of all reduced major arcs. -/
def chenTenMajorArcs (P : Nat) : Set Real :=
  ⋃ i : ChenTenArcIndex P, chenTenArc P i

/-- The part of the translated fundamental interval outside the major arcs. -/
def chenTenMinorArcs (P : Nat) : Set Real :=
  chenTenArcFundamentalInterval P \ chenTenMajorArcs P

/-- The integrand whose unit-interval integral counts Chen's bounded
15-variable representations. -/
def chenTenRepresentationIntegrand (P N : Nat) (alpha : Real) : Complex :=
  fifthPowerExponentialSum P alpha ^ 15 *
    Complex.exp (-2 * Real.pi * Complex.I * (alpha * (N : Real)))

/-- The translated fundamental interval has endpoint difference one. -/
theorem chenTenArcFundamentalInterval_length (P : Nat) :
    chenTenArcRightEndpoint P - chenTenArcLeftEndpoint P = 1 := by
  unfold chenTenArcRightEndpoint chenTenArcLeftEndpoint
  ring

/-- The endpoints of the translated fundamental interval are strictly
ordered. -/
theorem chenTenArcLeftEndpoint_lt_rightEndpoint (P : Nat) :
    chenTenArcLeftEndpoint P < chenTenArcRightEndpoint P := by
  rw [← sub_pos]
  rw [chenTenArcFundamentalInterval_length]
  norm_num

/-- The canonical reduced representative of the period-one endpoint is
`0/1`. -/
def chenTenZeroArcIndex (P : Nat) (hP : 0 < P) : ChenTenArcIndex P :=
  ⟨(⟨0, Nat.zero_lt_succ P⟩, ⟨1, Nat.succ_lt_succ hP⟩), by
    refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
    change 1 ^ 2 ≤ P
    omega⟩

/-- The canonical `0/1` arc starts exactly at the left endpoint of the
translated interval. -/
theorem chenTenZeroArc_eq (P : Nat) (hP : 0 < P) :
    chenTenArc P (chenTenZeroArcIndex P hP) =
      Set.Icc (chenTenArcLeftEndpoint P) (chenTenArcScale P)⁻¹ := by
  simp [chenTenArc, chenTenZeroArcIndex, ChenTenArcIndex.numerator,
    ChenTenArcIndex.denominator, rationalArc, rationalCenter,
    centeredClosedInterval, chenTenArcLeftEndpoint]

/-- Each indexed denominator plus one is still strictly below the common
major-arc scale. -/
theorem chenTenArcIndex_denominator_add_one_lt_scale {P : Nat}
    (hP : 0 < P) (i : ChenTenArcIndex P) :
    (i.denominator : Real) + 1 < chenTenArcScale P := by
  have hOneSq : ((1 : Nat) : Real) ^ 2 ≤ (P : Real) := by
    norm_num
    exact_mod_cast hP
  simpa [chenTenArcScale] using
    denominator_sum_lt_ten_mul_fourth_of_sq_le P i.denominator 1
      hP i.denominator_pos Nat.one_pos i.denominator_sq_le_real hOneSq

/-- Every indexed arc is contained in the half-open translated fundamental
interval; in particular, no arc wraps through its upper endpoint. -/
theorem chenTenArc_subset_fundamentalInterval_Ico {P : Nat} (hP : 0 < P)
    (i : ChenTenArcIndex P) :
    chenTenArc P i ⊆
      Set.Ico (chenTenArcLeftEndpoint P) (chenTenArcRightEndpoint P) := by
  have htau : 0 < chenTenArcScale P := chenTenArcScale_pos hP
  have hqReal : (0 : Real) < i.denominator := by
    exact_mod_cast i.denominator_pos
  have hqOne : (1 : Real) ≤ i.denominator := by
    exact_mod_cast i.denominator_pos
  have htauLe : chenTenArcScale P ≤
      (i.denominator : Real) * chenTenArcScale P := by
    calc
      chenTenArcScale P = 1 * chenTenArcScale P := by ring
      _ ≤ (i.denominator : Real) * chenTenArcScale P :=
        mul_le_mul_of_nonneg_right hqOne htau.le
  have hradiusLe :
      1 / ((i.denominator : Real) * chenTenArcScale P) ≤
        (chenTenArcScale P)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le htau htauLe
  have hcenterNonneg :
      0 ≤ (i.numerator : Real) / i.denominator :=
    div_nonneg (Nat.cast_nonneg _) hqReal.le
  have hlower :
      chenTenArcLeftEndpoint P ≤
        (i.numerator : Real) / i.denominator -
          1 / ((i.denominator : Real) * chenTenArcScale P) := by
    unfold chenTenArcLeftEndpoint
    linarith
  have haSucc : i.numerator + 1 ≤ i.denominator :=
    i.numerator_lt_denominator
  have haSuccReal : (i.numerator : Real) + 1 ≤ i.denominator := by
    exact_mod_cast haSucc
  have hcenterUnit :
      (i.numerator : Real) / i.denominator +
          1 / (i.denominator : Real) ≤ 1 := by
    calc
      (i.numerator : Real) / i.denominator +
          1 / (i.denominator : Real) =
          ((i.numerator : Real) + 1) / i.denominator := by ring
      _ ≤ 1 := (div_le_one hqReal).2 haSuccReal
  have hradii :
      1 / ((i.denominator : Real) * chenTenArcScale P) +
          (chenTenArcScale P)⁻¹ < 1 / (i.denominator : Real) := by
    have hwidth :
        (i.denominator : Real) + ((1 : Nat) : Real) <
          chenTenArcScale P := by
      simpa only [Nat.cast_one] using
        chenTenArcIndex_denominator_add_one_lt_scale hP i
    simpa only [Nat.cast_one, mul_one, one_mul, one_div] using
      reciprocal_arc_radii_add_lt_one_div_mul i.denominator 1
        (chenTenArcScale P) i.denominator_pos Nat.one_pos htau
        hwidth
  have hupper :
      (i.numerator : Real) / i.denominator +
          1 / ((i.denominator : Real) * chenTenArcScale P) <
        chenTenArcRightEndpoint P := by
    unfold chenTenArcRightEndpoint
    linarith
  intro x hx
  change x ∈ Set.Icc
    ((i.numerator : Real) / i.denominator -
      1 / ((i.denominator : Real) * chenTenArcScale P))
    ((i.numerator : Real) / i.denominator +
      1 / ((i.denominator : Real) * chenTenArcScale P)) at hx
  exact ⟨hlower.trans hx.1, hx.2.trans_lt hupper⟩

/-- Every indexed arc is contained in Chen's half-open translated fundamental
interval. -/
theorem chenTenArc_subset_fundamentalInterval {P : Nat} (hP : 0 < P)
    (i : ChenTenArcIndex P) :
    chenTenArc P i ⊆ chenTenArcFundamentalInterval P := by
  simpa only [chenTenArcFundamentalInterval] using
    chenTenArc_subset_fundamentalInterval_Ico hP i

/-- Every individual major arc is measurable. -/
theorem measurableSet_chenTenArc (P : Nat) (i : ChenTenArcIndex P) :
    MeasurableSet (chenTenArc P i) := by
  unfold chenTenArc rationalArc centeredClosedInterval
  exact measurableSet_Icc

/-- The finite union of major arcs is measurable. -/
theorem measurableSet_chenTenMajorArcs (P : Nat) :
    MeasurableSet (chenTenMajorArcs P) := by
  unfold chenTenMajorArcs
  exact MeasurableSet.iUnion fun i => measurableSet_chenTenArc P i

/-- The translated fundamental interval is measurable. -/
theorem measurableSet_chenTenArcFundamentalInterval (P : Nat) :
    MeasurableSet (chenTenArcFundamentalInterval P) := by
  unfold chenTenArcFundamentalInterval
  exact measurableSet_Ico

/-- The union of all major arcs stays in the translated fundamental
interval. -/
theorem chenTenMajorArcs_subset_fundamentalInterval {P : Nat} (hP : 0 < P) :
    chenTenMajorArcs P ⊆ chenTenArcFundamentalInterval P := by
  unfold chenTenMajorArcs
  exact Set.iUnion_subset fun i => chenTenArc_subset_fundamentalInterval hP i

/-- The minor-arc complement inside the fundamental interval is measurable. -/
theorem measurableSet_chenTenMinorArcs (P : Nat) :
    MeasurableSet (chenTenMinorArcs P) := by
  exact (measurableSet_chenTenArcFundamentalInterval P).diff
    (measurableSet_chenTenMajorArcs P)

/-- Major and minor arcs form the whole translated fundamental interval. -/
theorem chenTenMajorArcs_union_minorArcs {P : Nat} (hP : 0 < P) :
    chenTenMajorArcs P ∪ chenTenMinorArcs P =
      chenTenArcFundamentalInterval P := by
  rw [chenTenMinorArcs, Set.union_sdiff_self]
  exact Set.union_eq_right.mpr
    (chenTenMajorArcs_subset_fundamentalInterval hP)

/-- The major union and its relative minor-arc complement are disjoint. -/
theorem chenTenMajorArcs_disjoint_minorArcs (P : Nat) :
    Disjoint (chenTenMajorArcs P) (chenTenMinorArcs P) := by
  unfold chenTenMinorArcs
  exact Set.disjoint_sdiff_right

/-- The integral over the major union is the finite sum of the integrals over
its pairwise disjoint indexed arcs. -/
theorem setIntegral_chenTenMajorArcs_eq_sum {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    {P : Nat} (hP : 0 < P) (f : Real → E)
    (hf : IntegrableOn f (chenTenArcFundamentalInterval P)) :
    (∫ alpha in chenTenMajorArcs P, f alpha) =
      ∑ i : ChenTenArcIndex P, ∫ alpha in chenTenArc P i, f alpha := by
  unfold chenTenMajorArcs
  apply integral_iUnion_fintype
  · exact fun i => measurableSet_chenTenArc P i
  · exact chenTenArc_pairwise_disjoint hP
  · exact fun i => hf.mono_set (chenTenArc_subset_fundamentalInterval hP i)

/-- Exact major/minor decomposition of the set integral over Chen's
translated fundamental interval. -/
theorem sum_setIntegral_chenTenArc_add_minor_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    {P : Nat} (hP : 0 < P) (f : Real → E)
    (hf : IntegrableOn f (chenTenArcFundamentalInterval P)) :
    (∑ i : ChenTenArcIndex P, ∫ alpha in chenTenArc P i, f alpha) +
        (∫ alpha in chenTenMinorArcs P, f alpha) =
      ∫ alpha in chenTenArcFundamentalInterval P, f alpha := by
  rw [← setIntegral_chenTenMajorArcs_eq_sum hP f hf]
  simpa only [chenTenMinorArcs,
    Set.inter_eq_right.mpr (chenTenMajorArcs_subset_fundamentalInterval hP)]
    using integral_inter_add_sdiff (measurableSet_chenTenMajorArcs P) hf

/-- The interval integral over Chen's translated endpoints equals the set
integral over the canonical half-open fundamental interval. -/
theorem intervalIntegral_eq_setIntegral_chenTenArcFundamentalInterval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (P : Nat) (f : Real → E) :
    (∫ alpha in chenTenArcLeftEndpoint P..chenTenArcRightEndpoint P,
        f alpha) =
      ∫ alpha in chenTenArcFundamentalInterval P, f alpha := by
  rw [intervalIntegral.integral_of_le
    (chenTenArcLeftEndpoint_lt_rightEndpoint P).le]
  unfold chenTenArcFundamentalInterval
  exact integral_Ico_eq_integral_Ioc.symm

/-- Exact major/minor split of Chen's translated length-one interval
integral. -/
theorem intervalIntegral_eq_sum_chenTenArc_add_minor {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    {P : Nat} (hP : 0 < P) (f : Real → E)
    (hf : IntegrableOn f (chenTenArcFundamentalInterval P)) :
    (∫ alpha in chenTenArcLeftEndpoint P..chenTenArcRightEndpoint P,
        f alpha) =
      (∑ i : ChenTenArcIndex P, ∫ alpha in chenTenArc P i, f alpha) +
        ∫ alpha in chenTenMinorArcs P, f alpha := by
  rw [intervalIntegral_eq_setIntegral_chenTenArcFundamentalInterval]
  exact (sum_setIntegral_chenTenArc_add_minor_eq hP f hf).symm

/-- Chen's representation integrand is continuous. -/
theorem continuous_chenTenRepresentationIntegrand (P N : Nat) :
    Continuous (chenTenRepresentationIntegrand P N) := by
  unfold chenTenRepresentationIntegrand
  apply Continuous.mul
  · apply Continuous.pow
    unfold fifthPowerExponentialSum
    apply continuous_finsetSum
    intro x _hx
    unfold realFifthPowerExponential realFifthPowerPhase
    fun_prop
  · fun_prop

/-- Chen's representation integrand is integrable on the half-open
fundamental interval. -/
theorem integrableOn_chenTenRepresentationIntegrand (P N : Nat) :
    IntegrableOn (chenTenRepresentationIntegrand P N)
      (chenTenArcFundamentalInterval P) := by
  apply (continuous_chenTenRepresentationIntegrand P N).integrableOn_Icc.mono_set
  unfold chenTenArcFundamentalInterval
  exact Set.Ico_subset_Icc_self

/-- The bounded 15-variable representation count is exactly the sum of its
individual major-arc integrals and its minor-arc integral. -/
theorem positiveFifthPowerRepresentationCount_eq_majorArc_sum_add_minor
    (P N : Nat) (hP : 0 < P) :
    (positiveFifthPowerRepresentationCount 15 P N : Complex) =
      (∑ i : ChenTenArcIndex P,
        ∫ alpha in chenTenArc P i,
          chenTenRepresentationIntegrand P N alpha) +
        ∫ alpha in chenTenMinorArcs P,
          chenTenRepresentationIntegrand P N alpha := by
  rw [← integral_fifthPowerExponentialSum_pow_fifteen_eq_count
    P N (chenTenArcScale P)]
  simpa [chenTenArcLeftEndpoint, chenTenArcRightEndpoint,
    chenTenRepresentationIntegrand] using
    intervalIntegral_eq_sum_chenTenArc_add_minor hP
      (chenTenRepresentationIntegrand P N)
      (integrableOn_chenTenRepresentationIntegrand P N)

end

end Waring.Analytic
