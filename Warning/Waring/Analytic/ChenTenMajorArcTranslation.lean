import Waring.Analytic.ChenTenArcs
import Waring.Analytic.ChenTenMajorArcPointwise
import Waring.Analytic.ChenTenSingularCoefficient
import Mathlib.Algebra.Ring.GeomSum

/-!
# Translation and model separation on a Chen major arc

This file translates one closed major arc to its centered coordinate and
separates Chen's modeled representation integrand into its arithmetic and
continuous factors [CHEN1964-EN, pp. 1561-1562, equations (27)-(29);
CHEN1964-ZH, p. 728, equations (24)-(25)].
-/

namespace Waring.Analytic

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

namespace ChenTenArcIndex

/-- The positive denominator carried by an arc index supplies the `NeZero`
value required by `ZMod` character and singular-term APIs. -/
instance instNeZeroDenominator {P : Nat} (i : ChenTenArcIndex P) :
    NeZero i.denominator :=
  ⟨i.denominator_pos.ne'⟩

/-- A reduced arc numerator is a unit modulo its denominator. -/
theorem numerator_isUnit {P : Nat} (i : ChenTenArcIndex P) :
    IsUnit (i.numerator : ZMod i.denominator) := by
  exact (ZMod.isUnit_iff_coprime i.numerator i.denominator).2 i.coprime

end ChenTenArcIndex

/-- The rational center belonging to a reduced major-arc index. -/
def chenTenMajorArcCenter {P : Nat} (i : ChenTenArcIndex P) : Real :=
  rationalCenter i.numerator i.denominator

/-- The radius `1/(q*10*P^4)` belonging to an indexed major arc. -/
def chenTenMajorArcRadius (P : Nat) (i : ChenTenArcIndex P) : Real :=
  1 / ((i.denominator : Real) * chenTenArcScale P)

/-- The radius of an indexed major arc is positive when `P` is positive. -/
theorem chenTenMajorArcRadius_pos {P : Nat} (hP : 0 < P)
    (i : ChenTenArcIndex P) :
    0 < chenTenMajorArcRadius P i := by
  unfold chenTenMajorArcRadius
  have hq : (0 : Real) < i.denominator := by
    exact_mod_cast i.denominator_pos
  have htau := chenTenArcScale_pos hP
  positivity

/-- The target additive phase in the representation integral. -/
def chenTenTargetPhase (N : Nat) (alpha : Real) : Complex :=
  Complex.exp
    (-2 * Real.pi * Complex.I * (alpha * (N : Real)))

/-- The continuous factor remaining after the major-arc model is separated. -/
def chenTenSingularIntegralKernel (P N : Nat) (z : Real) : Complex :=
  fifthPerturbationIntegral z P ^ 15 * chenTenTargetPhase N z

/-- Chen's approximating Weyl-sum model on one indexed major arc. -/
def chenTenMajorArcWeylModel
    (P : Nat) (i : ChenTenArcIndex P) (z : Real) : Complex :=
  (i.denominator : Complex)⁻¹ *
    completePowerSum 5 (i.numerator : ZMod i.denominator) *
      fifthPerturbationIntegral z P

/-- The representation integrand built from the major-arc Weyl model. -/
def chenTenMajorArcModelIntegrand
    (P N : Nat) (i : ChenTenArcIndex P) (z : Real) : Complex :=
  chenTenMajorArcWeylModel P i z ^ 15 *
    chenTenTargetPhase N (chenTenMajorArcCenter i + z)

/-- The singular-series term belonging to one reduced arc index. -/
def chenTenIndexedSingularTerm
    (N : Nat) {P : Nat} (i : ChenTenArcIndex P) : Complex :=
  chenTenSingularTerm i.denominator N
    (i.numerator : ZMod i.denominator)

/-- The centered, denominator-dependent truncation of the singular integral. -/
def chenTenTruncatedSingularIntegral
    (P N : Nat) (i : ChenTenArcIndex P) : Complex :=
  ∫ z in -chenTenMajorArcRadius P i..chenTenMajorArcRadius P i,
    chenTenSingularIntegralKernel P N z

/-- The geometric-sum factor in a difference of fifteenth powers. -/
def fifteenthPowerDifferenceFactor (X Y : Complex) : Complex :=
  ∑ k ∈ Finset.range 15, X ^ k * Y ^ (14 - k)

/-- A closed center-radius set integral is the centered translated interval
integral. -/
theorem setIntegral_centeredClosedInterval_eq_intervalIntegral_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f : Real → E) (center radius : Real) (hradius : 0 ≤ radius) :
    (∫ alpha in centeredClosedInterval center radius, f alpha) =
      ∫ z in -radius..radius, f (center + z) := by
  unfold centeredClosedInterval
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith : center - radius ≤ center + radius)]
  symm
  simpa only [sub_eq_add_neg] using
    (intervalIntegral.integral_comp_add_left f center :
      (∫ z in -radius..radius, f (center + z)) =
        ∫ alpha in center + -radius..center + radius, f alpha)

/-- The set integral over one Chen major arc is its interval integral in the
centered coordinate `alpha=center+z`. -/
theorem setIntegral_chenTenArc_eq_intervalIntegral_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {P : Nat} (hP : 0 < P) (i : ChenTenArcIndex P) (f : Real → E) :
    (∫ alpha in chenTenArc P i, f alpha) =
      ∫ z in -chenTenMajorArcRadius P i..chenTenMajorArcRadius P i,
        f (chenTenMajorArcCenter i + z) := by
  change
    (∫ alpha in centeredClosedInterval
        (chenTenMajorArcCenter i) (chenTenMajorArcRadius P i), f alpha) = _
  exact setIntegral_centeredClosedInterval_eq_intervalIntegral_add
    f _ _ (chenTenMajorArcRadius_pos hP i).le

/-- Translating by the rational center identifies arc membership with the
centered closed radius interval. -/
theorem add_mem_chenTenArc_iff_mem_Icc
    {P : Nat} (i : ChenTenArcIndex P) (z : Real) :
    chenTenMajorArcCenter i + z ∈ chenTenArc P i ↔
      z ∈ Set.Icc (-chenTenMajorArcRadius P i)
        (chenTenMajorArcRadius P i) := by
  change
    chenTenMajorArcCenter i + z ∈
        Set.Icc
          (chenTenMajorArcCenter i - chenTenMajorArcRadius P i)
          (chenTenMajorArcCenter i + chenTenMajorArcRadius P i) ↔ _
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> linarith

/-- The centered arc condition is equivalently the usual absolute-value
bound on `z`. -/
theorem add_mem_chenTenArc_iff_abs_le
    {P : Nat} (i : ChenTenArcIndex P) (z : Real) :
    chenTenMajorArcCenter i + z ∈ chenTenArc P i ↔
      |z| ≤ chenTenMajorArcRadius P i := by
  rw [add_mem_chenTenArc_iff_mem_Icc]
  exact abs_le.symm

/-- Chen's target phase has norm one. -/
@[simp]
theorem norm_chenTenTargetPhase (N : Nat) (alpha : Real) :
    ‖chenTenTargetPhase N alpha‖ = 1 := by
  unfold chenTenTargetPhase
  rw [show
    -2 * Real.pi * Complex.I * (alpha * (N : Real)) =
      Complex.I * (((-2 * Real.pi * alpha * N : Real) : Complex)) by
        push_cast
        ring]
  exact Complex.norm_exp_I_mul_ofReal _

/-- The target phase splits under addition of real frequencies. -/
theorem chenTenTargetPhase_add (N : Nat) (x y : Real) :
    chenTenTargetPhase N (x + y) =
      chenTenTargetPhase N x * chenTenTargetPhase N y := by
  unfold chenTenTargetPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- At a rational center, the target phase is the negative standard additive
character appearing in Chen's singular term. -/
theorem chenTenTargetPhase_nat_div
    (q : Nat) [NeZero q] (a N : Nat) :
    chenTenTargetPhase N ((a : Real) / q) =
      ZMod.stdAddChar (-(a : ZMod q) * (N : ZMod q)) := by
  unfold chenTenTargetPhase
  push_cast
  have hargument :
      -(a : ZMod q) * (N : ZMod q) =
        ((-((a * N : Nat) : Int)) : ZMod q) := by
    push_cast
    ring
  calc
    Complex.exp (-2 * Real.pi * Complex.I *
        ((((a : Real) / q) * (N : Real)) : Complex)) =
        Complex.exp
          (2 * Real.pi * Complex.I *
            ((-((a * N : Nat) : Int) : Int) : Complex) /
              (q : Complex)) := by
      congr 1
      push_cast
      rw [div_eq_mul_inv]
      ring
    _ = ZMod.stdAddChar
        (((-((a * N : Nat) : Int)) : Int) : ZMod q) := by
      rw [ZMod.stdAddChar_coe]
    _ = ZMod.stdAddChar (-(a : ZMod q) * (N : ZMod q)) := by
      rw [hargument]
      congr 1
      push_cast
      rfl

/-- The radius notation here is definitionally the source pointwise radius
`1/(10*q*P^4)`, up to commutative ring normalization. -/
theorem chenTenMajorArcRadius_eq_pointwiseRadius
    (P : Nat) (i : ChenTenArcIndex P) :
    chenTenMajorArcRadius P i =
      1 / (10 * (i.denominator : Real) * (P : Real) ^ 4) := by
  unfold chenTenMajorArcRadius chenTenArcScale
  congr 1
  ring

/-- The checked `6*q` pointwise approximation, stated directly in the
centered coordinate of an indexed major arc. -/
theorem norm_fifthPowerExponentialSum_sub_chenTenMajorArcWeylModel_le
    {P : Nat} (hP : 0 < P) (i : ChenTenArcIndex P) (z : Real)
    (hz : z ∈ Set.Icc (-chenTenMajorArcRadius P i)
      (chenTenMajorArcRadius P i)) :
    ‖fifthPowerExponentialSum P
        (chenTenMajorArcCenter i + z) -
      chenTenMajorArcWeylModel P i z‖ ≤
      6 * (i.denominator : Real) := by
  have hzAbs : |z| ≤ chenTenMajorArcRadius P i := by
    exact abs_le.mpr hz
  have hzPointwise :
      |z| ≤ 1 / (10 * (i.denominator : Real) * (P : Real) ^ 4) := by
    rw [← chenTenMajorArcRadius_eq_pointwiseRadius P i]
    exact hzAbs
  have hbound := norm_fifthPowerExponentialSum_sub_majorTerm_le
    i.denominator i.numerator z P hP hzPointwise
  simpa [chenTenMajorArcCenter, rationalCenter,
    chenTenMajorArcWeylModel] using hbound

/-- The modeled representation integrand separates into Chen's arithmetic
singular term and the centered continuous kernel. -/
theorem chenTenMajorArcModelIntegrand_eq_singularTerm_mul_kernel
    (P N : Nat) (i : ChenTenArcIndex P) (z : Real) :
    chenTenMajorArcModelIntegrand P N i z =
      chenTenIndexedSingularTerm N i *
        chenTenSingularIntegralKernel P N z := by
  have hcenter :
      chenTenTargetPhase N (chenTenMajorArcCenter i) =
        ZMod.stdAddChar (-(i.numerator : ZMod i.denominator) *
          (N : ZMod i.denominator)) := by
    simpa [chenTenMajorArcCenter, rationalCenter] using
      chenTenTargetPhase_nat_div i.denominator i.numerator N
  unfold chenTenMajorArcModelIntegrand chenTenIndexedSingularTerm
    chenTenSingularIntegralKernel
  rw [chenTenTargetPhase_add, hcenter]
  unfold chenTenMajorArcWeylModel chenTenSingularTerm
  simp only [div_eq_mul_inv]
  ring

/-- Integrating the separated model over the centered arc factors out its
arithmetic singular term. -/
theorem intervalIntegral_chenTenMajorArcModelIntegrand_eq_singularTerm_mul_truncated
    (P N : Nat) (i : ChenTenArcIndex P) :
    (∫ z in -chenTenMajorArcRadius P i..chenTenMajorArcRadius P i,
        chenTenMajorArcModelIntegrand P N i z) =
      chenTenIndexedSingularTerm N i *
        chenTenTruncatedSingularIntegral P N i := by
  simp_rw [chenTenMajorArcModelIntegrand_eq_singularTerm_mul_kernel]
  rw [intervalIntegral.integral_const_mul]
  rfl

/-- The finite sum of centered modeled arc integrals has the corresponding
finite sum of separated singular terms. -/
theorem sum_intervalIntegral_chenTenMajorArcModelIntegrand_eq
    (P N : Nat) :
    (∑ i : ChenTenArcIndex P,
      ∫ z in -chenTenMajorArcRadius P i..chenTenMajorArcRadius P i,
        chenTenMajorArcModelIntegrand P N i z) =
      ∑ i : ChenTenArcIndex P,
        chenTenIndexedSingularTerm N i *
          chenTenTruncatedSingularIntegral P N i := by
  apply Finset.sum_congr rfl
  intro i _
  exact intervalIntegral_chenTenMajorArcModelIntegrand_eq_singularTerm_mul_truncated
    P N i

/-- The fifteenth-power difference has the exact finite geometric-sum
factorization used by the later error estimate. -/
theorem fifteenthPower_sub_eq_mul_differenceFactor (X Y : Complex) :
    X ^ 15 - Y ^ 15 =
      (X - Y) * fifteenthPowerDifferenceFactor X Y := by
  unfold fifteenthPowerDifferenceFactor
  simpa only [Nat.reduceSubDiff] using
    ((Commute.all X Y).mul_geom_sum₂ 15).symm

/-- The actual translated representation integrand differs from its model by
the Weyl-sum error times the finite power factor and the unit target phase. -/
theorem chenTenRepresentationIntegrand_sub_modelIntegrand_eq
    (P N : Nat) (i : ChenTenArcIndex P) (z : Real) :
    chenTenRepresentationIntegrand P N
        (chenTenMajorArcCenter i + z) -
      chenTenMajorArcModelIntegrand P N i z =
      (fifthPowerExponentialSum P
          (chenTenMajorArcCenter i + z) -
        chenTenMajorArcWeylModel P i z) *
        fifteenthPowerDifferenceFactor
          (fifthPowerExponentialSum P
            (chenTenMajorArcCenter i + z))
          (chenTenMajorArcWeylModel P i z) *
        chenTenTargetPhase N (chenTenMajorArcCenter i + z) := by
  change
    fifthPowerExponentialSum P (chenTenMajorArcCenter i + z) ^ 15 *
          chenTenTargetPhase N (chenTenMajorArcCenter i + z) -
        chenTenMajorArcWeylModel P i z ^ 15 *
          chenTenTargetPhase N (chenTenMajorArcCenter i + z) = _
  calc
    _ = (fifthPowerExponentialSum P
          (chenTenMajorArcCenter i + z) ^ 15 -
        chenTenMajorArcWeylModel P i z ^ 15) *
        chenTenTargetPhase N (chenTenMajorArcCenter i + z) := by ring
    _ = _ := by
      rw [fifteenthPower_sub_eq_mul_differenceFactor]

/-- Taking norms removes the unit target phase from the exact translated
integrand error. -/
theorem norm_chenTenRepresentationIntegrand_sub_modelIntegrand_eq
    (P N : Nat) (i : ChenTenArcIndex P) (z : Real) :
    ‖chenTenRepresentationIntegrand P N
          (chenTenMajorArcCenter i + z) -
        chenTenMajorArcModelIntegrand P N i z‖ =
      ‖fifthPowerExponentialSum P
          (chenTenMajorArcCenter i + z) -
        chenTenMajorArcWeylModel P i z‖ *
        ‖fifteenthPowerDifferenceFactor
          (fifthPowerExponentialSum P
            (chenTenMajorArcCenter i + z))
          (chenTenMajorArcWeylModel P i z)‖ := by
  rw [chenTenRepresentationIntegrand_sub_modelIntegrand_eq,
    norm_mul, norm_mul, norm_chenTenTargetPhase, mul_one]

/-- On a centered Chen--Ten arc, the existing `6q` Weyl-sum approximation
gives the corresponding multiplicative bound for the full integrand error. -/
theorem norm_chenTenRepresentationIntegrand_sub_modelIntegrand_le
    {P : Nat} (hP : 1 ≤ P) (N : Nat) (i : ChenTenArcIndex P) (z : Real)
    (hz : z ∈ Set.Icc (-chenTenMajorArcRadius P i)
      (chenTenMajorArcRadius P i)) :
    ‖chenTenRepresentationIntegrand P N
          (chenTenMajorArcCenter i + z) -
        chenTenMajorArcModelIntegrand P N i z‖ ≤
      (6 * (i.denominator : Real)) *
        ‖fifteenthPowerDifferenceFactor
          (fifthPowerExponentialSum P
            (chenTenMajorArcCenter i + z))
          (chenTenMajorArcWeylModel P i z)‖ := by
  rw [norm_chenTenRepresentationIntegrand_sub_modelIntegrand_eq]
  exact mul_le_mul_of_nonneg_right
    (norm_fifthPowerExponentialSum_sub_chenTenMajorArcWeylModel_le
      hP i z hz)
    (norm_nonneg _)

end

end Waring.Analytic
