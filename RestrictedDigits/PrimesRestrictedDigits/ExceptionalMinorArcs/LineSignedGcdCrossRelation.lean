import PrimesRestrictedDigits.ExceptionalMinorArcs.LineZeroCoefficientWitnesses
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Signed gcd normalization and the line cross relation

This implements the algebraic reduction following the definition of `N_2`
in `MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 211--212. The two relations are
cross-multiplied in `Int`; the defective normalized displays in the source are
not used.
-/

namespace PrimesRestrictedDigits

/-- The canonical signed primitive quotients of two first coefficients. -/
def linePrimitiveFirstCoefficients (x y : Int) : Int × Int :=
  (x / (Int.gcd x y : Int), y / (Int.gcd x y : Int))

/-- The sup height of the canonical signed primitive pair. -/
def linePrimitiveFirstCoefficientHeight (x y : Int) : Nat :=
  max (linePrimitiveFirstCoefficients x y).1.natAbs
    (linePrimitiveFirstCoefficients x y).2.natAbs

theorem linePrimitiveFirstCoefficients_fst_natAbs_le_height (x y : Int) :
    (linePrimitiveFirstCoefficients x y).1.natAbs <=
      linePrimitiveFirstCoefficientHeight x y :=
  le_max_left _ _

theorem linePrimitiveFirstCoefficients_snd_natAbs_le_height (x y : Int) :
    (linePrimitiveFirstCoefficients x y).2.natAbs <=
      linePrimitiveFirstCoefficientHeight x y :=
  le_max_right _ _

theorem linePrimitiveFirstCoefficients_fst_abs_le_height (x y : Int) :
    abs (((linePrimitiveFirstCoefficients x y).1 : Int) : Real) <=
      (linePrimitiveFirstCoefficientHeight x y : Real) := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  exact_mod_cast linePrimitiveFirstCoefficients_fst_natAbs_le_height x y

theorem linePrimitiveFirstCoefficients_snd_abs_le_height (x y : Int) :
    abs (((linePrimitiveFirstCoefficients x y).2 : Int) : Real) <=
      (linePrimitiveFirstCoefficientHeight x y : Real) := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  exact_mod_cast linePrimitiveFirstCoefficients_snd_natAbs_le_height x y

@[simp]
theorem linePrimitiveFirstCoefficients_fst (x y : Int) :
    (linePrimitiveFirstCoefficients x y).1 =
      x / (Int.gcd x y : Int) :=
  rfl

@[simp]
theorem linePrimitiveFirstCoefficients_snd (x y : Int) :
    (linePrimitiveFirstCoefficients x y).2 =
      y / (Int.gcd x y : Int) :=
  rfl

theorem linePrimitiveFirstCoefficients_gcd_pos
    {x y : Int} (hx : x ≠ 0) :
    0 < Int.gcd x y :=
  Int.gcd_pos_of_ne_zero_left y hx

/-- The positive gcd times the first signed quotient recovers the input. -/
theorem gcd_mul_linePrimitiveFirstCoefficients_fst (x y : Int) :
    (Int.gcd x y : Int) * (linePrimitiveFirstCoefficients x y).1 = x := by
  rw [linePrimitiveFirstCoefficients_fst, mul_comm]
  exact Int.ediv_mul_cancel (Int.gcd_dvd_left x y)

/-- The positive gcd times the second signed quotient recovers the input. -/
theorem gcd_mul_linePrimitiveFirstCoefficients_snd (x y : Int) :
    (Int.gcd x y : Int) * (linePrimitiveFirstCoefficients x y).2 = y := by
  rw [linePrimitiveFirstCoefficients_snd, mul_comm]
  exact Int.ediv_mul_cancel (Int.gcd_dvd_right x y)

theorem linePrimitiveFirstCoefficients_fst_ne_zero
    {x y : Int} (hx : x ≠ 0) :
    (linePrimitiveFirstCoefficients x y).1 ≠ 0 := by
  intro hzero
  apply hx
  rw [← gcd_mul_linePrimitiveFirstCoefficients_fst x y, hzero, mul_zero]

theorem linePrimitiveFirstCoefficients_snd_ne_zero
    {x y : Int} (hy : y ≠ 0) :
    (linePrimitiveFirstCoefficients x y).2 ≠ 0 := by
  intro hzero
  apply hy
  rw [← gcd_mul_linePrimitiveFirstCoefficients_snd x y, hzero, mul_zero]

/-- The canonical signed quotients are coprime when the first input is
nonzero. -/
theorem linePrimitiveFirstCoefficients_gcd_eq_one
    {x y : Int} (hx : x ≠ 0) :
    Int.gcd (linePrimitiveFirstCoefficients x y).1
      (linePrimitiveFirstCoefficients x y).2 = 1 := by
  exact Int.gcd_div_gcd_div_gcd
    (linePrimitiveFirstCoefficients_gcd_pos hx)

theorem gcd_mul_linePrimitiveFirstCoefficients_fst_natAbs (x y : Int) :
    Int.gcd x y * (linePrimitiveFirstCoefficients x y).1.natAbs =
      x.natAbs := by
  have h := congrArg Int.natAbs
    (gcd_mul_linePrimitiveFirstCoefficients_fst x y)
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using h

theorem gcd_mul_linePrimitiveFirstCoefficients_snd_natAbs (x y : Int) :
    Int.gcd x y * (linePrimitiveFirstCoefficients x y).2.natAbs =
      y.natAbs := by
  have h := congrArg Int.natAbs
    (gcd_mul_linePrimitiveFirstCoefficients_snd x y)
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using h

theorem linePrimitiveFirstCoefficients_fst_natAbs_le
    {x y : Int} (hx : x ≠ 0) :
    (linePrimitiveFirstCoefficients x y).1.natAbs <= x.natAbs := by
  calc
    (linePrimitiveFirstCoefficients x y).1.natAbs <=
        Int.gcd x y *
          (linePrimitiveFirstCoefficients x y).1.natAbs :=
      Nat.le_mul_of_pos_left _ (Int.gcd_pos_of_ne_zero_left y hx)
    _ = x.natAbs :=
      gcd_mul_linePrimitiveFirstCoefficients_fst_natAbs x y

theorem linePrimitiveFirstCoefficients_snd_natAbs_le
    {x y : Int} (hy : y ≠ 0) :
    (linePrimitiveFirstCoefficients x y).2.natAbs <= y.natAbs := by
  calc
    (linePrimitiveFirstCoefficients x y).2.natAbs <=
        Int.gcd x y *
          (linePrimitiveFirstCoefficients x y).2.natAbs :=
      Nat.le_mul_of_pos_left _ (Int.gcd_pos_of_ne_zero_right x hy)
    _ = y.natAbs :=
      gcd_mul_linePrimitiveFirstCoefficients_snd_natAbs x y

/-- Multiplication by the gcd recovers the raw sup height exactly. -/
theorem gcd_mul_linePrimitiveFirstCoefficientHeight (x y : Int) :
    Int.gcd x y * linePrimitiveFirstCoefficientHeight x y =
      max x.natAbs y.natAbs := by
  rw [linePrimitiveFirstCoefficientHeight]
  calc
    Int.gcd x y * max (linePrimitiveFirstCoefficients x y).1.natAbs
        (linePrimitiveFirstCoefficients x y).2.natAbs =
        max
          (Int.gcd x y *
            (linePrimitiveFirstCoefficients x y).1.natAbs)
          (Int.gcd x y *
            (linePrimitiveFirstCoefficients x y).2.natAbs) := by
      rw [max_mul_mul_left]
    _ = max x.natAbs y.natAbs := by
      rw [gcd_mul_linePrimitiveFirstCoefficients_fst_natAbs,
        gcd_mul_linePrimitiveFirstCoefficients_snd_natAbs]

theorem linePrimitiveFirstCoefficientHeight_pos
    {x y : Int} (hx : x ≠ 0) :
    0 < linePrimitiveFirstCoefficientHeight x y := by
  rw [linePrimitiveFirstCoefficientHeight, lt_max_iff]
  exact Or.inl (Int.natAbs_pos.mpr
    (linePrimitiveFirstCoefficients_fst_ne_zero hx))

/-- The source coefficients `(b1,b2,b3)` after eliminating the common first
pair member. -/
def lineCrossCoefficientVector (u u' : Int)
    (v v' : Fin 3 -> Int) : Fin 3 -> Int :=
  ![u' * v 1, -(u * v' 1), u' * v 2 - u * v' 2]

/-- The source constant `b4` after eliminating the common first member. -/
def lineCrossConstant (u u' v4 v4' : Int) : Int :=
  u' * v4 - u * v4'

@[simp]
theorem lineCrossCoefficientVector_zero (u u' : Int)
    (v v' : Fin 3 -> Int) :
    lineCrossCoefficientVector u u' v v' 0 = u' * v 1 :=
  rfl

@[simp]
theorem lineCrossCoefficientVector_one (u u' : Int)
    (v v' : Fin 3 -> Int) :
    lineCrossCoefficientVector u u' v v' 1 = -(u * v' 1) :=
  rfl

@[simp]
theorem lineCrossCoefficientVector_two (u u' : Int)
    (v v' : Fin 3 -> Int) :
    lineCrossCoefficientVector u u' v v' 2 =
      u' * v 2 - u * v' 2 :=
  rfl

theorem lineCrossCoefficientVector_zero_ne
    {u u' : Int} {v v' : Fin 3 -> Int}
    (hu' : u' ≠ 0) (hv : v 1 ≠ 0) :
    lineCrossCoefficientVector u u' v v' 0 ≠ 0 := by
  rw [lineCrossCoefficientVector_zero]
  exact mul_ne_zero hu' hv

theorem lineCrossCoefficientVector_one_ne
    {u u' : Int} {v v' : Fin 3 -> Int}
    (hu : u ≠ 0) (hv' : v' 1 ≠ 0) :
    lineCrossCoefficientVector u u' v v' 1 ≠ 0 := by
  rw [lineCrossCoefficientVector_one]
  exact neg_ne_zero.mpr (mul_ne_zero hu hv')

theorem lineCrossCoefficientVector_ne_zero
    {u u' : Int} {v v' : Fin 3 -> Int}
    (hu' : u' ≠ 0) (hv : v 1 ≠ 0) :
    lineCrossCoefficientVector u u' v v' ≠ 0 := by
  intro hzero
  exact lineCrossCoefficientVector_zero_ne hu' hv (congrFun hzero 0)

theorem linePrimitiveCrossCoefficientVector_zero_ne
    {x y : Int} {v v' : Fin 3 -> Int}
    (hy : y ≠ 0) (hv : v 1 ≠ 0) :
    lineCrossCoefficientVector
        (linePrimitiveFirstCoefficients x y).1
        (linePrimitiveFirstCoefficients x y).2 v v' 0 ≠ 0 :=
  lineCrossCoefficientVector_zero_ne
    (linePrimitiveFirstCoefficients_snd_ne_zero hy) hv

theorem linePrimitiveCrossCoefficientVector_one_ne
    {x y : Int} {v v' : Fin 3 -> Int}
    (hx : x ≠ 0) (hv' : v' 1 ≠ 0) :
    lineCrossCoefficientVector
        (linePrimitiveFirstCoefficients x y).1
        (linePrimitiveFirstCoefficients x y).2 v v' 1 ≠ 0 :=
  lineCrossCoefficientVector_one_ne
    (linePrimitiveFirstCoefficients_fst_ne_zero hx) hv'

/-- Cross-multiplication of two exact relations cancels their common first
pair member. -/
theorem lineCrossRelation_eq_zero
    {X : Nat} {a1 a2 a2' : Fin X}
    {v v' : Fin 3 -> Int} {v4 v4' u u' : Int} {d : Nat}
    (hrel : intVectorDot v (lineCoefficientVector a1 a2) + v4 = 0)
    (hrel' : intVectorDot v' (lineCoefficientVector a1 a2') + v4' = 0)
    (hv1 : v 0 = (d : Int) * u)
    (hv1' : v' 0 = (d : Int) * u') :
    intVectorDot (lineCrossCoefficientVector u u' v v')
        (lineCoefficientVector a2 a2') +
      lineCrossConstant u u' v4 v4' = 0 := by
  simp [intVectorDot, Fin.sum_univ_succ,
    ] at hrel hrel'
  simp [intVectorDot, Fin.sum_univ_succ, lineCrossCoefficientVector,
    lineCrossConstant]
  rw [hv1] at hrel
  rw [hv1'] at hrel'
  linear_combination u' * hrel - u * hrel'

theorem lineCrossCoefficientVector_zero_abs_le
    {u u' : Int} {v v' : Fin 3 -> Int} {U V : Real}
    (hU : 0 <= U) (hu' : abs ((u' : Int) : Real) <= U)
    (hv : abs ((v 1 : Int) : Real) <= V) :
    abs (((lineCrossCoefficientVector u u' v v' 0 : Int) : Real)) <=
      U * V := by
  simp only [lineCrossCoefficientVector_zero, Int.cast_mul, abs_mul]
  exact mul_le_mul hu' hv (abs_nonneg _) hU

theorem lineCrossCoefficientVector_one_abs_le
    {u u' : Int} {v v' : Fin 3 -> Int} {U V : Real}
    (hU : 0 <= U) (hu : abs ((u : Int) : Real) <= U)
    (hv' : abs ((v' 1 : Int) : Real) <= V) :
    abs (((lineCrossCoefficientVector u u' v v' 1 : Int) : Real)) <=
      U * V := by
  simp only [lineCrossCoefficientVector_one, Int.cast_neg, Int.cast_mul,
    abs_neg, abs_mul]
  exact mul_le_mul hu hv' (abs_nonneg _) hU

theorem lineCrossCoefficientVector_two_abs_le
    {u u' : Int} {v v' : Fin 3 -> Int} {U V : Real}
    (hU : 0 <= U)
    (hu : abs ((u : Int) : Real) <= U)
    (hu' : abs ((u' : Int) : Real) <= U)
    (hv : abs ((v 2 : Int) : Real) <= V)
    (hv' : abs ((v' 2 : Int) : Real) <= V) :
    abs (((lineCrossCoefficientVector u u' v v' 2 : Int) : Real)) <=
      2 * U * V := by
  simp only [lineCrossCoefficientVector_two, Int.cast_sub, Int.cast_mul]
  calc
    abs ((u' : Real) * (v 2 : Real) - (u : Real) * (v' 2 : Real)) <=
        abs ((u' : Real) * (v 2 : Real)) +
          abs ((u : Real) * (v' 2 : Real)) :=
      abs_sub _ _
    _ = abs (u' : Real) * abs (v 2 : Real) +
        abs (u : Real) * abs (v' 2 : Real) := by
      rw [abs_mul, abs_mul]
    _ <= U * V + U * V := add_le_add
      (mul_le_mul hu' hv (abs_nonneg _) hU)
      (mul_le_mul hu hv' (abs_nonneg _) hU)
    _ = 2 * U * V := by ring

theorem lineCrossCoefficientVector_abs_le
    {u u' : Int} {v v' : Fin 3 -> Int} {U V : Real}
    (hU : 0 <= U)
    (hu : abs ((u : Int) : Real) <= U)
    (hu' : abs ((u' : Int) : Real) <= U)
    (hv : forall i, abs ((v i : Int) : Real) <= V)
    (hv' : forall i, abs ((v' i : Int) : Real) <= V) :
    forall i,
      abs (((lineCrossCoefficientVector u u' v v' i : Int) : Real)) <=
        2 * U * V := by
  have hV : 0 <= V := (abs_nonneg ((v 0 : Int) : Real)).trans (hv 0)
  have hUV : 0 <= U * V := mul_nonneg hU hV
  intro i
  fin_cases i
  · exact (lineCrossCoefficientVector_zero_abs_le hU hu' (hv 1)).trans
      (by nlinarith)
  · exact (lineCrossCoefficientVector_one_abs_le hU hu (hv' 1)).trans
      (by nlinarith)
  · exact lineCrossCoefficientVector_two_abs_le
      hU hu hu' (hv 2) (hv' 2)

theorem lineCrossConstant_abs_le
    {u u' v4 v4' : Int} {U V : Real}
    (hU : 0 <= U)
    (hu : abs ((u : Int) : Real) <= U)
    (hu' : abs ((u' : Int) : Real) <= U)
    (hv4 : abs ((v4 : Int) : Real) <= V)
    (hv4' : abs ((v4' : Int) : Real) <= V) :
    abs (((lineCrossConstant u u' v4 v4' : Int) : Real)) <=
      2 * U * V := by
  simp only [lineCrossConstant, Int.cast_sub, Int.cast_mul]
  calc
    abs ((u' : Real) * (v4 : Real) - (u : Real) * (v4' : Real)) <=
        abs ((u' : Real) * (v4 : Real)) +
          abs ((u : Real) * (v4' : Real)) :=
      abs_sub _ _
    _ = abs (u' : Real) * abs (v4 : Real) +
        abs (u : Real) * abs (v4' : Real) := by
      rw [abs_mul, abs_mul]
    _ <= U * V + U * V := add_le_add
      (mul_le_mul hu' hv4 (abs_nonneg _) hU)
      (mul_le_mul hu hv4' (abs_nonneg _) hU)
    _ = 2 * U * V := by ring

/-- Two bounded relations with a common first member give the source cross
relation on their second members. -/
theorem isLowHeightPlanePair_of_linePrimitiveCross
    {X : Nat} {U V : Real} {w w' : LowHeightPlaneWitness X}
    (ha1 : w.a1 = w'.a1)
    (hw : w.IsRelation V) (hw' : w'.IsRelation V)
    (hw0' : w'.v 0 ≠ 0) (hw1 : w.v 1 ≠ 0)
    (hheight : (linePrimitiveFirstCoefficientHeight
      (w.v 0) (w'.v 0) : Real) <= U) :
    IsLowHeightPlanePair (2 * U * V) w.a2 w'.a2 := by
  let p := linePrimitiveFirstCoefficients (w.v 0) (w'.v 0)
  let b := lineCrossCoefficientVector p.1 p.2 w.v w'.v
  let b4 := lineCrossConstant p.1 p.2 w.v4 w'.v4
  have hU : 0 <= U :=
    (Nat.cast_nonneg (linePrimitiveFirstCoefficientHeight
      (w.v 0) (w'.v 0))).trans hheight
  have hu : abs ((p.1 : Int) : Real) <= U := by
    dsimp only [p]
    exact (linePrimitiveFirstCoefficients_fst_abs_le_height
      (w.v 0) (w'.v 0)).trans hheight
  have hu' : abs ((p.2 : Int) : Real) <= U := by
    dsimp only [p]
    exact (linePrimitiveFirstCoefficients_snd_abs_le_height
      (w.v 0) (w'.v 0)).trans hheight
  refine ⟨b, b4, Or.inl ?_, ?_, ?_, ?_⟩
  · dsimp only [b, p]
    exact lineCrossCoefficientVector_ne_zero
      (linePrimitiveFirstCoefficients_snd_ne_zero hw0') hw1
  · dsimp only [b, p]
    exact lineCrossCoefficientVector_abs_le hU hu hu' hw.2.1 hw'.2.1
  · dsimp only [b4, p]
    exact lineCrossConstant_abs_le hU hu hu' hw.2.2.1 hw'.2.2.1
  · dsimp only [b, b4, p]
    apply lineCrossRelation_eq_zero hw.2.2.2
      (by simpa only [← ha1] using hw'.2.2.2)
    · exact (gcd_mul_linePrimitiveFirstCoefficients_fst
        (w.v 0) (w'.v 0)).symm
    · exact (gcd_mul_linePrimitiveFirstCoefficients_snd
        (w.v 0) (w'.v 0)).symm

end PrimesRestrictedDigits
