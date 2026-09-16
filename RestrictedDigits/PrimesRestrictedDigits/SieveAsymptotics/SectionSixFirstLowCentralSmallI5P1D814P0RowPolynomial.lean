import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation
/-! # SectionSixFirstLowCentralSmallI5P1D814P0RowPolynomial -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-!
# transformed Piece0 order-4 row arithmetic

This fixed-delta module contains only the exact polynomial and rational arithmetic slice. It
proves no set-integral, Fubini, Jacobian, source-region, or full-Piece0 statement. The source
context is Maynard, published Section 6, Eq. (6.12).
-/

def sectionSixFirstLowCentralSmallI5P1D814FinPoly {n : Nat}
    (c : Fin n → Real) (x : Real) : Real :=
  ∑ i : Fin n, c i * x ^ (i : Nat)

theorem sectionSixFirstLowCentralSmallI5P1D814_intervalIntegral_finPoly
    {n : Nat} (c : Fin n → Real) (a b : Real) :
    (∫ x in a..b,
      sectionSixFirstLowCentralSmallI5P1D814FinPoly c x) =
      ∑ i : Fin n, c i *
        (b ^ ((i : Nat) + 1) - a ^ ((i : Nat) + 1)) /
          (((i : Nat) : Real) + 1) := by
  classical
  simp only [sectionSixFirstLowCentralSmallI5P1D814FinPoly]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_const_mul, integral_pow]
    ring
  · intro i hi
    have hc : Continuous (fun x : Real => c i * x ^ (i : Nat)) := by
      fun_prop
    exact hc.intervalIntegrable (μ := volume) a b

def sectionSixFirstLowCentralSmallI5P1D814Q4 (a x : Real) : Real :=
  1 / a - x / a ^ 2 + x ^ 2 / a ^ 3 - x ^ 3 / a ^ 4 + x ^ 4 / a ^ 5

def sectionSixFirstLowCentralSmallI5P1D814Q4Primitive (a x : Real) : Real :=
  x / a - x ^ 2 / (2 * a ^ 2) + x ^ 3 / (3 * a ^ 3) -
    x ^ 4 / (4 * a ^ 4) + x ^ 5 / (5 * a ^ 5)

theorem sectionSixFirstLowCentralSmallI5P1D814_q4_sub_inv
    {a x : Real} (ha : 0 < a) (hx : 0 ≤ x) :
    sectionSixFirstLowCentralSmallI5P1D814Q4 a x - 1 / (a + x) =
      x ^ 5 / (a ^ 5 * (a + x)) := by
  have hax : 0 < a + x := by linarith
  unfold sectionSixFirstLowCentralSmallI5P1D814Q4
  field_simp [ne_of_gt ha, ne_of_gt hax]
  ring

/- The first of the 256 equal d-slabs in transformed Piece0. -/
def sectionSixFirstLowCentralSmallI5P1D814P0Row0A : Real :=
  16249 / 125000

def sectionSixFirstLowCentralSmallI5P1D814P0Row0B : Real :=
  208081 / 1600000

def sectionSixFirstLowCentralSmallI5P1D814P0Row0R (d : Real) : Real :=
  (16 / 25 - 212499 / 500000 - d) / 2

def sectionSixFirstLowCentralSmallI5P1D814P0Row0Coeff : Fin 11 → Real := ![
  (124596995462940856783918083484502403740193502791740689 /
    619981557044426599804491883923614702528228712303820800 : Real),
  (-239082606393733504548566279055673987847530790853125 /
    129162824384255541625935809150753063026714315063296 : Real),
  (67138717902403139278096997671782460425745068359375 /
    8072676524015971351620988071922066439169644691456 : Real),
  (-4749924299271945485302558408559689508819580078125 /
    94601678015812164276808453967836716084019273728 : Real),
  (968700388195195288517115276856887340545654296875 /
    3941736583992173511533685581993196503500803072 : Real),
  (-16292873729397481778273071832954883575439453125 /
    20529878041625903705904612406214565122400016 : Real),
  (29292433370900582549246610142290592193603515625 /
    11548056398414570834571344478495692881350009 : Real),
  (-9442732355238409945741295814514160156250000000 /
    1283117377601618981619038275388410320150001 : Real),
  (62940507749954122118651866912841796875000000000 /
    3849352132804856944857114826165230960450003 : Real),
  (-27285932446829974651336669921875000000000000000 /
    1283117377601618981619038275388410320150001 : Real),
  (18189894035458564758300781250000000000000000000 /
    1283117377601618981619038275388410320150001 : Real)]

def sectionSixFirstLowCentralSmallI5P1D814P0Row0CrossPoly (d : Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D814FinPoly
    sectionSixFirstLowCentralSmallI5P1D814P0Row0Coeff d

theorem sectionSixFirstLowCentralSmallI5P1D814_p0CrossPoly_eq
    (d : Real) :
    sectionSixFirstLowCentralSmallI5P1D814P0Row0CrossPoly d =
      sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
        sectionSixFirstLowCentralSmallI5P1D814P0Row0A
        (sectionSixFirstLowCentralSmallI5P1D814P0Row0R d) ^ 2 / 2 := by
  norm_num [sectionSixFirstLowCentralSmallI5P1D814P0Row0CrossPoly,
    sectionSixFirstLowCentralSmallI5P1D814FinPoly,
    sectionSixFirstLowCentralSmallI5P1D814P0Row0Coeff,
    sectionSixFirstLowCentralSmallI5P1D814P0Row0A,
    sectionSixFirstLowCentralSmallI5P1D814P0Row0R,
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive,
    Fin.sum_univ_succ]
  field_simp
  ring

theorem sectionSixFirstLowCentralSmallI5P1D814_p0CrossPoly_integral :
    (∫ d in sectionSixFirstLowCentralSmallI5P1D814P0Row0A..
      sectionSixFirstLowCentralSmallI5P1D814P0Row0B,
      sectionSixFirstLowCentralSmallI5P1D814P0Row0CrossPoly d) =
      (422425090467166297479419210932558798733999410219527139358672154053039 /
        179962709777932353439091705787450694066781916350571323414262526771200000000 : Real) := by
  change (∫ d in sectionSixFirstLowCentralSmallI5P1D814P0Row0A..
    sectionSixFirstLowCentralSmallI5P1D814P0Row0B,
    sectionSixFirstLowCentralSmallI5P1D814FinPoly
      sectionSixFirstLowCentralSmallI5P1D814P0Row0Coeff d) = _
  rw [sectionSixFirstLowCentralSmallI5P1D814_intervalIntegral_finPoly]
  norm_num [sectionSixFirstLowCentralSmallI5P1D814P0Row0Coeff,
    sectionSixFirstLowCentralSmallI5P1D814P0Row0A,
    sectionSixFirstLowCentralSmallI5P1D814P0Row0B, Fin.sum_univ_succ]

theorem sectionSixFirstLowCentralSmallI5P1D814_p0Row0Weight_lt :
    (564383 / 1000000 : Real) *
        (1 / (16249 / 250000 : Real) -
          1 / (sectionSixFirstLowCentralSmallI5P1D814P0Row0B -
            16249 / 250000 : Real)) /
        (212499 / 500000 -
          sectionSixFirstLowCentralSmallI5P1D814P0Row0B) *
        (∫ d in sectionSixFirstLowCentralSmallI5P1D814P0Row0A..
          sectionSixFirstLowCentralSmallI5P1D814P0Row0B,
          sectionSixFirstLowCentralSmallI5P1D814P0Row0CrossPoly d) <
      (1 / 10000000 : Real) := by
  rw [sectionSixFirstLowCentralSmallI5P1D814_p0CrossPoly_integral]
  norm_num [sectionSixFirstLowCentralSmallI5P1D814P0Row0A,
    sectionSixFirstLowCentralSmallI5P1D814P0Row0B]

end

end PrimesRestrictedDigits
