import PrimesRestrictedDigits.ExceptionalMinorArcs.CongruenceLatticeShortVector
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-!
# Counting points in homogeneous congruence coordinates
This is the homogeneous determinant-fiber count in the verified
repair for Lemma 15.2 of `MAYNARD-PRD-PUBLISHED`, pp. 212--213. It uses one
primitive short direction and explicit triangular coordinates, rather than a
Minkowski-reduced basis.
-/
open scoped BigOperators
namespace PrimesRestrictedDigits
private theorem card_int_finset_le_two_mul_add_one
    (S : Finset Int) (R : Real) (hR : 0 <= R)
    (hS : forall z, Membership.mem S z -> abs (z : Real) <= R) :
    (S.card : Real) <= 2 * R + 1 := by
  let n : Nat := Nat.floor R
  have hsubset : forall z, Membership.mem S z ->
      Membership.mem (Finset.Icc (-(n : Int)) (n : Int)) z := by
    intro z hz
    rw [Finset.mem_Icc]
    have hzUpperReal : (z : Real) <= R :=
      (le_abs_self (z : Real)).trans (hS z hz)
    have hzUpper : z <= (n : Int) := by
      have hzFloor : z <= Int.floor R := Int.le_floor.mpr hzUpperReal
      simpa [n, Int.natCast_floor_eq_floor hR] using hzFloor
    have hzLower : -(n : Int) <= z := by
      have hzNegReal : ((-z : Int) : Real) <= R := by
        calc
          ((-z : Int) : Real) <= abs (((-z : Int) : Real)) :=
            le_abs_self _
          _ = abs (z : Real) := by rw [Int.cast_neg, abs_neg]
          _ <= R := hS z hz
      have hzNegFloor : -z <= Int.floor R :=
        Int.le_floor.mpr hzNegReal
      have hzNeg : -z <= (n : Int) := by
        simpa [n, Int.natCast_floor_eq_floor hR] using hzNegFloor
      simpa using neg_le_neg hzNeg
    exact And.intro hzLower hzUpper
  have hcard : S.card <= 2 * n + 1 := by
    apply (Finset.card_le_card hsubset).trans_eq
    have hinterval :
        (Finset.Icc (-(n : Int)) (n : Int)).card = 2 * n + 1 := by
      have h := Int.card_Icc_of_le (-(n : Int)) (n : Int) (by omega)
      have hcast :
          ((Finset.Icc (-(n : Int)) (n : Int)).card : Int) =
            ((2 * n + 1 : Nat) : Int) := by
        calc
          ((Finset.Icc (-(n : Int)) (n : Int)).card : Int) =
              (n : Int) + 1 - (-(n : Int)) := h
          _ = ((2 * n + 1 : Nat) : Int) := by push_cast; ring
      exact_mod_cast hcast
    exact hinterval
  calc
    (S.card : Real) <= ((2 * n + 1 : Nat) : Real) := by
      exact_mod_cast hcard
    _ = 2 * (n : Real) + 1 := by push_cast; ring
    _ <= 2 * R + 1 := by
      have hn : (n : Real) <= R := Nat.floor_le hR
      linarith
private theorem abs_realPairDet_le_two_mul_norm_mul_norm
    (u z : Prod Real Real) :
    abs (realPairDet u z) <= 2 * norm u * norm z := by
  have huFirst : abs u.1 <= norm u := by
    simpa [Real.norm_eq_abs] using norm_fst_le u
  have huSecond : abs u.2 <= norm u := by
    simpa [Real.norm_eq_abs] using norm_snd_le u
  have hzFirst : abs z.1 <= norm z := by
    simpa [Real.norm_eq_abs] using norm_fst_le z
  have hzSecond : abs z.2 <= norm z := by
    simpa [Real.norm_eq_abs] using norm_snd_le z
  calc
    abs (realPairDet u z) <=
        abs (u.1 * z.2) + abs (u.2 * z.1) := by
      exact abs_sub _ _
    _ = abs u.1 * abs z.2 + abs u.2 * abs z.1 := by
      rw [abs_mul, abs_mul]
    _ <= norm u * norm z + norm u * norm z := by
      exact add_le_add
        (mul_le_mul huFirst hzSecond (abs_nonneg _) (norm_nonneg _))
        (mul_le_mul huSecond hzFirst (abs_nonneg _) (norm_nonneg _))
    _ = 2 * norm u * norm z := by ring
private theorem card_intPairDet_fiber_le
    (T a : Nat) (s B : Real) (u : Prod Int Int)
    (alpha beta d : Int) (m : Real)
    (hbezout : alpha * u.1 + beta * u.2 = 1)
    (hm : m = norm (anisotropicCongruenceVector T a s u))
    (hmPos : 0 < m) (hB : 0 <= B)
    (S : Finset (Prod Int Int))
    (hS : forall z, Membership.mem S z ->
      norm (anisotropicCongruenceVector T a s z) <= B) :
    ((S.filter fun z => intPairDet u z = d).card : Real) <=
      4 * B / m + 1 := by
  let fiber := S.filter fun z => intPairDet u z = d
  by_cases hfiber : fiber.Nonempty
  next =>
    let w := hfiber.choose
    have hw : Membership.mem fiber w := hfiber.choose_spec
    have hwS : Membership.mem S w := (Finset.mem_filter.mp hw).1
    have hwDet : intPairDet u w = d := (Finset.mem_filter.mp hw).2
    let offset : Prod Int Int -> Int := fun z =>
      intPairBezoutHeight alpha beta z - intPairBezoutHeight alpha beta w
    have hoffsetInjective : Set.InjOn offset fiber := by
      intro z hz v hv hzv
      have hzDet : intPairDet u z = d := (Finset.mem_filter.mp hz).2
      have hvDet : intPairDet u v = d := (Finset.mem_filter.mp hv).2
      have hsub := sub_eq_zsmul_of_intPairDet_eq u z v alpha beta
        hbezout (hzDet.trans hvDet.symm)
      have hheight :
          intPairBezoutHeight alpha beta z -
              intPairBezoutHeight alpha beta v = 0 := by
        dsimp [offset] at hzv
        linarith
      rw [hheight, zero_zsmul] at hsub
      exact sub_eq_zero.mp hsub
    have hoffsetBound : forall n, Membership.mem (fiber.image offset) n ->
        abs (n : Real) <= 2 * B / m := by
      intro n hn
      have hnData := Finset.mem_image.mp hn
      let z := hnData.choose
      have hz : Membership.mem fiber z := hnData.choose_spec.1
      have hnEq : offset z = n := hnData.choose_spec.2
      have hzS : Membership.mem S z := (Finset.mem_filter.mp hz).1
      have hzDet : intPairDet u z = d := (Finset.mem_filter.mp hz).2
      have hsub := sub_eq_zsmul_of_intPairDet_eq u z w alpha beta
        hbezout (hzDet.trans hwDet.symm)
      have hnormSub :
          norm (anisotropicCongruenceVector T a s (z - w)) <= 2 * B := by
        rw [anisotropicCongruenceVector_sub]
        calc
          norm (anisotropicCongruenceVector T a s z -
              anisotropicCongruenceVector T a s w) <=
              norm (anisotropicCongruenceVector T a s z) +
                norm (anisotropicCongruenceVector T a s w) := norm_sub_le _ _
          _ <= B + B := add_le_add (hS z hzS) (hS w hwS)
          _ = 2 * B := by ring
      have hnormOffset :
          abs ((intPairBezoutHeight alpha beta z -
              intPairBezoutHeight alpha beta w : Int) : Real) * m <=
            2 * B := by
        rw [hsub, anisotropicCongruenceVector_zsmul,
          norm_zsmul Real, Real.norm_eq_abs, hm.symm] at hnormSub
        exact hnormSub
      have hboundZ : abs (offset z : Real) <= (2 * B) / m := by
        dsimp [offset]
        calc
          abs ((intPairBezoutHeight alpha beta z -
              intPairBezoutHeight alpha beta w : Int) : Real) =
              (abs ((intPairBezoutHeight alpha beta z -
                intPairBezoutHeight alpha beta w : Int) : Real) * m) / m := by
            field_simp [hmPos.ne']
          _ <= (2 * B) / m :=
            div_le_div_of_nonneg_right hnormOffset hmPos.le
      simpa [hnEq] using hboundZ
    have himageCard := card_int_finset_le_two_mul_add_one
      (fiber.image offset) (2 * B / m) (by positivity) hoffsetBound
    have hcardImage : (fiber.card : Real) =
        ((fiber.image offset).card : Real) := by
      norm_cast
      exact (Finset.card_image_of_injOn hoffsetInjective).symm
    rw [hcardImage]
    convert himageCard using 1; ring
  next =>
    have hfiberEmpty : fiber = Finset.empty :=
      Finset.not_nonempty_iff_eq_empty.mp hfiber
    rw [show S.filter (fun z => intPairDet u z = d) = fiber from rfl,
      hfiberEmpty]
    have hcardZero :
        (Finset.empty : Finset (Prod Int Int)).card = 0 := rfl
    rw [hcardZero, Nat.cast_zero]
    have hBm : 0 <= B / m := div_nonneg hB hmPos.le
    rw [show 4 * B / m = 4 * (B / m) by ring]
    nlinarith
/-- A finite coefficient set in an anisotropically scaled congruence lattice
is controlled by its minimum nonzero spacing and determinant scale. -/
theorem card_anisotropicCongruenceCoefficients_le
    (T a : Nat) (s mu B : Real)
    (ha : 0 < a) (hs : 0 < s) (hmu : 0 < mu) (hB : 0 <= B)
    (hmin : forall z : Prod Int Int, Not (z = 0) ->
      mu <= norm (anisotropicCongruenceVector T a s z))
    (S : Finset (Prod Int Int))
    (hS : forall z, Membership.mem S z ->
      norm (anisotropicCongruenceVector T a s z) <= B) :
    (S.card : Real) <=
      16 * (1 + B / mu + B ^ 2 / ((a : Real) * s)) := by
  let short := exists_primitive_anisotropicCongruenceVector T a s ha hs
  let u : Prod Int Int := short.choose
  have huPrimitive : Int.gcd u.1 u.2 = 1 := by
    simpa [u] using short.choose_spec.1
  have huPos : 0 < norm (anisotropicCongruenceVector T a s u) := by
    simpa [u] using short.choose_spec.2.1
  have huShort : norm (anisotropicCongruenceVector T a s u) <=
      Real.sqrt ((a : Real) * s) := by
    simpa [u] using short.choose_spec.2.2
  let m : Real := norm (anisotropicCongruenceVector T a s u)
  let D : Real := (a : Real) * s
  have hmPos : 0 < m := by simpa [m] using huPos
  have hDPos : 0 < D := by dsimp [D]; positivity
  have huNe : Not (u = 0) := by
    intro hu
    have hzero : norm (anisotropicCongruenceVector T a s u) = 0 := by
      rw [hu, anisotropicCongruenceVector_zero]
      exact norm_zero
    linarith
  have hmuLeM : mu <= m := by
    simpa [m] using hmin u huNe
  have hmShort : m <= Real.sqrt D := by
    simpa [m, D] using huShort
  let alpha : Int := Int.gcdA u.1 u.2
  let beta : Int := Int.gcdB u.1 u.2
  have hbezout : alpha * u.1 + beta * u.2 = 1 := by
    simpa [alpha, beta, huPrimitive, mul_comm] using
      (Int.gcd_eq_gcd_ab u.1 u.2).symm
  let determinants : Finset Int := S.image (intPairDet u)
  have hdeterminantBound : forall d, Membership.mem determinants d ->
      abs (d : Real) <= 2 * m * B / D := by
    intro d hd
    have hdData := Finset.mem_image.mp hd
    let z := hdData.choose
    have hz : Membership.mem S z := hdData.choose_spec.1
    have hdEq : intPairDet u z = d := hdData.choose_spec.2
    have hscaled : abs (intPairDet u z : Real) * D <= 2 * m * B := by
      calc
        abs (intPairDet u z : Real) * D =
          abs (D * (intPairDet u z : Real)) := by
          rw [abs_mul, abs_of_pos hDPos]
          ring
        _ = abs (realPairDet (anisotropicCongruenceVector T a s u)
            (anisotropicCongruenceVector T a s z)) := by
          rw [realPairDet_anisotropicCongruenceVector]
        _ <= 2 * m *
            norm (anisotropicCongruenceVector T a s z) := by
          simpa [m] using abs_realPairDet_le_two_mul_norm_mul_norm
            (anisotropicCongruenceVector T a s u)
            (anisotropicCongruenceVector T a s z)
        _ <= 2 * m * B := by
          gcongr
          exact hS z hz
    have hzBound : abs (intPairDet u z : Real) <=
        (2 * m * B) / D := by
      calc
        abs (intPairDet u z : Real) =
            (abs (intPairDet u z : Real) * D) / D := by
          field_simp [hDPos.ne']
        _ <= (2 * m * B) / D :=
          div_le_div_of_nonneg_right hscaled hDPos.le
    simpa [hdEq] using hzBound
  have hdeterminantsCard : (determinants.card : Real) <=
      4 * m * B / D + 1 := by
    have h := card_int_finset_le_two_mul_add_one determinants
      (2 * m * B / D) (by positivity) hdeterminantBound
    convert h using 1; ring
  have hfiberBound : forall d, Membership.mem determinants d ->
      ((S.filter fun z => intPairDet u z = d).card : Real) <=
        4 * B / m + 1 := by
    intro d _hd
    exact card_intPairDet_fiber_le T a s B u alpha beta d m
      hbezout rfl hmPos hB S hS
  have hcardProduct : (S.card : Real) <=
      (4 * m * B / D + 1) * (4 * B / m + 1) := by
    calc
      (S.card : Real) =
          Finset.sum determinants fun d =>
            ((S.filter fun z => intPairDet u z = d).card : Real) := by
        norm_cast
        exact Finset.card_eq_sum_card_image (intPairDet u) S
      _ <= Finset.sum determinants (fun _d => 4 * B / m + 1) := by
        gcongr with d hd
        exact hfiberBound d hd
      _ = (determinants.card : Real) * (4 * B / m + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ <= (4 * m * B / D + 1) * (4 * B / m + 1) := by
        gcongr
  have hmSquare : m ^ 2 <= D := by
    nlinarith [Real.sq_sqrt hDPos.le, norm_nonneg
      (anisotropicCongruenceVector T a s u)]
  have hmMu : m * mu <= D := by
    calc
      m * mu <= m * m := mul_le_mul_of_nonneg_left hmuLeM hmPos.le
      _ = m ^ 2 := by ring
      _ <= D := hmSquare
  have hBdiv : B / m <= B / mu := by
    exact div_le_div_of_nonneg_left hB hmu hmuLeM
  have hmDiv : m / D <= 1 / mu := by
    calc
      m / D = (m * mu) / (D * mu) := by
        field_simp [hDPos.ne', hmu.ne']
      _ <= D / (D * mu) := by
        exact div_le_div_of_nonneg_right hmMu (by positivity)
      _ = 1 / mu := by
        field_simp [hDPos.ne', hmu.ne']
  have hexpanded :
      (4 * m * B / D + 1) * (4 * B / m + 1) =
        1 + 4 * (B / m) + 4 * B * (m / D) +
          16 * B ^ 2 / D := by
    field_simp [hmPos.ne', hDPos.ne']
    ring
  rw [hexpanded] at hcardProduct
  calc
    (S.card : Real) <=
        1 + 4 * (B / m) + 4 * B * (m / D) +
          16 * B ^ 2 / D := hcardProduct
    _ <= 1 + 8 * (B / mu) + 16 * B ^ 2 / D := by
      have hlinearOne : 4 * (B / m) <= 4 * (B / mu) := by
        gcongr
      have hlinearTwo : 4 * B * (m / D) <= 4 * (B / mu) := by
        calc
          4 * B * (m / D) <= 4 * B * (1 / mu) := by
            gcongr
          _ = 4 * (B / mu) := by ring
      linarith
    _ <= 16 * (1 + B / mu + B ^ 2 / D) := by
      have hBmu : 0 <= B / mu := by positivity
      calc
        1 + 8 * (B / mu) + 16 * B ^ 2 / D <=
            1 + 8 * (B / mu) + 16 * B ^ 2 / D +
              (15 + 8 * (B / mu)) := by
          exact le_add_of_nonneg_right (by linarith)
        _ = 16 * (1 + B / mu + B ^ 2 / D) := by ring
    _ = 16 * (1 + B / mu + B ^ 2 / ((a : Real) * s)) := by
      rfl

end PrimesRestrictedDigits
