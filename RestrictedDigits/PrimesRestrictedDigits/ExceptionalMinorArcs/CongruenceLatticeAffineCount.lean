import PrimesRestrictedDigits.ExceptionalMinorArcs.CongruenceLatticeCount
import Mathlib.Data.Int.ModEq

/-!
# Counting points in an affine congruence class

This is the affine-translation part of the repair for Lemma 15.2 of `MAYNARD-PRD-PUBLISHED`,
pp. 212--213. A basepoint is chosen from the bounded set itself, avoiding the unsupported
anisotropic claim about an unscaled Euclidean-minimal representative in the published proof.
-/

namespace PrimesRestrictedDigits

/-- The anisotropically scaled real vector attached to a physical integer
pair. -/
def scaledPhysicalPair (s : Real) (z : Prod Int Int) : Prod Real Real :=
  (s * (z.1 : Real), (z.2 : Real))

private theorem scaledPhysicalPair_sub
    (s : Real) (z w : Prod Int Int) :
    scaledPhysicalPair s (z - w) =
      scaledPhysicalPair s z - scaledPhysicalPair s w := by
  apply Prod.ext
  · simp [scaledPhysicalPair]
    ring
  · simp [scaledPhysicalPair]

private theorem scaledPhysicalPair_injective
    (s : Real) (hs : 0 < s) : Function.Injective (scaledPhysicalPair s) := by
  intro z w hzw
  apply Prod.ext
  next =>
    have hfirst := congrArg Prod.fst hzw
    simp only [scaledPhysicalPair, mul_eq_mul_left_iff] at hfirst
    have hcast : (z.1 : Real) = (w.1 : Real) :=
      hfirst.resolve_right hs.ne'
    exact_mod_cast hcast
  next =>
    have hsecond := congrArg Prod.snd hzw
    have hcast : (z.2 : Real) = (w.2 : Real) := by
      simpa [scaledPhysicalPair] using hsecond
    exact_mod_cast hcast

private def affineDifferenceCoefficient
    (T a : Nat) (base z : Prod Int Int) : Prod Int Int :=
  let x := z.1 - base.1
  let y := z.2 - base.2
  (x, ((T : Int) * x + y) / (a : Int))

private theorem anisotropicCongruenceVector_affineDifferenceCoefficient
    (T a : Nat) (s : Real) (base z : Prod Int Int)
    (hdiv : Dvd.dvd (a : Int)
      ((T : Int) * (z.1 - base.1) + (z.2 - base.2))) :
    anisotropicCongruenceVector T a s
        (affineDifferenceCoefficient T a base z) =
      scaledPhysicalPair s (z - base) := by
  apply Prod.ext
  next => simp [affineDifferenceCoefficient, scaledPhysicalPair]
  next =>
    have hcancel := Int.mul_ediv_cancel' hdiv
    have hinteger :
        (a : Int) *
              (((T : Int) * (z.1 - base.1) + (z.2 - base.2)) /
                (a : Int)) -
            (T : Int) * (z.1 - base.1) = z.2 - base.2 := by
      rw [hcancel]
      ring
    change
      ((((a : Int) *
            (((T : Int) * (z.1 - base.1) + (z.2 - base.2)) /
              (a : Int)) -
          (T : Int) * (z.1 - base.1) : Int) : Real) =
        ((z.2 - base.2 : Int) : Real))
    exact_mod_cast hinteger

/-- A bounded finite subset of one affine congruence class is controlled by
the minimum spacing in its homogeneous congruence lattice. -/
theorem card_affineCongruence_le
    (T a : Nat) (s mu B : Real) (r : Int)
    (ha : 0 < a) (hs : 0 < s) (hmu : 0 < mu) (hB : 0 <= B)
    (hmin : forall z : Prod Int Int, Not (z = 0) ->
      Int.ModEq (a : Int) ((T : Int) * z.1 + z.2) 0 ->
      mu <= norm (scaledPhysicalPair s z))
    (S : Finset (Prod Int Int))
    (hcong : forall z, Membership.mem S z ->
      Int.ModEq (a : Int) ((T : Int) * z.1 + z.2) r)
    (hbound : forall z, Membership.mem S z ->
      norm (scaledPhysicalPair s z) <= B) :
    (S.card : Real) <=
      16 + 32 * B / mu + 64 * B ^ 2 / ((a : Real) * s) := by
  have hcoefficientMin : forall z : Prod Int Int, Not (z = 0) ->
      mu <= norm (anisotropicCongruenceVector T a s z) := by
    intro z hz
    let physical : Prod Int Int :=
      (z.1, (a : Int) * z.2 - (T : Int) * z.1)
    have hphysicalNe : Not (physical = 0) := by
      intro hphysical
      have hmapZero : anisotropicCongruenceVector T a s z = 0 := by
        have hscaled := congrArg (scaledPhysicalPair s) hphysical
        simpa [physical, scaledPhysicalPair, anisotropicCongruenceVector,
          anisotropicCongruenceMap] using hscaled
      exact hz ((anisotropicCongruenceVector_eq_zero_iff
        T a s ha hs z).mp hmapZero)
    have hphysicalCongruence :
        Int.ModEq (a : Int)
          ((T : Int) * physical.1 + physical.2) 0 := by
      simp [physical, Int.modEq_iff_dvd]
    simpa [physical, scaledPhysicalPair, anisotropicCongruenceVector,
      anisotropicCongruenceMap] using
        hmin physical hphysicalNe hphysicalCongruence
  by_cases hSEmpty : S = Finset.empty
  next =>
    subst S
    have hcardZero :
        (Finset.empty : Finset (Prod Int Int)).card = 0 := rfl
    rw [hcardZero, Nat.cast_zero]
    have hBmu : 0 <= B / mu := div_nonneg hB hmu.le
    have hdet : 0 <= B ^ 2 / ((a : Real) * s) := by positivity
    calc
      (0 : Real) <=
          16 + 32 * (B / mu) +
            64 * (B ^ 2 / ((a : Real) * s)) := by positivity
      _ = 16 + 32 * B / mu +
          64 * B ^ 2 / ((a : Real) * s) := by ring
  next =>
    have hSNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSEmpty
    let base : Prod Int Int := hSNonempty.choose
    have hbase : Membership.mem S base := hSNonempty.choose_spec
    let coefficient : Prod Int Int -> Prod Int Int :=
      affineDifferenceCoefficient T a base
    let coefficients : Finset (Prod Int Int) := S.image coefficient
    have hhomogeneous : forall z, Membership.mem S z ->
        Int.ModEq (a : Int)
          ((T : Int) * (z.1 - base.1) + (z.2 - base.2)) 0 := by
      intro z hz
      have h := (hcong z hz).sub (hcong base hbase)
      convert h using 1 <;> ring
    have hdiv : forall z, Membership.mem S z ->
        Dvd.dvd (a : Int)
          ((T : Int) * (z.1 - base.1) + (z.2 - base.2)) := by
      intro z hz
      have h := Int.modEq_iff_dvd.mp (hhomogeneous z hz)
      have hneg : Dvd.dvd (a : Int)
          (-((T : Int) * (z.1 - base.1) + (z.2 - base.2))) := by
        convert h using 1; ring
      exact Int.dvd_neg.mp hneg
    have hvector : forall z, Membership.mem S z ->
        anisotropicCongruenceVector T a s (coefficient z) =
          scaledPhysicalPair s (z - base) := by
      intro z hz
      exact anisotropicCongruenceVector_affineDifferenceCoefficient
        T a s base z (hdiv z hz)
    have hcoefficientInjective : Set.InjOn coefficient S := by
      intro z hz w hw hzw
      apply sub_left_injective (b := base)
      apply scaledPhysicalPair_injective s hs
      calc
        scaledPhysicalPair s (z - base) =
            anisotropicCongruenceVector T a s (coefficient z) :=
          (hvector z hz).symm
        _ = anisotropicCongruenceVector T a s (coefficient w) := by
          rw [hzw]
        _ = scaledPhysicalPair s (w - base) := hvector w hw
    have hcoefficientsCard : coefficients.card = S.card := by
      exact Finset.card_image_of_injOn hcoefficientInjective
    have hcoefficientsBound : forall z, Membership.mem coefficients z ->
        norm (anisotropicCongruenceVector T a s z) <= 2 * B := by
      intro z hz
      have hzData := Finset.mem_image.mp hz
      let w := hzData.choose
      have hw : Membership.mem S w := hzData.choose_spec.1
      have hzEq : coefficient w = z := hzData.choose_spec.2
      have hwBound :
          norm (anisotropicCongruenceVector T a s (coefficient w)) <=
            2 * B := by
        rw [hvector w hw, scaledPhysicalPair_sub]
        calc
          norm (scaledPhysicalPair s w - scaledPhysicalPair s base) <=
              norm (scaledPhysicalPair s w) +
                norm (scaledPhysicalPair s base) := norm_sub_le _ _
          _ <= B + B := add_le_add (hbound w hw) (hbound base hbase)
          _ = 2 * B := by ring
      simpa [hzEq] using hwBound
    have hcount := card_anisotropicCongruenceCoefficients_le
      T a s mu (2 * B) ha hs hmu (by positivity) hcoefficientMin
      coefficients hcoefficientsBound
    calc
      (S.card : Real) = (coefficients.card : Real) := by
        exact_mod_cast hcoefficientsCard.symm
      _ <= 16 *
          (1 + (2 * B) / mu +
            (2 * B) ^ 2 / ((a : Real) * s)) := hcount
      _ = 16 + 32 * B / mu +
          64 * B ^ 2 / ((a : Real) * s) := by ring

end PrimesRestrictedDigits
