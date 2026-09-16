import PrimesRestrictedDigits.ExceptionalMinorArcs.CongruenceLatticeAffineCount
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Source-scale affine congruence count

This specializes the exact affine lattice count to the factor-ten height class used in
`MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 212--213.
-/

namespace PrimesRestrictedDigits

/-- At scale `s = X / A` and minimum `M / 20`, the source lower band
`A / 10 < a` gives the uniform factor-`640` affine count. -/
theorem card_affineCongruence_le_sourceScale
    (T a X A : Nat) (M B : Real) (r : Int)
    (hX : 0 < X) (hA : 0 < A)
    (haBand : (A : Real) / 10 < (a : Real))
    (hM : 0 < M) (hB : 0 <= B)
    (hmin : forall z : Prod Int Int, Not (z = 0) ->
      Int.ModEq (a : Int) ((T : Int) * z.1 + z.2) 0 ->
      M / 20 <=
        norm (scaledPhysicalPair ((X : Real) / (A : Real)) z))
    (S : Finset (Prod Int Int))
    (hcong : forall z, Membership.mem S z ->
      Int.ModEq (a : Int) ((T : Int) * z.1 + z.2) r)
    (hbound : forall z, Membership.mem S z ->
      norm (scaledPhysicalPair ((X : Real) / (A : Real)) z) <= B) :
    (S.card : Real) <=
      640 * (1 + B / M + B ^ 2 / (X : Real)) := by
  let s : Real := (X : Real) / (A : Real)
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have haReal : (0 : Real) < a := by
    have hAdiv : (0 : Real) < (A : Real) / 10 := by positivity
    exact hAdiv.trans haBand
  have ha : 0 < a := by exact_mod_cast haReal
  have hmu : 0 < M / 20 := by positivity
  have hcount := card_affineCongruence_le
    T a s (M / 20) B r ha hs hmu hB
    (by simpa only [s] using hmin) S hcong
    (by simpa only [s] using hbound)
  have hdet : (X : Real) / 10 < (a : Real) * s := by
    dsimp [s]
    have hscale : 0 < (X : Real) / (A : Real) := by positivity
    have hmul := mul_lt_mul_of_pos_right haBand hscale
    calc
      (X : Real) / 10 = ((A : Real) / 10) *
          ((X : Real) / (A : Real)) := by field_simp
      _ < (a : Real) * ((X : Real) / (A : Real)) := hmul
  have hquadratic :
      64 * B ^ 2 / ((a : Real) * s) <=
        640 * B ^ 2 / (X : Real) := by
    have hleft : B ^ 2 / ((a : Real) * s) <=
        B ^ 2 / ((X : Real) / 10) := by
      exact div_le_div_of_nonneg_left
        (sq_nonneg B) (by positivity) hdet.le
    calc
      64 * B ^ 2 / ((a : Real) * s) =
          64 * (B ^ 2 / ((a : Real) * s)) := by ring
      _ <= 64 * (B ^ 2 / ((X : Real) / 10)) := by gcongr
      _ = 640 * B ^ 2 / (X : Real) := by
        field_simp
        ring
  have hlinear : 32 * B / (M / 20) = 640 * B / M := by
    field_simp
    ring
  rw [hlinear] at hcount
  calc
    (S.card : Real) <=
        16 + 640 * B / M + 64 * B ^ 2 / ((a : Real) * s) := hcount
    _ <= 16 + 640 * B / M + 640 * B ^ 2 / (X : Real) := by
      linarith
    _ = 16 + 640 * (B / M) +
        640 * (B ^ 2 / (X : Real)) := by ring
    _ <= 640 + 640 * (B / M) +
        640 * (B ^ 2 / (X : Real)) := by norm_num
    _ = 640 * (1 + B / M + B ^ 2 / (X : Real)) := by ring

end PrimesRestrictedDigits
