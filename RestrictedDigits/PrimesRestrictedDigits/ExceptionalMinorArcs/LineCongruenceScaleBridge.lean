import PrimesRestrictedDigits.ExceptionalMinorArcs.CongruenceLatticeSourceCount
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineCongruenceMinimum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Source congruence minimum at the scaled physical norm

This is the minimum-height bridge used in `MAYNARD-PRD-PUBLISHED`, Lemma 15.2,
pp. 212--213. It specializes the affine congruence coefficient to `X`, as
required by the source minimum.
-/

namespace PrimesRestrictedDigits

/-- Dilation by `X / A >= 1` cannot reduce the repaired source minimum. -/
theorem sourceScaledPhysicalPair_norm_ge_minimum
    (X A a : Nat) (hA : 0 < A) (hAX : A <= X)
    (z : Prod Int Int) (hz : Not (z = 0))
    (hcong : Int.ModEq (a : Int)
      ((X : Int) * z.1 + z.2) 0) :
    (lineCongruenceMinimum X a : Real) <=
      norm (scaledPhysicalPair ((X : Real) / (A : Real)) z) := by
  let c : Prod Int Int := (-z.2, z.1)
  have hcne : Not (c = 0) := by
    intro hc
    apply hz
    apply Prod.ext
    · have hc2 := congrArg Prod.snd hc
      simpa [c] using hc2
    · have hc1 := congrArg Prod.fst hc
      simpa [c] using neg_eq_zero.mp hc1
  have hccong :
      Int.ModEq (a : Int) c.1 (c.2 * (X : Int)) := by
    rw [Int.modEq_iff_dvd] at hcong ⊢
    have hcong' :
        (a : Int) ∣ -((X : Int) * z.1 + z.2) := by
      convert hcong using 1; ring
    have hdiv :
        (a : Int) ∣ (X : Int) * z.1 + z.2 :=
      Int.dvd_neg.mp hcong'
    convert hdiv using 1; simp [c]; ring
  have hminimumNat :
      lineCongruenceMinimum X a <= lineCongruencePairHeight c :=
    lineCongruenceMinimum_le_height X a c ⟨hcne, hccong⟩
  have hminimum :
      (lineCongruenceMinimum X a : Real) <=
        (lineCongruencePairHeight c : Real) := by
    exact_mod_cast hminimumNat
  have hAReal : (0 : Real) < A := by exact_mod_cast hA
  have hAXReal : (A : Real) <= X := by exact_mod_cast hAX
  have hs : (1 : Real) <= (X : Real) / (A : Real) := by
    exact (le_div_iff₀ hAReal).2 (by simpa using hAXReal)
  have hsNonneg : (0 : Real) <= (X : Real) / (A : Real) :=
    zero_le_one.trans hs
  have hz1 :
      abs (z.1 : Real) <=
        abs (((X : Real) / (A : Real)) * (z.1 : Real)) := by
    rw [abs_mul, abs_of_nonneg hsNonneg]
    calc
      abs (z.1 : Real) = 1 * abs (z.1 : Real) := by ring
      _ <= ((X : Real) / (A : Real)) * abs (z.1 : Real) := by
        exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
  have hheight :
      (lineCongruencePairHeight c : Real) <=
        norm (scaledPhysicalPair ((X : Real) / (A : Real)) z) := by
    rw [Prod.norm_def]
    simp only [scaledPhysicalPair, Real.norm_eq_abs]
    rw [show (lineCongruencePairHeight c : Real) =
      max (abs (z.2 : Real)) (abs (z.1 : Real)) by
        simp [lineCongruencePairHeight, c, Nat.cast_max]]
    exact max_le (le_max_right _ _) (hz1.trans (le_max_left _ _))
  exact hminimum.trans hheight

/-- A strict source minimum band supplies factor-20 premise. -/
theorem sourceMinimumBand_le_scaledPhysicalPair_norm
    (X A a : Nat) (M : Real)
    (hA : 0 < A) (hAX : A <= X) (hM : 0 < M)
    (hMband : M / 10 < (lineCongruenceMinimum X a : Real))
    (z : Prod Int Int) (hz : Not (z = 0))
    (hcong : Int.ModEq (a : Int)
      ((X : Int) * z.1 + z.2) 0) :
    M / 20 <=
      norm (scaledPhysicalPair ((X : Real) / (A : Real)) z) := by
  have hmin := sourceScaledPhysicalPair_norm_ge_minimum
    X A a hA hAX z hz hcong
  have hhalf : M / 20 <= M / 10 := by linarith
  exact hhalf.trans (hMband.le.trans hmin)

/-- The source minimum class directly discharges the minimum hypothesis of
the factor-`640` affine congruence count. -/
theorem card_affineCongruence_le_sourceMinimumBand
    (a X A : Nat) (M B : Real) (r : Int)
    (hA : 0 < A) (hAX : A <= X)
    (haBand : (A : Real) / 10 < (a : Real))
    (hM : 0 < M)
    (hMband : M / 10 < (lineCongruenceMinimum X a : Real))
    (hB : 0 <= B)
    (S : Finset (Prod Int Int))
    (hcong : forall z, Membership.mem S z ->
      Int.ModEq (a : Int) ((X : Int) * z.1 + z.2) r)
    (hbound : forall z, Membership.mem S z ->
      norm (scaledPhysicalPair ((X : Real) / (A : Real)) z) <= B) :
    (S.card : Real) <=
      640 * (1 + B / M + B ^ 2 / (X : Real)) := by
  have hX : 0 < X := hA.trans_le hAX
  apply card_affineCongruence_le_sourceScale
    X a X A M B r hX hA haBand hM hB
  · intro z hz hzcong
    exact sourceMinimumBand_le_scaledPhysicalPair_norm
      X A a M hA hAX hM hMband z hz hzcong
  · exact hcong
  · exact hbound

end PrimesRestrictedDigits
