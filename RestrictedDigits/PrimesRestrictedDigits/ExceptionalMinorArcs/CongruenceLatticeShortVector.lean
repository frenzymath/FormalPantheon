import PrimesRestrictedDigits.ExceptionalMinorArcs.CongruenceLatticeCoordinates
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# A primitive short direction in explicit congruence coordinates

This is the Dirichlet-approximation component of the replacement for the reduced-basis
paragraph in Lemma 15.2 of `MAYNARD-PRD-PUBLISHED`, pp. 212--213.
-/

namespace PrimesRestrictedDigits

/-- The explicit anisotropic congruence lattice has a primitive nonzero
direction no longer than the square root of its determinant scale. -/
theorem exists_primitive_anisotropicCongruenceVector
    (T a : Nat) (s : Real) (ha : 0 < a) (hs : 0 < s) :
    exists u : Int × Int,
      And (Int.gcd u.1 u.2 = 1)
        (And (0 < norm (anisotropicCongruenceVector T a s u))
          (norm (anisotropicCongruenceVector T a s u) <=
            Real.sqrt ((a : Real) * s))) := by
  by_cases has : (a : Real) <= s
  · refine ⟨(0, 1), by simp, ?_, ?_⟩
    · rw [show norm (anisotropicCongruenceVector T a s (0, 1)) =
          (a : Real) by
        rw [Prod.norm_def]
        simp [anisotropicCongruenceVector, anisotropicCongruenceMap,
          abs_of_nonneg (by positivity : (0 : Real) <= a)]]
      positivity
    · rw [show norm (anisotropicCongruenceVector T a s (0, 1)) =
          (a : Real) by
        rw [Prod.norm_def]
        simp [anisotropicCongruenceVector, anisotropicCongruenceMap,
          abs_of_nonneg (by positivity : (0 : Real) <= a)]]
      rw [Real.le_sqrt (by positivity) (by positivity)]
      have haNonneg : (0 : Real) <= a := by positivity
      nlinarith
  · have hsa : s < (a : Real) := lt_of_not_ge has
    let t : Real := Real.sqrt ((a : Real) * s)
    have ht : 0 < t := by
      exact Real.sqrt_pos.2 (mul_pos (by positivity) hs)
    have hts : s < t := by
      rw [Real.lt_sqrt hs.le]
      have haReal : (0 : Real) < a := by positivity
      nlinarith
    let n : Nat := Nat.floor (t / s)
    have hn : 0 < n := by
      change 0 < Nat.floor (t / s)
      rw [Nat.floor_pos]
      exact (one_le_div₀ hs).2 hts.le
    obtain ⟨j, k, hk, hkn, herror⟩ :=
      Real.exists_int_int_abs_mul_sub_le
        ((T : Real) / (a : Real)) hn
    let w : Int × Int := (k, j)
    have hfloorNonneg : 0 <= t / s := by positivity
    have hnFloor : (n : Real) <= t / s := by
      change ((Nat.floor (t / s) : Nat) : Real) <= t / s
      exact Nat.floor_le hfloorNonneg
    have hkReal : (k : Real) <= (n : Real) := by
      exact_mod_cast hkn
    have hkRealPos : (0 : Real) < k := by exact_mod_cast hk
    have hsn : s * (n : Real) <= t := by
      calc
        s * (n : Real) <= s * (t / s) :=
          mul_le_mul_of_nonneg_left hnFloor hs.le
        _ = t := by field_simp
    have hfirst : abs (s * (k : Real)) <= t := by
      rw [abs_mul, abs_of_pos hs, abs_of_pos hkRealPos]
      exact (mul_le_mul_of_nonneg_left hkReal hs.le).trans hsn
    have htSquare : t ^ 2 = (a : Real) * s := by
      exact Real.sq_sqrt (mul_nonneg (by positivity) hs.le)
    have hfloorLt : t / s < (n : Real) + 1 := by
      change t / s < ((Nat.floor (t / s) : Nat) : Real) + 1
      exact Nat.lt_floor_add_one (t / s)
    have hden : 0 < (n : Real) + 1 := by positivity
    have haDiv : (a : Real) / ((n : Real) + 1) <= t := by
      have hmul : t < ((n : Real) + 1) * s :=
        (div_lt_iff₀ hs).mp hfloorLt
      apply (div_le_iff₀ hden).2
      nlinarith [mul_pos ht hs]
    have hsecondIdentity :
        (((a : Int) * j - (T : Int) * k : Int) : Real) =
          -(a : Real) *
            ((k : Real) * ((T : Real) / (a : Real)) - (j : Real)) := by
      push_cast
      field_simp
      ring
    have hsecond :
        abs ((((a : Int) * j - (T : Int) * k : Int) : Real)) <= t := by
      rw [hsecondIdentity, abs_mul, abs_neg,
        abs_of_nonneg (by positivity : (0 : Real) <= a)]
      calc
        (a : Real) *
              abs ((k : Real) * ((T : Real) / (a : Real)) - (j : Real)) <=
            (a : Real) * (1 / ((n : Real) + 1)) :=
          mul_le_mul_of_nonneg_left herror (by positivity)
        _ = (a : Real) / ((n : Real) + 1) := by ring
        _ <= t := haDiv
    have hwBound : norm (anisotropicCongruenceVector T a s w) <= t := by
      rw [Prod.norm_def]
      exact max_le hfirst hsecond
    have hgcdPos : 0 < Int.gcd k j :=
      Int.gcd_pos_of_ne_zero_left j hk.ne'
    obtain ⟨g, p, q, hg, hcoprime, hkFactor, hjFactor⟩ :=
      Int.exists_gcd_one' hgcdPos
    let u : Int × Int := (p, q)
    have hwu : w = (g : Int) • u := by
      apply Prod.ext <;> simp [w, u, hkFactor, hjFactor, mul_comm]
    have hmap :
        anisotropicCongruenceVector T a s w =
          (g : Int) • anisotropicCongruenceVector T a s u := by
      rw [hwu, anisotropicCongruenceVector_zsmul]
    have hnormMap :
        norm (anisotropicCongruenceVector T a s w) =
          (g : Real) * norm (anisotropicCongruenceVector T a s u) := by
      rw [hmap, norm_zsmul Real]
      simp [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : Real) <= g)]
    have hu : Not (u = 0) := by
      intro hu0
      change (p, q) = (0, 0) at hu0
      injection hu0 with hp hq
      simp [hp, hq] at hcoprime
    have huPos : 0 < norm (anisotropicCongruenceVector T a s u) := by
      rw [norm_pos_iff]
      exact (anisotropicCongruenceVector_eq_zero_iff T a s ha hs u).not.mpr hu
    have huLeW :
        norm (anisotropicCongruenceVector T a s u) <=
          norm (anisotropicCongruenceVector T a s w) := by
      rw [hnormMap]
      have hgOne : (1 : Real) <= g := by exact_mod_cast hg
      nlinarith [norm_nonneg (anisotropicCongruenceVector T a s u)]
    refine ⟨u, hcoprime, huPos, ?_⟩
    simpa only [t] using huLeW.trans hwBound

end PrimesRestrictedDigits
