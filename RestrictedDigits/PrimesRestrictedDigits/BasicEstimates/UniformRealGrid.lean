import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-! # UniformRealGrid -/

namespace PrimesRestrictedDigits

noncomputable section

def uniformRealGridLower {n : Nat}
    (a b : Real) (i : Fin n) : Real :=
  a + (b - a) * (((i : Nat) : Real) / n)

def uniformRealGridUpper {n : Nat}
    (a b : Real) (i : Fin n) : Real :=
  a + (b - a) * ((((i : Nat) : Real) + 1) / n)

theorem uniformRealGrid_bounds
    {a b : Real} {n : Nat} (hn : 0 < n) (hab : a <= b) (i : Fin n) :
    a <= uniformRealGridLower a b i /\
    uniformRealGridLower a b i <= uniformRealGridUpper a b i /\
    uniformRealGridUpper a b i <= b := by
  let w : Real := (b - a) / n
  have hnReal : (0 : Real) < n := Nat.cast_pos.mpr hn
  have hw : 0 ≤ w := div_nonneg (sub_nonneg.mpr hab) hnReal.le
  have hcountWidth : (n : Real) * w = b - a := by
    dsimp only [w]
    exact mul_div_cancel₀ (b - a) hnReal.ne'
  have hLower : uniformRealGridLower a b i = a + (i : Nat) * w := by
    simp only [uniformRealGridLower]
    dsimp only [w]
    ring
  have hUpper : uniformRealGridUpper a b i =
      a + (((i : Nat) : Real) + 1) * w := by
    simp only [uniformRealGridUpper]
    dsimp only [w]
    ring
  have hiSucc : (i : Nat) + 1 ≤ n := Nat.succ_le_iff.mpr i.isLt
  have hiSuccReal : ((i : Nat) : Real) + 1 ≤ (n : Real) := by
    have hcast : (((i : Nat) + 1 : Nat) : Real) ≤ (n : Real) :=
      Nat.cast_le.mpr hiSucc
    simpa using hcast
  rw [hLower, hUpper]
  refine ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hw), ?_, ?_⟩
  · have hiStep : ((i : Nat) : Real) ≤ ((i : Nat) : Real) + 1 := by
      linarith
    have hproduct := mul_le_mul_of_nonneg_right hiStep hw
    linarith
  · have hproduct := mul_le_mul_of_nonneg_right hiSuccReal hw
    rw [hcountWidth] at hproduct
    linarith

theorem exists_uniformRealGrid_cell
    {a b x : Real} {n : Nat} (hn : 0 < n) (hab : a < b)
    (hax : a <= x) (hxb : x <= b) :
    exists i : Fin n,
      uniformRealGridLower a b i <= x /\
      x <= uniformRealGridUpper a b i := by
  let w : Real := (b - a) / n
  have hnReal : (0 : Real) < n := Nat.cast_pos.mpr hn
  have hw : 0 < w := div_pos (sub_pos.mpr hab) hnReal
  have hcountWidth : (n : Real) * w = b - a := by
    dsimp only [w]
    exact mul_div_cancel₀ (b - a) hnReal.ne'
  rcases eq_or_lt_of_le hxb with hxbEq | hxb'
  · let i : Fin n := ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩
    subst x
    have hbnds := uniformRealGrid_bounds hn hab.le i
    refine ⟨i, hbnds.2.1.trans hbnds.2.2, ?_⟩
    have hlastNat : n - 1 + 1 = n := Nat.sub_add_cancel hn
    have hlastReal : (((n - 1 : Nat) : Real) + 1) = (n : Real) := by
      have hcast := congrArg (fun k : Nat ↦ (k : Real)) hlastNat
      simpa using hcast
    have hUpper : uniformRealGridUpper a b i =
        a + (((n - 1 : Nat) : Real) + 1) * w := by
      simp only [uniformRealGridUpper]
      dsimp only [i, w]
      ring
    rw [hUpper, hlastReal, hcountWidth]
    linarith
  · let y : Real := x - a
    let j : Nat := Nat.floor (y / w)
    have hy : 0 ≤ y := sub_nonneg.mpr hax
    have hratioNonneg : 0 ≤ y / w := div_nonneg hy hw.le
    have hratio : y / w < (n : Real) := by
      rw [div_lt_iff₀ hw, hcountWidth]
      dsimp only [y]
      linarith
    have hj : j < n := (Nat.floor_lt hratioNonneg).mpr hratio
    let i : Fin n := ⟨j, hj⟩
    refine ⟨i, ?_, ?_⟩
    · have hfloor := Nat.floor_le hratioNonneg
      have hmul := mul_le_mul_of_nonneg_right hfloor hw.le
      have hLower : uniformRealGridLower a b i = a + (j : Real) * w := by
        simp only [uniformRealGridLower]
        dsimp only [i, w]
        ring
      calc
        uniformRealGridLower a b i = a + (j : Real) * w := hLower
        _ ≤ a + (y / w) * w := by linarith
        _ = x := by
          rw [div_mul_cancel₀ _ hw.ne']
          dsimp only [y]
          ring
    · have hfloor := Nat.lt_floor_add_one (y / w)
      have hmul := mul_lt_mul_of_pos_right hfloor hw
      have hUpper : uniformRealGridUpper a b i =
          a + ((j : Real) + 1) * w := by
        simp only [uniformRealGridUpper]
        dsimp only [i, w]
        ring
      apply le_of_lt
      calc
        x = a + (y / w) * w := by
          rw [div_mul_cancel₀ _ hw.ne']
          dsimp only [y]
          ring
        _ < a + ((j : Real) + 1) * w := by linarith
        _ = uniformRealGridUpper a b i := hUpper.symm

theorem uniformRealGridLower_lt_upper
    {a b : Real} {n : Nat} (hn : 0 < n) (hab : a < b) (i : Fin n) :
    uniformRealGridLower a b i < uniformRealGridUpper a b i := by
  let w : Real := (b - a) / n
  have hnReal : (0 : Real) < n := Nat.cast_pos.mpr hn
  have hw : 0 < w := div_pos (sub_pos.mpr hab) hnReal
  have hLower : uniformRealGridLower a b i = a + (i : Nat) * w := by
    simp only [uniformRealGridLower]
    dsimp only [w]
    ring
  have hUpper : uniformRealGridUpper a b i =
      a + (((i : Nat) : Real) + 1) * w := by
    simp only [uniformRealGridUpper]
    dsimp only [w]
    ring
  rw [hLower, hUpper]
  have hiStep : ((i : Nat) : Real) < ((i : Nat) : Real) + 1 := by
    linarith
  have hproduct := mul_lt_mul_of_pos_right hiStep hw
  linarith

end

end PrimesRestrictedDigits
