import PrimesRestrictedDigits.Fourier.HybridLatticeCarrier
import PrimesRestrictedDigits.Fourier.ContinuousTransformPeriodicity
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic.GCongr

/-!
# Residue fibers of aligned integer windows

The dense branch groups aligned numerators modulo the decimal grid. This module records the
exact interval count and periodicity bridges.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

private theorem card_Ico_filter_modEq_lt_rat
    (a b r v : Int) (hr : 0 < r) (hab : a <= b) :
    ((((Finset.Ico a b).filter fun x => Int.ModEq r x v).card : Int) : Rat) <
      ((b - a : Int) : Rat) / (r : Rat) + 1 := by
  let A : Rat := ((b - v : Int) : Rat) / (r : Rat)
  let B : Rat := ((a - v : Int) : Rat) / (r : Rat)
  let Q : Rat := ((b - a : Int) : Rat) / (r : Rat)
  have hAB : A = Q + B := by
    dsimp [A, B, Q]
    field_simp [hr.ne']
    push_cast
    ring
  have hceil : Int.ceil A - Int.ceil B <= Int.ceil Q := by
    have h := Int.ceil_add_le Q B
    rw [hAB]
    linarith
  have hQ : 0 <= Q := by
    dsimp [Q]
    positivity
  have hmax : max (Int.ceil A - Int.ceil B) 0 <= Int.ceil Q :=
    max_le hceil (Int.ceil_nonneg hQ)
  have hcard :
      (((Finset.Ico a b).filter fun x => Int.ModEq r x v).card : Int) =
        max (Int.ceil A - Int.ceil B) 0 := by
    simpa [A, B] using Int.Ico_filter_modEq_card a b hr v
  calc
    ((((Finset.Ico a b).filter fun x => Int.ModEq r x v).card : Int) : Rat) <=
        ((Int.ceil Q : Int) : Rat) := by exact_mod_cast hcard.symm ▸ hmax
    _ < Q + 1 := Int.ceil_lt_add_one Q
    _ = ((b - a : Int) : Rat) / (r : Rat) + 1 := rfl

noncomputable def alignedGridResidueFiber
    (length : Nat) (E x : Real) (r : Int) : Finset Int :=
  (alignedGridWindow length E x).filter fun b =>
    Int.ModEq (10 ^ length : Int) b r

theorem mem_alignedGridResidueFiber_iff
    {length : Nat} {E x : Real} {r b : Int} :
    b ∈ alignedGridResidueFiber length E x r ↔
      b ∈ alignedGridWindow length E x ∧
        Int.ModEq (10 ^ length : Int) b r := by
  simp [alignedGridResidueFiber]

theorem alignedGridResidueFiber_card_lt
    (length : Nat) (E x : Real) (r : Int) :
    ((alignedGridResidueFiber length E x r).card : Real) <
      2 + (2 * (Nat.ceil E : Real) + 1) /
        ((10 ^ length : Nat) : Real) := by
  let B : Int := Nat.ceil E
  let N : Int := ((10 ^ length : Nat) : Int)
  have hN : 0 < N := by
    dsimp [N]
    positivity
  let ambient : Finset Int := Finset.Ico (-B) (N + B + 1)
  have hsubset : alignedGridResidueFiber length E x r ⊆
      ambient.filter fun b => Int.ModEq N b r := by
    intro b hb
    have hb' := mem_alignedGridResidueFiber_iff.mp hb
    have hwindow := mem_alignedGridWindow_iff.mp hb'.1
    apply Finset.mem_filter.mpr
    constructor
    · dsimp [ambient, B, N] at hwindow ⊢
      rw [Finset.mem_Ico]
      omega
    · exact hb'.2
  have hcard := Finset.card_le_card hsubset
  have hrat := card_Ico_filter_modEq_lt_rat
    (-B) (N + B + 1) N r hN (by omega)
  have hreal := (Rat.cast_lt (K := Real)).mpr hrat
  have hcast :
      (((ambient.filter (fun b => Int.ModEq N b r)).card : Nat) : Real) <
        2 + (2 * (B : Real) + 1) / (N : Real) := by
    dsimp [ambient] at hreal ⊢
    norm_num [Rat.cast_natCast, Rat.cast_add, Rat.cast_sub,
      Rat.cast_div, Rat.cast_ofNat, Int.cast_add, Int.cast_neg] at hreal ⊢
    field_simp [show (N : Real) ≠ 0 by exact_mod_cast hN.ne'] at hreal
    have hrewrite :
        2 + (2 * (B : Real) + 1) / (N : Real) =
          (2 * (N : Real) + (2 * (B : Real) + 1)) / (N : Real) := by
      field_simp [show (N : Real) ≠ 0 by exact_mod_cast hN.ne']
    rw [hrewrite]
    apply (lt_div_iff₀ (show (0 : Real) < N by exact_mod_cast hN)).mpr
    nlinarith [hreal]
  have hcardReal :
      ((alignedGridResidueFiber length E x r).card : Real) <=
        ((ambient.filter (fun b => Int.ModEq N b r)).card : Real) := by
    exact_mod_cast hcard
  calc
    ((alignedGridResidueFiber length E x r).card : Real) <=
        ((ambient.filter (fun b => Int.ModEq N b r)).card : Real) := hcardReal
    _ < 2 + (2 * (B : Real) + 1) / (N : Real) := hcast
    _ = 2 + (2 * (Nat.ceil E : Real) + 1) /
        ((10 ^ length : Nat) : Real) := by
      dsimp [B, N]
      norm_num

theorem normalizedPaddedDigitFourierMagnitudeAt_alignedResidue_eq
    (digit : Fin 10) (length : Nat) (b : Int) :
    normalizedPaddedDigitFourierMagnitudeAt digit length
        ((b : Real) / ((10 ^ length : Nat) : Real)) =
      normalizedPaddedDigitFourierMagnitudeAt digit length
        ((b % (10 ^ length : Int) : Real) /
          ((10 ^ length : Nat) : Real)) := by
  let N : Int := ((10 ^ length : Nat) : Int)
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hdecomp := Int.emod_add_ediv_mul b N
  have hbEq : b = b % N + N * (b / N) := by
    calc
      b = b % N + (b / N) * N := hdecomp.symm
      _ = b % N + N * (b / N) := by ring
  have hbCast : (b : Real) =
      (b % N : Real) + (N : Real) * ((b / N : Int) : Real) := by
    exact_mod_cast hbEq
  have harg :
      (b : Real) / (N : Real) =
        (b % N : Real) / (N : Real) + ((b / N : Int) : Real) := by
    rw [hbCast]
    field_simp [hN.ne']
  have hperiod := normalizedPaddedDigitFourierMagnitudeAt_periodic digit length
  have hshift := hperiod.int_mul (b / N)
    ((b % N : Real) / (N : Real))
  change normalizedPaddedDigitFourierMagnitudeAt digit length
      ((b : Real) / (N : Real)) =
    normalizedPaddedDigitFourierMagnitudeAt digit length
      ((b % N : Real) / (N : Real))
  calc
    _ = normalizedPaddedDigitFourierMagnitudeAt digit length
        ((b % N : Real) / (N : Real) + ((b / N : Int) : Real)) := by rw [harg]
    _ = _ := by simpa using hshift

/-- Regroup one aligned-grid sum by its canonical residues modulo the decimal
grid, retaining every lift as a fiber cardinality. -/
theorem alignedGridSum_eq_sum_residueFibers
    (digit : Fin 10) (length : Nat) (E x : Real) :
    alignedGridSum digit length E x =
      ∑ r ∈ Finset.Ico (0 : Int) (10 ^ length : Int),
        (alignedGridResidueFiber length E x r).card *
          normalizedPaddedDigitFourierMagnitudeAt digit length
            ((r : Real) / ((10 ^ length : Nat) : Real)) := by
  classical
  let window := alignedGridWindow length E x
  let residues := Finset.Ico (0 : Int) (10 ^ length : Int)
  let residue : Int -> Int := fun b => b % (10 ^ length : Int)
  let value : Int -> Real := fun b =>
    normalizedPaddedDigitFourierMagnitudeAt digit length
      ((b : Real) / ((10 ^ length : Nat) : Real))
  have hN : (0 : Int) < (10 ^ length : Int) := by positivity
  have hresidueMem (b : Int) : residue b ∈ residues := by
    dsimp [residue, residues]
    rw [Finset.mem_Ico]
    exact ⟨Int.emod_nonneg _ hN.ne', Int.emod_lt_of_pos _ hN⟩
  have hfilterAll :
      window.filter (fun b => residue b ∈ residues) = window := by
    ext b
    simp only [Finset.mem_filter]
    tauto
  have hfiberwise := Finset.sum_fiberwise_eq_sum_filter
    window residues residue value
  rw [hfilterAll] at hfiberwise
  rw [alignedGridSum]
  change (∑ b ∈ window, value b) = _
  rw [← hfiberwise]
  apply Finset.sum_congr rfl
  intro r hr
  have hrData := Finset.mem_Ico.mp hr
  have hrMod : r % (10 ^ length : Int) = r :=
    Int.emod_eq_of_lt hrData.1 hrData.2
  have hfiber :
      window.filter (fun b => residue b = r) =
        alignedGridResidueFiber length E x r := by
    ext b
    simp only [Finset.mem_filter, mem_alignedGridResidueFiber_iff]
    dsimp [window, residue]
    rw [Int.ModEq, hrMod]
  rw [hfiber]
  calc
    (∑ b ∈ alignedGridResidueFiber length E x r, value b) =
        ∑ _b ∈ alignedGridResidueFiber length E x r,
          normalizedPaddedDigitFourierMagnitudeAt digit length
            ((r : Real) / ((10 ^ length : Nat) : Real)) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hbData := mem_alignedGridResidueFiber_iff.mp hb
      have hbMod : b % (10 ^ length : Int) = r := by
        rw [Int.ModEq] at hbData
        exact hbData.2.trans hrMod
      dsimp [value]
      rw [normalizedPaddedDigitFourierMagnitudeAt_alignedResidue_eq, hbMod]
    _ = (alignedGridResidueFiber length E x r).card *
        normalizedPaddedDigitFourierMagnitudeAt digit length
          ((r : Real) / ((10 ^ length : Nat) : Real)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]

end

end PrimesRestrictedDigits
