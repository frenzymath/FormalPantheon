import PrimesRestrictedDigits.ExceptionalMinorArcs.LineNormalizedCrossData
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Bounded coprime linear fibers

This makes the residue-class count behind equation `(15.4)` of `MAYNARD-PRD-PUBLISHED`, Lemma
15.2, pp. 211--212, exact. Closed endpoints and the factor-ten width are retained.
-/

namespace PrimesRestrictedDigits

/-- Bounded integer pairs solving `u' * x - u * y = b`. -/
noncomputable def lineCoprimeLinearPairFiber
    (V : Real) (u uPrime b : Int) : Finset (Prod Int Int) :=
  ((lineCoefficientBox V).product (lineCoefficientBox V)).filter fun p =>
    uPrime * p.1 - u * p.2 = b

@[simp]
theorem mem_lineCoprimeLinearPairFiber
    {V : Real} {u uPrime b : Int} {p : Prod Int Int} :
    p ∈ lineCoprimeLinearPairFiber V u uPrime b ↔
      p.1 ∈ lineCoefficientBox V ∧
        p.2 ∈ lineCoefficientBox V ∧
        uPrime * p.1 - u * p.2 = b := by
  classical
  simp [lineCoprimeLinearPairFiber, and_assoc]

private theorem card_Ico_filter_modEq_lt_rat
    (a b r v : Int) (hr : 0 < r) (hab : a ≤ b) :
    ((((Finset.Ico a b).filter fun x => Int.ModEq r x v).card : Int) : Rat) <
      ((b - a : Int) : Rat) / (r : Rat) + 1 := by
  let A : Rat := ((b - v : Int) : Rat) / (r : Rat)
  let B : Rat := ((a - v : Int) : Rat) / (r : Rat)
  let Q : Rat := ((b - a : Int) : Rat) / (r : Rat)
  have hrRat : (0 : Rat) < (r : Rat) := by exact_mod_cast hr
  have hAB : A = Q + B := by
    dsimp [A, B, Q]
    field_simp [hr.ne']
    push_cast
    ring
  have hceil : Int.ceil A - Int.ceil B ≤ Int.ceil Q := by
    have h := Int.ceil_add_le Q B
    rw [hAB]
    linarith
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hmax : max (Int.ceil A - Int.ceil B) 0 ≤ Int.ceil Q :=
    max_le hceil (Int.ceil_nonneg hQ)
  have hcard :
      (((Finset.Ico a b).filter fun x => Int.ModEq r x v).card : Int) =
        max (Int.ceil A - Int.ceil B) 0 := by
    simpa [A, B] using Int.Ico_filter_modEq_card a b hr v
  calc
    ((((Finset.Ico a b).filter fun x => Int.ModEq r x v).card : Int) : Rat) ≤
        ((Int.ceil Q : Int) : Rat) := by exact_mod_cast hcard.symm ▸ hmax
    _ < Q + 1 := Int.ceil_lt_add_one Q
    _ = ((b - a : Int) : Rat) / (r : Rat) + 1 := rfl

private theorem card_Ico_filter_modEq_le_natCeil
    (a b r v : Int) (hr : 0 < r) (hab : a ≤ b) :
    ((Finset.Ico a b).filter fun x => Int.ModEq r x v).card ≤
      Nat.ceil (((b - a : Int) : Rat) / (r : Rat)) := by
  let A : Rat := ((b - v : Int) : Rat) / (r : Rat)
  let B : Rat := ((a - v : Int) : Rat) / (r : Rat)
  let Q : Rat := ((b - a : Int) : Rat) / (r : Rat)
  have hAB : A = Q + B := by
    dsimp [A, B, Q]
    field_simp [hr.ne']
    push_cast
    ring
  have hceil : Int.ceil A - Int.ceil B ≤ Int.ceil Q := by
    have h := Int.ceil_add_le Q B
    rw [hAB]
    linarith
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hmax : max (Int.ceil A - Int.ceil B) 0 ≤ Int.ceil Q :=
    max_le hceil (Int.ceil_nonneg hQ)
  have hcard :
      (((Finset.Ico a b).filter fun x => Int.ModEq r x v).card : Int) =
        max (Int.ceil A - Int.ceil B) 0 := by
    simpa [A, B] using Int.Ico_filter_modEq_card a b hr v
  have hInt :
      (((Finset.Ico a b).filter fun x => Int.ModEq r x v).card : Int) ≤
        Int.ceil Q := hcard.trans_le hmax
  have hNatCeil : ((Nat.ceil Q : Nat) : Int) = Int.ceil Q :=
    Int.natCast_ceil_eq_ceil hQ
  rw [← hNatCeil] at hInt
  have hNat :
      ((Finset.Ico a b).filter fun x => Int.ModEq r x v).card ≤
        Nat.ceil Q := by exact_mod_cast hInt
  simpa only [Q] using hNat

private theorem card_Icc_filter_modEq_le_natCeil
    (N : Nat) (u v : Int) (hu : u ≠ 0) :
    ((Finset.Icc (-(N : Int)) (N : Int)).filter fun x =>
      Int.ModEq (u.natAbs : Int) x v).card ≤
      Nat.ceil ((2 * (N : Rat) + 1) / (u.natAbs : Rat)) := by
  have hmNat : 0 < u.natAbs := Int.natAbs_pos.mpr hu
  have hmInt : 0 < (u.natAbs : Int) := by exact_mod_cast hmNat
  have h := card_Ico_filter_modEq_le_natCeil
    (-(N : Int)) ((N : Int) + 1) (u.natAbs : Int) v hmInt (by omega)
  have hinterval :
      Finset.Ico (-(N : Int)) ((N : Int) + 1) =
        Finset.Icc (-(N : Int)) (N : Int) := by
    ext x
    simp
  rw [hinterval] at h
  norm_num [Int.cast_sub, Int.cast_add, Int.cast_neg,
    Int.cast_natCast, Nat.cast_ofNat] at h ⊢
  ring_nf at h ⊢
  exact h

private theorem card_Icc_filter_modEq_lt_real
    (N : Nat) (u v : Int) (hu : u ≠ 0) :
    (((Finset.Icc (-(N : Int)) (N : Int)).filter fun x =>
        Int.ModEq (u.natAbs : Int) x v).card : Real) <
      (2 * (N : Real) + 1) / (u.natAbs : Real) + 1 := by
  have hmNat : 0 < u.natAbs := Int.natAbs_pos.mpr hu
  have hmInt : 0 < (u.natAbs : Int) := by exact_mod_cast hmNat
  have h := card_Ico_filter_modEq_lt_rat
    (-(N : Int)) ((N : Int) + 1) (u.natAbs : Int) v hmInt (by omega)
  have hinterval :
      Finset.Ico (-(N : Int)) ((N : Int) + 1) =
        Finset.Icc (-(N : Int)) (N : Int) := by
    ext x
    simp
  rw [hinterval] at h
  have hRat :
      ((((Finset.Icc (-(N : Int)) (N : Int)).filter fun x =>
          Int.ModEq (u.natAbs : Int) x v).card : Nat) : Rat) <
        (2 * (N : Rat) + 1) / (u.natAbs : Rat) + 1 := by
    norm_num [Int.cast_sub, Int.cast_add, Int.cast_neg,
      Int.cast_natCast, Nat.cast_ofNat] at h ⊢
    ring_nf at h ⊢
    exact h
  have hCast := (Rat.cast_lt (K := Real)).mpr hRat
  norm_num [Rat.cast_natCast, Rat.cast_add, Rat.cast_div,
    Rat.cast_ofNat] at hCast ⊢
  ring_nf at hCast ⊢
  exact hCast

private theorem lineCoprimeLinearPairFiber_mapsTo_residue
    (V : Real) (u uPrime b : Int)
    (hgcd : Int.gcd u uPrime = 1)
    {base : Prod Int Int}
    (hbase : base ∈ lineCoprimeLinearPairFiber V u uPrime b) :
    Set.MapsTo Prod.fst
      (lineCoprimeLinearPairFiber V u uPrime b : Set (Prod Int Int))
      (((Finset.Icc (-(Nat.floor V : Int)) (Nat.floor V : Int)).filter
        fun x => Int.ModEq (u.natAbs : Int) x base.1) : Set Int) := by
  intro p hp
  have hpData := mem_lineCoprimeLinearPairFiber.mp hp
  have hbaseData := mem_lineCoprimeLinearPairFiber.mp hbase
  apply Finset.mem_filter.mpr
  refine ⟨by simpa [lineCoefficientBox, integerCoordinateBox] using hpData.1, ?_⟩
  apply Int.modEq_natAbs.mpr
  rw [Int.modEq_iff_dvd]
  apply Int.dvd_of_dvd_mul_right_of_gcd_one
      (b := uPrime) (c := base.1 - p.1)
  · refine ⟨base.2 - p.2, ?_⟩
    linear_combination hbaseData.2.2 - hpData.2.2
  · simpa [Int.gcd_comm] using hgcd

private theorem lineCoprimeLinearPairFiber_fst_injOn
    (V : Real) (u uPrime b : Int) (hu : u ≠ 0) :
    Set.InjOn Prod.fst
      (lineCoprimeLinearPairFiber V u uPrime b : Set (Prod Int Int)) := by
  intro p hp q hq hpq
  apply Prod.ext
  · exact hpq
  · have hpData := mem_lineCoprimeLinearPairFiber.mp hp
    have hqData := mem_lineCoprimeLinearPairFiber.mp hq
    have hmul : u * p.2 = u * q.2 := by
      rw [hpq] at hpData
      linear_combination hqData.2.2 - hpData.2.2
    exact mul_left_cancel₀ hu hmul

/-- Exact natural ceiling bound for one coprime linear fiber. -/
theorem card_lineCoprimeLinearPairFiber_le
    (V : Real) (u uPrime b : Int) (hu : u ≠ 0)
    (hgcd : Int.gcd u uPrime = 1) :
    (lineCoprimeLinearPairFiber V u uPrime b).card ≤
      Nat.ceil ((2 * (Nat.floor V : Rat) + 1) /
        (u.natAbs : Rat)) := by
  classical
  let S := lineCoprimeLinearPairFiber V u uPrime b
  by_cases hS : S.Nonempty
  · let base := hS.choose
    have hbase : base ∈ S := hS.choose_spec
    let target :=
      (Finset.Icc (-(Nat.floor V : Int)) (Nat.floor V : Int)).filter
        fun x => Int.ModEq (u.natAbs : Int) x base.1
    have hcard : S.card ≤ target.card :=
      Finset.card_le_card_of_injOn Prod.fst
        (lineCoprimeLinearPairFiber_mapsTo_residue
          V u uPrime b hgcd hbase)
        (lineCoprimeLinearPairFiber_fst_injOn V u uPrime b hu)
    exact hcard.trans
      (card_Icc_filter_modEq_le_natCeil (Nat.floor V) u base.1 hu)
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [S, hEmpty]

/-- Real interval form of the exact residue count. -/
theorem card_lineCoprimeLinearPairFiber_real_lt
    (V : Real) (u uPrime b : Int) (hV : 0 ≤ V) (hu : u ≠ 0)
    (hgcd : Int.gcd u uPrime = 1) :
    ((lineCoprimeLinearPairFiber V u uPrime b).card : Real) <
      (2 * V + 1) / abs (u : Real) + 1 := by
  classical
  let S := lineCoprimeLinearPairFiber V u uPrime b
  have huAbs : 0 < abs (u : Real) := abs_pos.mpr (by exact_mod_cast hu)
  by_cases hS : S.Nonempty
  · let base := hS.choose
    have hbase : base ∈ S := hS.choose_spec
    let target :=
      (Finset.Icc (-(Nat.floor V : Int)) (Nat.floor V : Int)).filter
        fun x => Int.ModEq (u.natAbs : Int) x base.1
    have hcard : (S.card : Real) ≤ target.card := by
      dsimp only [S, target]
      exact_mod_cast Finset.card_le_card_of_injOn Prod.fst
        (lineCoprimeLinearPairFiber_mapsTo_residue
          V u uPrime b hgcd hbase)
        (lineCoprimeLinearPairFiber_fst_injOn V u uPrime b hu)
    have htarget :=
      card_Icc_filter_modEq_lt_real (Nat.floor V) u base.1 hu
    have hfloor : (Nat.floor V : Real) ≤ V := Nat.floor_le hV
    have hdenom : (u.natAbs : Real) = abs (u : Real) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    calc
      (S.card : Real) ≤ (target.card : Real) := hcard
      _ < (2 * (Nat.floor V : Real) + 1) /
          (u.natAbs : Real) + 1 := htarget
      _ ≤ (2 * V + 1) / abs (u : Real) + 1 := by
        rw [hdenom]
        gcongr
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change (S.card : Real) < (2 * V + 1) / abs (u : Real) + 1
    rw [hEmpty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- Factor-ten form used twice in the small primitive-height count. -/
theorem card_lineCoprimeLinearPairFiber_real_le_scale
    (V U : Real) (u uPrime b : Int) (hV : 1 ≤ V) (hU : 0 < U)
    (hu : u ≠ 0) (hgcd : Int.gcd u uPrime = 1)
    (huLower : U / 10 < (u.natAbs : Real))
    (huUpper : (u.natAbs : Real) ≤ V) :
    ((lineCoprimeLinearPairFiber V u uPrime b).card : Real) ≤
      40 * V / U := by
  have huAbs : 0 < abs (u : Real) := abs_pos.mpr (by exact_mod_cast hu)
  have hdenom : (u.natAbs : Real) = abs (u : Real) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have huBand : U / 10 < abs (u : Real) := by simpa [hdenom] using huLower
  have huBound : abs (u : Real) ≤ V := by simpa [hdenom] using huUpper
  have huNat : 1 ≤ u.natAbs :=
    (Nat.one_le_iff_ne_zero).mpr (Int.natAbs_ne_zero.mpr hu)
  have huOne : (1 : Real) ≤ abs (u : Real) := by
    rw [← hdenom]
    exact_mod_cast huNat
  have hcount := card_lineCoprimeLinearPairFiber_real_lt
    V u uPrime b (zero_le_one.trans hV) hu hgcd
  have hcoarse : (2 * V + 1) / abs (u : Real) + 1 ≤
      4 * V / abs (u : Real) := by
    rw [show (2 * V + 1) / abs (u : Real) + 1 =
      (2 * V + 1 + abs (u : Real)) / abs (u : Real) by
        field_simp [huAbs.ne']]
    rw [div_le_div_iff_of_pos_right huAbs]
    nlinarith
  have hUAbs : U < 10 * abs (u : Real) := by nlinarith
  have hscale : 4 * V / abs (u : Real) < 40 * V / U := by
    rw [div_lt_iff₀ huAbs]
    rw [show 40 * V / U * abs (u : Real) =
      (40 * V * abs (u : Real)) / U by ring]
    rw [lt_div_iff₀ hU]
    calc
      4 * V * U < 4 * V * (10 * abs (u : Real)) :=
        mul_lt_mul_of_pos_left hUAbs (by positivity)
      _ = 40 * V * abs (u : Real) := by ring
  exact (hcount.trans_le hcoarse).trans hscale |>.le

end PrimesRestrictedDigits
