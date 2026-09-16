import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import PrimesRestrictedDigits.MajorArcs.Partition

/-!
# Cardinality bounds for the canonical major arcs

This proves the exact polynomial overcounts. They are the elementary finite-set inputs behind
the major-arc cardinality estimates on pp. 186, 188--189 of `MAYNARD-PRD-PUBLISHED`.
-/

namespace PrimesRestrictedDigits

private noncomputable def majorArcRationalFiber
    (X : Nat) (Q : Real) (r : Rat) : Finset Nat :=
  by classical exact
    (Finset.range X).filter fun a => majorArcRationalApproximation X a Q r

theorem majorArcRationalCarrier_card_le (N : Nat) :
    (majorArcRationalCarrier N).card <= N * (3 * N + 1) := by
  classical
  have hnum :
      (Finset.Icc (-(N : Int)) (2 * (N : Int))).card = 3 * N + 1 := by
    rw [Int.card_Icc]
    have hequal :
        2 * (N : Int) + 1 - (-(N : Int)) = ((3 * N + 1 : Nat) : Int) := by
      omega
    rw [hequal, Int.toNat_natCast]
  have hden : (Finset.Icc 1 N).card = N := by
    rw [Nat.card_Icc]
    omega
  calc
    (majorArcRationalCarrier N).card <=
        ((Finset.Icc (-(N : Int)) (2 * (N : Int))).product
          (Finset.Icc 1 N)).card := by
      exact Finset.card_image_le
    _ = (Finset.Icc (-(N : Int)) (2 * (N : Int))).card *
          (Finset.Icc 1 N).card := by
      rw [Finset.product_eq_sprod, Finset.card_product]
    _ = N * (3 * N + 1) := by
      rw [hnum, hden, Nat.mul_comm]

theorem majorArcClassOneFrequencies_subset_raw (X : Nat) (Q : Real) :
    majorArcClassOneFrequencies X Q <= majorArcRawFrequencies X Q := by
  classical
  intro a ha
  simp only [majorArcClassOneFrequencies, majorArcRawFrequencies,
    Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, (majorArcRawApproximation_iff_classes X a Q).2
    (Or.inl ha.2)⟩

theorem majorArcClassTwoFrequencies_subset_raw (X : Nat) (Q : Real) :
    majorArcClassTwoFrequencies X Q <= majorArcRawFrequencies X Q := by
  classical
  intro a ha
  simp only [majorArcClassTwoFrequencies, majorArcRawFrequencies,
    Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, (majorArcRawApproximation_iff_classes X a Q).2
    (Or.inr (Or.inl ha.2))⟩

theorem majorArcClassThreeFrequencies_subset_raw (X : Nat) (Q : Real) :
    majorArcClassThreeFrequencies X Q <= majorArcRawFrequencies X Q := by
  classical
  intro a ha
  simp only [majorArcClassThreeFrequencies, majorArcRawFrequencies,
    Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, (majorArcRawApproximation_iff_classes X a Q).2
    (Or.inr (Or.inr ha.2))⟩

private theorem majorArcRationalFiber_card_le
    {X : Nat} {Q : Real} (hX : 0 < X) (r : Rat) :
    (majorArcRationalFiber X Q r).card <= 2 * Nat.ceil Q + 1 := by
  classical
  let fiber := majorArcRationalFiber X Q r
  change fiber.card <= 2 * Nat.ceil Q + 1
  -- Anchor at the least frequency to keep both closed endpoints exact.
  by_cases hfiber : fiber.Nonempty
  · let m := fiber.min' hfiber
    have hm : m ∈ fiber := fiber.min'_mem hfiber
    have hmApprox : majorArcRationalApproximation X m Q r := by
      exact (Finset.mem_filter.mp hm).2
    have hmaps : Set.MapsTo (fun a : Nat => a - m) (fiber : Set Nat)
        (Finset.Icc 0 (2 * Nat.ceil Q) : Set Nat) := by
      intro a ha
      change a ∈ fiber at ha
      have hma : m <= a := fiber.min'_le a ha
      have haApprox : majorArcRationalApproximation X a Q r := by
        exact (Finset.mem_filter.mp ha).2
      have hXReal : (0 : Real) < X := by
        exact_mod_cast hX
      have haUpper := (abs_le.mp haApprox.1).2
      have hmLower := (abs_le.mp hmApprox.1).1
      have hquotient :
          (a : Real) / X - (m : Real) / X <= 2 * (Q / X) := by
        linarith
      have hscaled := mul_le_mul_of_nonneg_right hquotient hXReal.le
      have hdifference : (a : Real) - (m : Real) <= 2 * Q := by
        calc
          (a : Real) - (m : Real) =
              ((a : Real) / X - (m : Real) / X) * X := by
            field_simp [hXReal.ne']
          _ <= (2 * (Q / X)) * X := hscaled
          _ = 2 * Q := by
            field_simp [hXReal.ne']
      have hceil : Q <= (Nat.ceil Q : Real) := Nat.le_ceil Q
      have hsubReal : ((a - m : Nat) : Real) <= (2 * Nat.ceil Q : Nat) := by
        rw [Nat.cast_sub hma]
        exact hdifference.trans (by
          norm_num only [Nat.cast_mul, Nat.cast_ofNat]
          linarith)
      have hsub : a - m <= 2 * Nat.ceil Q := by
        exact_mod_cast hsubReal
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, hsub⟩
    have hinjective :
        (fiber : Set Nat).InjOn (fun a : Nat => a - m) := by
      intro a ha b hb hequal
      change a ∈ fiber at ha
      change b ∈ fiber at hb
      have hma : m <= a := fiber.min'_le a ha
      have hmb : m <= b := fiber.min'_le b hb
      change a - m = b - m at hequal
      exact (tsub_left_inj hma hmb).mp hequal
    calc
      fiber.card <= (Finset.Icc 0 (2 * Nat.ceil Q)).card :=
        Finset.card_le_card_of_injOn (fun a : Nat => a - m) hmaps hinjective
      _ = 2 * Nat.ceil Q + 1 := by
        rw [Nat.card_Icc]
        omega
  · have hempty : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hfiber
    simp [hempty]

private theorem majorArcRawFrequencies_eq_biUnion
    {X : Nat} {Q : Real} (hX : 0 < X) (hQX : Q <= (X : Real)) :
    majorArcRawFrequencies X Q =
      (majorArcRationalCarrier (Nat.ceil Q)).biUnion
        (majorArcRationalFiber X Q) := by
  classical
  apply Finset.ext
  intro a
  simp only [majorArcRawFrequencies, Finset.mem_filter, Finset.mem_range,
    Finset.mem_biUnion]
  constructor
  · rintro ⟨ha, r, hr⟩
    refine ⟨r, majorArcRationalCarrier_complete hX hQX ha hr, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, hr⟩
  · rintro ⟨r, _, hr⟩
    exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hr).1, r,
      (Finset.mem_filter.mp hr).2⟩

theorem majorArcRawFrequencies_card_le
    {X : Nat} {Q : Real} (hX : 0 < X) (hQX : Q <= (X : Real)) :
    (majorArcRawFrequencies X Q).card <=
      Nat.ceil Q * (3 * Nat.ceil Q + 1) * (2 * Nat.ceil Q + 1) := by
  classical
  rw [majorArcRawFrequencies_eq_biUnion hX hQX]
  calc
    ((majorArcRationalCarrier (Nat.ceil Q)).biUnion
        (majorArcRationalFiber X Q)).card <=
        (majorArcRationalCarrier (Nat.ceil Q)).card *
          (2 * Nat.ceil Q + 1) := by
      exact Finset.card_biUnion_le_card_mul _ _ _ fun r _ =>
        majorArcRationalFiber_card_le hX r
    _ <= (Nat.ceil Q * (3 * Nat.ceil Q + 1)) *
          (2 * Nat.ceil Q + 1) := by
      exact Nat.mul_le_mul_right _ (majorArcRationalCarrier_card_le (Nat.ceil Q))
    _ = Nat.ceil Q * (3 * Nat.ceil Q + 1) *
          (2 * Nat.ceil Q + 1) := rfl

theorem majorArcClassOneFrequencies_card_le
    {X : Nat} {Q : Real} (hX : 0 < X) (hQX : Q <= (X : Real)) :
    (majorArcClassOneFrequencies X Q).card <=
      Nat.ceil Q * (3 * Nat.ceil Q + 1) * (2 * Nat.ceil Q + 1) :=
  (Finset.card_le_card (majorArcClassOneFrequencies_subset_raw X Q)).trans
    (majorArcRawFrequencies_card_le hX hQX)

theorem majorArcClassTwoFrequencies_card_le
    {X : Nat} {Q : Real} (hX : 0 < X) (hQX : Q <= (X : Real)) :
    (majorArcClassTwoFrequencies X Q).card <=
      Nat.ceil Q * (3 * Nat.ceil Q + 1) * (2 * Nat.ceil Q + 1) :=
  (Finset.card_le_card (majorArcClassTwoFrequencies_subset_raw X Q)).trans
    (majorArcRawFrequencies_card_le hX hQX)

theorem majorArcClassThreeFrequencies_card_le
    {X : Nat} {Q : Real} (hX : 0 < X) (hQX : Q <= (X : Real)) :
    (majorArcClassThreeFrequencies X Q).card <=
      Nat.ceil Q * (3 * Nat.ceil Q + 1) := by
  classical
  let ratio : Nat -> Rat := fun a => (a : Rat) / (X : Rat)
  have hmaps : Set.MapsTo ratio
      (majorArcClassThreeFrequencies X Q : Set Nat)
      (majorArcRationalCarrier (Nat.ceil Q) : Set Rat) := by
    intro a ha
    change a ∈ majorArcClassThreeFrequencies X Q at ha
    rw [majorArcClassThreeFrequencies, Finset.mem_filter] at ha
    rcases ha.2 with ⟨r, hr, _, hequal⟩
    have hcarrier := majorArcRationalCarrier_complete hX hQX
      (Finset.mem_range.mp ha.1) hr
    simpa [ratio, ← hequal] using hcarrier
  have hinjective :
      (majorArcClassThreeFrequencies X Q : Set Nat).InjOn ratio := by
    intro a _ b _ hequal
    have hXNonzero : (X : Rat) ≠ 0 := by
      exact_mod_cast hX.ne'
    have habRat : (a : Rat) = (b : Rat) := by
      exact (div_left_inj' hXNonzero).mp hequal
    exact_mod_cast habRat
  exact (Finset.card_le_card_of_injOn ratio hmaps hinjective).trans
    (majorArcRationalCarrier_card_le (Nat.ceil Q))

end PrimesRestrictedDigits
