import PrimesRestrictedDigits.SieveAsymptotics.RosserPartialRecurrence

/-!
# Complete finite Rosser failure recurrences

These are the all-rank forms of Iwaniec's finite recurrences (4.4)--(4.6). The proof keeps the
strict carrier and the upper cubic head gate visible while extending inner finite rank sums by
the existing length-vanishing lemmas. See `IWANIEC-ROSSER-SIEVE-1980`, pp. 180--181.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem sieveFactorsBelow_length_le_of_lt
    (P : Finset Nat) {p z : Real} (hpz : p < z) :
    (sieveFactorsBelow P p).length <=
      (sieveFactorsBelow P z).length := by
  have hsubset : P.filter (fun q : Nat => (q : Real) < p) ⊆
      P.filter (fun q : Nat => (q : Real) < z) := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨
      (Finset.mem_filter.mp hq).1,
      (Finset.mem_filter.mp hq).2.trans hpz⟩
  have hcard := Finset.card_le_card hsubset
  simpa only [sieveFactorsBelow, Finset.length_sort] using hcard

private theorem upperRosserFailurePartialSum_eq_full_of_length_le
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (_hprime : ∀ p ∈ P, p.Prime)
    (hR : (sieveFactorsBelow P z).length <= R) :
    upperRosserFailurePartialSum P nu level z R =
      upperRosserFailureSum P nu level z := by
  rw [upperRosserFailurePartialSum, upperRosserFailureSum]
  have hsubset :
      Finset.range (((sieveFactorsBelow P z).length + 1) / 2) ⊆
        Finset.range (R + 1) := by
    intro r hr
    simp only [Finset.mem_range] at hr ⊢
    omega
  apply (Finset.sum_subset hsubset ?_).symm
  intro r hr hrnot
  apply upperRosserFailureSumAtRank_eq_zero_of_length_lt
  simp only [Finset.mem_range] at hr hrnot
  omega

private theorem lowerRosserFailurePartialSum_eq_full_of_length_le
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (_hprime : ∀ p ∈ P, p.Prime)
    (hR : (sieveFactorsBelow P z).length <= R) :
    lowerRosserFailurePartialSum P nu level z R =
      lowerRosserFailureSum P nu level z := by
  rw [lowerRosserFailurePartialSum, lowerRosserFailureSum]
  have hsubset :
      Finset.Icc 1 ((sieveFactorsBelow P z).length / 2) ⊆
        Finset.Icc 1 R := by
    intro r hr
    simp only [Finset.mem_Icc] at hr ⊢
    omega
  apply (Finset.sum_subset hsubset ?_).symm
  intro r hr hrnot
  apply lowerRosserFailureSumAtRank_eq_zero_of_length_lt
  simp only [Finset.mem_Icc] at hr hrnot
  omega

private theorem upperRosserFailureGate_filter_eq
    (P : Finset Nat) (level z : Real) :
    P.filter (fun p : Nat =>
        (p : Real) < z ∧ (p : Real) * (p : Real) ^ 2 < level) =
      P.filter (fun p : Nat =>
        (p : Real) < z ∧ (p : Real) ^ 3 < level) := by
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpP, hpz, hgate⟩
    exact ⟨hpP, hpz, by nlinarith [hgate]⟩
  · rintro ⟨hpP, hpz, hgate⟩
    exact ⟨hpP, hpz, by nlinarith [hgate]⟩

private theorem upperRosserFailurePartialSum_eq_rankZero_add_gated
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (hprime : ∀ p ∈ P, p.Prime) :
    upperRosserFailurePartialSum P nu level z R =
      upperRosserFailureSumAtRank P nu level z 0 +
        ∑ p ∈ P.filter (fun p : Nat =>
          (p : Real) < z ∧ (p : Real) ^ 3 < level),
          nu p * lowerRosserFailurePartialSum P nu (level / p) p R := by
  induction R with
  | zero =>
      simp
  | succ R ih =>
      rw [upperRosserFailurePartialSum_succ, ih,
        upperRosserFailureSumAtRank_succ_eq_sum_lower
          P nu level z R hprime]
      rw [upperRosserFailureGate_filter_eq P level z]
      rw [add_assoc]
      apply congrArg (fun x =>
        upperRosserFailureSumAtRank P nu level z 0 + x)
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← mul_add, ← lowerRosserFailurePartialSum_succ]

theorem lowerRosserFailureSum_eq_sum_upper_full
    (P : Finset Nat) (nu : Nat → Real) (level z : Real)
    (hprime : ∀ p ∈ P, p.Prime) :
    lowerRosserFailureSum P nu level z =
      ∑ p ∈ P.filter (fun p : Nat => (p : Real) < z),
        nu p * upperRosserFailureSum P nu (level / p) p := by
  let n := (sieveFactorsBelow P z).length
  have houter := lowerRosserFailurePartialSum_eq_full_of_length_le
    P nu level z (n + 1) hprime (by dsimp [n]; omega)
  rw [← houter,
    lowerRosserFailurePartialSum_succ_eq_sum_upper_unrestricted
      P nu level z n hprime]
  apply Finset.sum_congr rfl
  intro p hp
  have hpz : (p : Real) < z := (Finset.mem_filter.mp hp).2
  have hinner := upperRosserFailurePartialSum_eq_full_of_length_le
    P nu (level / p) (p : Real) n hprime
      (by
        change (sieveFactorsBelow P p).length <=
          (sieveFactorsBelow P z).length
        exact sieveFactorsBelow_length_le_of_lt P hpz)
  rw [hinner]

theorem upperRosserFailureSum_eq_rankZero_add_sum_lower_gated
    (P : Finset Nat) (nu : Nat → Real) (level z : Real)
    (hprime : ∀ p ∈ P, p.Prime) :
    upperRosserFailureSum P nu level z =
      upperRosserFailureSumAtRank P nu level z 0 +
        ∑ p ∈ P.filter (fun p : Nat =>
          (p : Real) < z ∧ (p : Real) ^ 3 < level),
          nu p * lowerRosserFailureSum P nu (level / p) p := by
  let n := (sieveFactorsBelow P z).length
  have houter := upperRosserFailurePartialSum_eq_full_of_length_le
    P nu level z n hprime (by
      change (sieveFactorsBelow P z).length <=
        (sieveFactorsBelow P z).length
      exact le_rfl)
  calc
    upperRosserFailureSum P nu level z =
        upperRosserFailurePartialSum P nu level z n := houter.symm
    _ = upperRosserFailureSumAtRank P nu level z 0 +
        ∑ p ∈ P.filter (fun p : Nat =>
          (p : Real) < z ∧ (p : Real) ^ 3 < level),
          nu p * lowerRosserFailurePartialSum P nu (level / p) p n :=
      upperRosserFailurePartialSum_eq_rankZero_add_gated
        P nu level z n hprime
    _ = upperRosserFailureSumAtRank P nu level z 0 +
        ∑ p ∈ P.filter (fun p : Nat =>
          (p : Real) < z ∧ (p : Real) ^ 3 < level),
          nu p * lowerRosserFailureSum P nu (level / p) p := by
      apply congrArg (fun x =>
        upperRosserFailureSumAtRank P nu level z 0 + x)
      apply Finset.sum_congr rfl
      intro p hp
      have hpz : (p : Real) < z := (Finset.mem_filter.mp hp).2.1
      have hinner := lowerRosserFailurePartialSum_eq_full_of_length_le
        P nu (level / p) (p : Real) n hprime
          (by
            change (sieveFactorsBelow P p).length <=
              (sieveFactorsBelow P z).length
            exact sieveFactorsBelow_length_le_of_lt P hpz)
      rw [hinner]

theorem upperRosserFailureSum_eq_rankZero_add_sum_lower_of_cube_le
    (P : Finset Nat) (nu : Nat → Real) (level z : Real)
    (hprime : ∀ p ∈ P, p.Prime) (hcube : z ^ 3 ≤ level) :
    upperRosserFailureSum P nu level z =
      upperRosserFailureSumAtRank P nu level z 0 +
        ∑ p ∈ P.filter (fun p : Nat => (p : Real) < z),
          nu p * lowerRosserFailureSum P nu (level / p) p := by
  rw [upperRosserFailureSum_eq_rankZero_add_sum_lower_gated
    P nu level z hprime]
  have hfilters :
      P.filter (fun p : Nat =>
          (p : Real) < z ∧ (p : Real) ^ 3 < level) =
        P.filter (fun p : Nat => (p : Real) < z) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hpP, hpz, hgate⟩
      exact ⟨hpP, hpz⟩
    · rintro ⟨hpP, hpz⟩
      have hpPrime := hprime p hpP
      have hpNonneg : (0 : Real) ≤ p := by
        exact_mod_cast hpPrime.pos.le
      have hpCube : (p : Real) ^ 3 < z ^ 3 :=
        pow_lt_pow_left₀ hpz hpNonneg (by norm_num)
      exact ⟨hpP, hpz, hpCube.trans_le hcube⟩
  rw [hfilters]

end PrimesRestrictedDigits
