import PrimesRestrictedDigits.MajorArcs.PartitionCardinalityScale
import PrimesRestrictedDigits.MajorArcs.TenGrid

/-!
# Corrected M3 contribution aggregation

This formalizes the finite aggregation on `MAYNARD-PRD-PUBLISHED`,
pp. 188--189. A pointwise progression error is summed over all reduced
residues, so the proof retains the resulting totient factor.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The normalized contribution of the complete repaired M3 frequency
carrier. -/
noncomputable def majorArcClassThreeContribution
    (X : Nat) (Q : Real) (A s : Finset Nat)
    (w : Nat → Complex) : Complex :=
  (∑ h ∈ majorArcClassThreeFrequencies X Q,
      majorArcWeightedPhaseSum A (fun _ => 1)
          ((h : Real) / (X : Real)) *
        majorArcWeightedPhaseSum s w (-((h : Real) / (X : Real)))) /
    (X : Complex)

/-- The ten decimal frequencies are distinct at every positive digit length. -/
theorem card_majorArcTenGridFrequencies
    {X K : Nat} (hK : 0 < K) (hX : X = 10 ^ K) :
    (majorArcTenGridFrequencies X).card = 10 := by
  subst X
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  have hscale : 0 < 10 ^ (k + 1) / 10 := by
    rw [pow_succ]
    simp
  calc
    (majorArcTenGridFrequencies (10 ^ (k + 1))).card =
        (Finset.range 10).card := by
      apply Finset.card_image_of_injective
      intro c d hcd
      exact Nat.eq_of_mul_eq_mul_right hscale hcd
    _ = 10 := by simp

/-- Reindex the canonical nonzero-Moebius part of M3 by the ten decimal
fractions, preserving the opposite phase signs. -/
theorem sum_majorArcClassThree_nonzeroMoebius_eq_tenGrid
    {X K : Nat} (hK : 0 < K) (hX : X = 10 ^ K)
    {Q : Real} (hQ : 10 ≤ Q)
    (A s : Finset Nat) (w : Nat → Complex) :
    (∑ h ∈ (majorArcClassThreeFrequencies X Q).filter
        (fun h : Nat => ArithmeticFunction.moebius
          (((h : Rat) / (X : Rat)).den) ≠ 0),
      majorArcWeightedPhaseSum A (fun _ => 1)
          ((h : Real) / (X : Real)) *
        majorArcWeightedPhaseSum s w
          (-((h : Real) / (X : Real)))) =
      ∑ c ∈ Finset.range 10,
        majorArcWeightedPhaseSum A (fun _ => 1)
          ((c : Real) / 10) *
        majorArcWeightedPhaseSum s w
          (-((c : Real) / 10)) := by
  subst X
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  have hpowdiv : 10 ^ (k + 1) / 10 = 10 ^ k := by
    rw [pow_succ]
    omega
  have hinjective :
      Function.Injective (fun c : Nat => c * 10 ^ k) := by
    intro c d hcd
    exact Nat.eq_of_mul_eq_mul_right
      (by positivity : 0 < 10 ^ k) hcd
  have hratio (c : Nat) :
      ((c * 10 ^ k : Nat) : Real) /
          ((10 ^ (k + 1) : Nat) : Real) =
        (c : Real) / 10 := by
    rw [pow_succ]
    push_cast
    field_simp
  rw [majorArcClassThree_nonzeroMoebius_eq_tenGrid
    (by omega : 0 < k + 1) rfl hQ,
    majorArcTenGridFrequencies, hpowdiv,
    Finset.sum_image hinjective.injOn]
  apply Finset.sum_congr rfl
  intro c hc
  rw [hratio]

private theorem norm_majorArcWeightedPhaseSum_zeroMoebius_le
    {X K : Nat} (hK : 0 < K) (hX : X = 10 ^ K)
    {Q E : Real} (hE : 0 ≤ E)
    (s : Finset Nat) (w : Nat → Complex)
    (hsupport : ∀ n ∈ s, w n ≠ 0 → Nat.Coprime n 10)
    (T : Complex)
    (hAP : ∀ q : Nat, 0 < q → q ∣ X → (q : Real) ≤ Q →
      ∀ r : Nat, Nat.Coprime r q →
        ‖majorArcResidueWeightSum s w q r -
          T / (Nat.totient q : Complex)‖ ≤ E)
    {a : Nat} (ha : a ∈ majorArcClassThreeFrequencies X Q)
    (hmu : ArithmeticFunction.moebius
      (((a : Rat) / (X : Rat)).den) = 0) :
    ‖majorArcWeightedPhaseSum s w (-((a : Real) / (X : Real)))‖ ≤
      Q * E := by
  classical
  let ratio : Rat := (a : Rat) / (X : Rat)
  let q : Nat := ratio.den
  let b : Int := -ratio.num
  have haData := Finset.mem_filter.mp ha
  have hclass : majorArcClassThree X a Q := haData.2
  rcases hclass.exact with ⟨r, hr, hrdiv, hrequal⟩
  have hq : 0 < q := ratio.den_pos
  have hqdiv : q ∣ X := by
    simpa [q, ratio, hrequal] using hrdiv
  have hqQ : (q : Real) ≤ Q := by
    simpa [q, ratio, hrequal] using hr.2
  have hb : Nat.Coprime b.natAbs q := by
    simpa [b, q] using ratio.reduced
  have hsupportq : ∀ n ∈ s, w n ≠ 0 → Nat.Coprime n q := by
    intro n hn hwn
    apply Nat.Coprime.of_dvd_right hqdiv
    rw [hX]
    exact (Nat.coprime_pow_right_iff hK n 10).2 (hsupport n hn hwn)
  have hratioReal : (ratio : Real) = (a : Real) / (X : Real) := by
    simp [ratio]
  have htheta : (b : Real) / (q : Real) =
      -((a : Real) / (X : Real)) := by
    rw [← hratioReal]
    dsimp [b, q]
    rw [Rat.cast_def]
    push_cast
    ring
  have hbound := norm_majorArcWeightedPhaseSum_sub_moebius_main_le_totient
    s w hq hb hsupportq (T / (Nat.totient q : Complex))
    (fun r hr => hAP q hq hqdiv hqQ r (Finset.mem_filter.mp hr).2)
  have hmuq : ArithmeticFunction.moebius q = 0 := by
    simpa [q, ratio] using hmu
  rw [htheta, hmuq] at hbound
  simp only [Int.cast_zero, zero_mul, sub_zero] at hbound
  apply hbound.trans
  have hphi : (Nat.totient q : Real) ≤ Q := by
    have hphiReal : (Nat.totient q : Real) ≤ (q : Real) := by
      exact_mod_cast Nat.totient_le q
    exact hphiReal.trans hqQ
  gcongr

/-- A uniform per-residue progression error bounds the complete normalized M3
contribution. This includes both the ten-grid and zero-Moebius frequencies. -/
theorem norm_majorArcClassThreeContribution_sub_density_le
    (digit : Fin 10) {X K : Nat} (hK : 0 < K)
    (hX : X = 10 ^ K) {Q : Real} (hQ : 10 ≤ Q)
    (hQX : Q ≤ (X : Real))
    (s : Finset Nat) (w : Nat → Complex)
    (hsupport : ∀ n ∈ s, w n ≠ 0 → Nat.Coprime n 10)
    (T : Complex) {E : Real} (hE : 0 ≤ E)
    (hAP : ∀ q : Nat, 0 < q → q ∣ X → (q : Real) ≤ Q →
      ∀ r : Nat, Nat.Coprime r q →
        ‖majorArcResidueWeightSum s w q r -
          T / (Nat.totient q : Complex)‖ ≤ E) :
    ‖majorArcClassThreeContribution X Q
        (paddedRestrictedNumbers digit K) s w -
      (restrictedDigitDensity digit : Complex) *
        ((paddedRestrictedNumbers digit K).card : Complex) * T /
          (X : Complex)‖ ≤
      14 * ((paddedRestrictedNumbers digit K).card : Real) * Q ^ 3 * E /
        (X : Real) := by
  classical
  let A := paddedRestrictedNumbers digit K
  let F := majorArcClassThreeFrequencies X Q
  let P : Nat → Prop := fun h => ArithmeticFunction.moebius
    (((h : Rat) / (X : Rat)).den) ≠ 0
  let Z := F.filter fun h => ¬P h
  let term : Nat → Complex := fun h =>
    majorArcWeightedPhaseSum A (fun _ => 1)
        ((h : Real) / (X : Real)) *
      majorArcWeightedPhaseSum s w (-((h : Real) / (X : Real)))
  let grid : Complex := ∑ c ∈ Finset.range 10,
    majorArcWeightedPhaseSum A (fun _ => 1) ((c : Real) / 10) *
      majorArcWeightedPhaseSum s w (-((c : Real) / 10))
  let main : Complex := (restrictedDigitDensity digit : Complex) *
    (A.card : Complex) * T
  have hXpos : (0 : Real) < X := by
    rw [hX]
    positivity
  have hTenDiv : 10 ∣ X := by
    rw [hX]
    exact dvd_pow_self 10 hK.ne'
  have hGridBound : ‖grid - main‖ ≤ 10 * (A.card : Real) * E := by
    dsimp [grid, main]
    simpa only [A] using
      norm_majorArcTenGrid_bilinear_sub_density_main_le
        digit hK s w hsupport T hE
          (fun m hm hcoprime =>
            hAP 10 (by norm_num) hTenDiv hQ m hcoprime)
  have hOffGridBound :
      ‖∑ h ∈ Z, term h‖ ≤ (Z.card : Real) * (A.card : Real) * Q * E := by
    calc
      ‖∑ h ∈ Z, term h‖ ≤ ∑ h ∈ Z, ‖term h‖ := norm_sum_le _ _
      _ ≤ ∑ _h ∈ Z, (A.card : Real) * Q * E := by
        gcongr with h hh
        rcases Finset.mem_filter.mp hh with ⟨hhF, hhNot⟩
        have hhMu : ArithmeticFunction.moebius
            (((h : Rat) / (X : Rat)).den) = 0 := by
          exact not_ne_iff.mp (by simpa only [P] using hhNot)
        dsimp [term]
        rw [norm_mul]
        calc
          ‖majorArcWeightedPhaseSum A (fun _ => 1)
                ((h : Real) / (X : Real))‖ *
              ‖majorArcWeightedPhaseSum s w
                (-((h : Real) / (X : Real)))‖ ≤
              (A.card : Real) * (Q * E) := by
            gcongr
            · exact norm_majorArcWeightedPhaseSum_one_le_card A _
            · exact norm_majorArcWeightedPhaseSum_zeroMoebius_le
                hK hX hE s w hsupport T hAP
                  (by simpa only [F] using hhF) hhMu
          _ = (A.card : Real) * Q * E := by ring
      _ = (Z.card : Real) * (A.card : Real) * Q * E := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hSplit :
      (∑ h ∈ F.filter P, term h) + (∑ h ∈ Z, term h) =
        ∑ h ∈ F, term h := by
    simpa only [Z] using F.sum_filter_add_sum_filter_not P term
  have hGridEq : (∑ h ∈ F.filter P, term h) = grid := by
    dsimp [F, P, term, grid]
    exact sum_majorArcClassThree_nonzeroMoebius_eq_tenGrid
      hK hX hQ A s w
  have hRawEq :
      (∑ h ∈ F, term h) - main =
        (grid - main) + ∑ h ∈ Z, term h := by
    rw [← hSplit, hGridEq]
    ring
  have hNonzeroCard : (F.filter P).card = 10 := by
    dsimp [F, P]
    rw [majorArcClassThree_nonzeroMoebius_eq_tenGrid hK hX hQ,
      card_majorArcTenGridFrequencies hK hX]
  have hCardSplit : (F.filter P).card + Z.card = F.card := by
    simpa only [Z] using F.card_filter_add_card_filter_not P
  have hCard : F.card = 10 + Z.card := by omega
  have hCardReal : (F.card : Real) = 10 + (Z.card : Real) := by
    exact_mod_cast hCard
  have hCombine :
      10 * (A.card : Real) * E +
          (Z.card : Real) * (A.card : Real) * Q * E ≤
        (F.card : Real) * (A.card : Real) * Q * E := by
    have hcore :
        10 + (Z.card : Real) * Q ≤
          (10 + (Z.card : Real)) * Q := by
      nlinarith
    calc
      10 * (A.card : Real) * E +
            (Z.card : Real) * (A.card : Real) * Q * E =
          (10 + (Z.card : Real) * Q) * ((A.card : Real) * E) := by ring
      _ ≤ ((10 + (Z.card : Real)) * Q) * ((A.card : Real) * E) := by
        gcongr
      _ = (F.card : Real) * (A.card : Real) * Q * E := by
        rw [hCardReal]
        ring
  have hCardBound : (F.card : Real) ≤ 14 * Q ^ 2 := by
    exact majorArcClassThreeFrequencies_card_real_le (by linarith) hQX
  have hRawBound :
      ‖(∑ h ∈ F, term h) - main‖ ≤
        14 * (A.card : Real) * Q ^ 3 * E := by
    rw [hRawEq]
    calc
      ‖(grid - main) + ∑ h ∈ Z, term h‖ ≤
          ‖grid - main‖ + ‖∑ h ∈ Z, term h‖ := norm_add_le _ _
      _ ≤ 10 * (A.card : Real) * E +
          (Z.card : Real) * (A.card : Real) * Q * E :=
        add_le_add hGridBound hOffGridBound
      _ ≤ (F.card : Real) * (A.card : Real) * Q * E := hCombine
      _ ≤ (14 * Q ^ 2) * (A.card : Real) * Q * E := by
        gcongr
      _ = 14 * (A.card : Real) * Q ^ 3 * E := by ring
  change
    ‖(∑ h ∈ F, term h) / (X : Complex) - main / (X : Complex)‖ ≤
      14 * (A.card : Real) * Q ^ 3 * E / (X : Real)
  rw [← sub_div, norm_div, norm_natCast]
  exact div_le_div_of_nonneg_right hRawBound hXpos.le

/-- At error scale `B * X / Q^4`, the corrected M3 contribution saves one
power of `Q`. -/
theorem norm_majorArcClassThreeContribution_sub_density_le_sourceScale
    (digit : Fin 10) {X K : Nat} (hK : 0 < K)
    (hX : X = 10 ^ K) {Q B : Real} (hQ : 10 ≤ Q)
    (hQX : Q ≤ (X : Real)) (hB : 0 ≤ B)
    (s : Finset Nat) (w : Nat → Complex)
    (hsupport : ∀ n ∈ s, w n ≠ 0 → Nat.Coprime n 10)
    (T : Complex)
    (hAP : ∀ q : Nat, 0 < q → q ∣ X → (q : Real) ≤ Q →
      ∀ r : Nat, Nat.Coprime r q →
        ‖majorArcResidueWeightSum s w q r -
          T / (Nat.totient q : Complex)‖ ≤
            B * (X : Real) / Q ^ 4) :
    ‖majorArcClassThreeContribution X Q
        (paddedRestrictedNumbers digit K) s w -
      (restrictedDigitDensity digit : Complex) *
        ((paddedRestrictedNumbers digit K).card : Complex) * T /
          (X : Complex)‖ ≤
      14 * B * ((paddedRestrictedNumbers digit K).card : Real) / Q := by
  have hE : 0 ≤ B * (X : Real) / Q ^ 4 := by positivity
  have hbound := norm_majorArcClassThreeContribution_sub_density_le
    digit hK hX hQ hQX s w hsupport T hE hAP
  apply hbound.trans_eq
  have hQ0 : Q ≠ 0 := by linarith
  have hX0 : (X : Real) ≠ 0 := by
    rw [hX]
    positivity
  field_simp

end PrimesRestrictedDigits
