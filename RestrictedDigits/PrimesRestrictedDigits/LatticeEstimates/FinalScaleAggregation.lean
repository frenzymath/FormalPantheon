import PrimesRestrictedDigits.LatticeEstimates.FinalLatticeSum
import PrimesRestrictedDigits.LatticeEstimates.SmoothFactorBands

/-!
# Smooth-scale aggregation for the lattice estimate

This file sums the corrected Lemma 14.4 bound over the two decimal-smooth factor bands and
performs the final scale conversion in the proof of Proposition 13.3.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The corrected Lemma 14.4 minimum summed over both decimal-smooth factor
bands. -/
noncomputable def latticeExceptionalSmoothPairSum
    (digit : Fin 10) (length Q1 G1 G2 D0 D1 E0 : Nat) : Real :=
  ∑ d0 ∈ latticeSmoothFactorTenBand D0,
    ∑ d1 ∈ latticeSmoothFactorTenBand D1,
      latticeExceptionalProductMinimum digit length d0 d1 Q1 G1 G2 E0

theorem latticeExceptionalSmoothPairSum_nonneg
    (digit : Fin 10) (length Q1 G1 G2 D0 D1 E0 : Nat) :
    0 ≤ latticeExceptionalSmoothPairSum digit length Q1 G1 G2 D0 D1 E0 := by
  unfold latticeExceptionalSmoothPairSum
  exact Finset.sum_nonneg fun d0 _ => Finset.sum_nonneg fun d1 _ =>
    latticeExceptionalProductMinimum_nonneg digit length d0 d1 Q1 G1 G2 E0

/-- Summing Lemma 14.4 spends half of its saving on the combined ordered pair
of decimal-smooth factor bands. -/
theorem exists_latticeExceptionalSmoothPairSum_le (loss : Nat) :
    ∃ C : Real, 0 < C ∧
      ∀ (digit : Fin 10)
        (length qLength g1Length g2Length d0Length d1Length eLength : Nat)
        (P : Real),
        let X : Real := ((10 ^ length : Nat) : Real)
        let A : Real := ((10 ^ loss : Nat) : Real)
        let Q1 : Nat := 10 ^ qLength
        let G1 : Nat := 10 ^ g1Length
        let G2 : Nat := 10 ^ g2Length
        let D0 : Nat := 10 ^ d0Length
        let D1 : Nat := 10 ^ d1Length
        let E0 : Nat := 10 ^ eLength
        let Q0 : Nat := Q1 * G1 * G2 * D0 * D1
        X ^ (17 / 40 : Real) ≤ P →
        ((E0 * Q0 : Nat) : Real) ≤ A * X / P →
        (G1 : Real) ≤ A * G2 →
        latticeExceptionalSmoothPairSum digit length Q1 G1 G2 D0 D1 E0 ≤
          C * ((Q0 : Real) ^ (1 - latticeSumSaving / 2) *
            (E0 : Real) ^ (1 - latticeSumSaving)) := by
  obtain ⟨Cminimum, hCminimum, hminimum⟩ :=
    exists_latticeExceptionalProductMinimum_le loss
  obtain ⟨Cband, hCband, hband⟩ :=
    exists_card_latticeSmoothFactorTenBand_le
      (latticeSumSaving / 2) (by positivity [latticeSumSaving_pos])
  let C : Real := Cband ^ 2 * Cminimum
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro digit length qLength g1Length g2Length d0Length d1Length eLength P
  dsimp only
  intro hP hscale hG
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Real := ((10 ^ loss : Nat) : Real)
  let Q1 : Nat := 10 ^ qLength
  let G1 : Nat := 10 ^ g1Length
  let G2 : Nat := 10 ^ g2Length
  let D0 : Nat := 10 ^ d0Length
  let D1 : Nat := 10 ^ d1Length
  let E0 : Nat := 10 ^ eLength
  let Q0 : Nat := Q1 * G1 * G2 * D0 * D1
  let B0 := latticeSmoothFactorTenBand D0
  let B1 := latticeSmoothFactorTenBand D1
  let M : Real := Cminimum *
    ((Q0 : Real) ^ (1 - latticeSumSaving) *
      (E0 : Real) ^ (1 - latticeSumSaving))
  change ((E0 * Q0 : Nat) : Real) ≤ A * X / P at hscale
  change (G1 : Real) ≤ A * G2 at hG
  have hQ0 : 0 < Q0 := by dsimp only [Q0, Q1, G1, G2, D0, D1]; positivity
  have hQ0Real : 0 < (Q0 : Real) := by exact_mod_cast hQ0
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hpoint : ∀ d0 ∈ B0, ∀ d1 ∈ B1,
      latticeExceptionalProductMinimum digit length d0 d1 Q1 G1 G2 E0 ≤ M := by
    intro d0 hd0 d1 hd1
    have hd0Data := mem_latticeSmoothFactorTenBand_iff.mp hd0
    have hd1Data := mem_latticeSmoothFactorTenBand_iff.mp hd1
    have hd0Smooth :=
      (isDecimalSmooth_iff_exists_dvd_pow_ten d0).1 hd0Data.2
    have hd1Smooth :=
      (isDecimalSmooth_iff_exists_dvd_pow_ten d1).1 hd1Data.2
    have hraw := hminimum digit length qLength g1Length g2Length
      d0Length d1Length eLength d0 d1 P hP hscale hG
      hd0Data.1 hd1Data.1 hd0Smooth hd1Smooth
    simpa only [M, X, A, Q1, G1, G2, D0, D1, E0, Q0] using hraw
  have hsum :
      latticeExceptionalSmoothPairSum digit length Q1 G1 G2 D0 D1 E0 ≤
        (B0.card : Real) * (B1.card : Real) * M := by
    unfold latticeExceptionalSmoothPairSum
    change (∑ d0 ∈ B0, ∑ d1 ∈ B1,
      latticeExceptionalProductMinimum digit length d0 d1 Q1 G1 G2 E0) ≤ _
    calc
      (∑ d0 ∈ B0, ∑ d1 ∈ B1,
          latticeExceptionalProductMinimum digit length d0 d1 Q1 G1 G2 E0) ≤
          ∑ _d0 ∈ B0, ∑ _d1 ∈ B1, M := by
        apply Finset.sum_le_sum
        intro d0 hd0
        apply Finset.sum_le_sum
        exact hpoint d0 hd0
      _ = (B0.card : Real) * (B1.card : Real) * M := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hB0 : (B0.card : Real) ≤
      Cband * (D0 : Real) ^ (latticeSumSaving / 2) := by
    simpa only [B0, D0] using hband d0Length
  have hB1 : (B1.card : Real) ≤
      Cband * (D1 : Real) ^ (latticeSumSaving / 2) := by
    simpa only [B1, D1] using hband d1Length
  have hcards : (B0.card : Real) * (B1.card : Real) ≤
      Cband ^ 2 * ((D0 : Real) * D1) ^ (latticeSumSaving / 2) := by
    calc
      (B0.card : Real) * (B1.card : Real) ≤
          (Cband * (D0 : Real) ^ (latticeSumSaving / 2)) *
            (Cband * (D1 : Real) ^ (latticeSumSaving / 2)) :=
        mul_le_mul hB0 hB1 (by positivity) (by positivity)
      _ = Cband ^ 2 * ((D0 : Real) * D1) ^
          (latticeSumSaving / 2) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        ring
  have hD : D0 * D1 ≤ Q0 := by
    dsimp only [Q0]
    have hfactorPos : 0 < Q1 * G1 * G2 := by positivity
    have hfactor : 1 ≤ Q1 * G1 * G2 := hfactorPos
    calc
      D0 * D1 = 1 * (D0 * D1) := by ring
      _ ≤ (Q1 * G1 * G2) * (D0 * D1) := Nat.mul_le_mul_right _ hfactor
      _ = Q1 * G1 * G2 * D0 * D1 := by ring
  have hDpower : ((D0 : Real) * D1) ^ (latticeSumSaving / 2) ≤
      (Q0 : Real) ^ (latticeSumSaving / 2) := by
    apply Real.rpow_le_rpow (by positivity) _ (by positivity [latticeSumSaving_pos])
    exact_mod_cast hD
  have hQcombine :
      (Q0 : Real) ^ (latticeSumSaving / 2) *
          (Q0 : Real) ^ (1 - latticeSumSaving) =
        (Q0 : Real) ^ (1 - latticeSumSaving / 2) := by
    rw [← Real.rpow_add hQ0Real]
    congr 1
    ring
  calc
    latticeExceptionalSmoothPairSum digit length Q1 G1 G2 D0 D1 E0 ≤
        (B0.card : Real) * (B1.card : Real) * M := hsum
    _ ≤ (Cband ^ 2 * ((D0 : Real) * D1) ^
          (latticeSumSaving / 2)) * M :=
      mul_le_mul_of_nonneg_right hcards hM
    _ ≤ (Cband ^ 2 * (Q0 : Real) ^ (latticeSumSaving / 2)) * M := by
      gcongr
    _ = C * ((Q0 : Real) ^ (1 - latticeSumSaving / 2) *
          (E0 : Real) ^ (1 - latticeSumSaving)) := by
      dsimp only [C, M]
      calc
        Cband ^ 2 * (Q0 : Real) ^ (latticeSumSaving / 2) *
              (Cminimum * ((Q0 : Real) ^ (1 - latticeSumSaving) *
                (E0 : Real) ^ (1 - latticeSumSaving))) =
            Cband ^ 2 * Cminimum *
              (((Q0 : Real) ^ (latticeSumSaving / 2) *
                (Q0 : Real) ^ (1 - latticeSumSaving)) *
                  (E0 : Real) ^ (1 - latticeSumSaving)) := by ring
        _ = Cband ^ 2 * Cminimum *
            ((Q0 : Real) ^ (1 - latticeSumSaving / 2) *
              (E0 : Real) ^ (1 - latticeSumSaving)) := by rw [hQcombine]

/-- The smooth-pair sum is controlled by the final physical scale `X/P`. -/
theorem exists_latticeExceptionalSmoothPairSum_le_sourceScale (loss : Nat) :
    ∃ C : Real, 0 < C ∧
      ∀ (digit : Fin 10)
        (length qLength g1Length g2Length d0Length d1Length eLength : Nat)
        (P : Real),
        let X : Real := ((10 ^ length : Nat) : Real)
        let A : Real := ((10 ^ loss : Nat) : Real)
        let Q1 : Nat := 10 ^ qLength
        let G1 : Nat := 10 ^ g1Length
        let G2 : Nat := 10 ^ g2Length
        let D0 : Nat := 10 ^ d0Length
        let D1 : Nat := 10 ^ d1Length
        let E0 : Nat := 10 ^ eLength
        let Q0 : Nat := Q1 * G1 * G2 * D0 * D1
        X ^ (17 / 40 : Real) ≤ P →
        ((E0 * Q0 : Nat) : Real) ≤ A * X / P →
        (G1 : Real) ≤ A * G2 →
        latticeExceptionalSmoothPairSum digit length Q1 G1 G2 D0 D1 E0 ≤
          C * (X / P) ^ (1 - latticeSumSaving / 2) := by
  obtain ⟨Csum, hCsum, hsum⟩ :=
    exists_latticeExceptionalSmoothPairSum_le loss
  let A : Real := ((10 ^ loss : Nat) : Real)
  let exponent : Real := 1 - latticeSumSaving / 2
  let C : Real := Csum * A ^ exponent
  have hA : 0 < A := by dsimp only [A]; positivity
  have hexponent : 0 < exponent := by
    dsimp only [exponent]
    nlinarith [latticeSumSaving_pos, latticeSumSaving_lt_one]
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro digit length qLength g1Length g2Length d0Length d1Length eLength P
  dsimp only
  intro hP hscale hG
  let X : Real := ((10 ^ length : Nat) : Real)
  let Q1 : Nat := 10 ^ qLength
  let G1 : Nat := 10 ^ g1Length
  let G2 : Nat := 10 ^ g2Length
  let D0 : Nat := 10 ^ d0Length
  let D1 : Nat := 10 ^ d1Length
  let E0 : Nat := 10 ^ eLength
  let Q0 : Nat := Q1 * G1 * G2 * D0 * D1
  change ((E0 * Q0 : Nat) : Real) ≤ A * X / P at hscale
  change (G1 : Real) ≤ A * G2 at hG
  have hraw := hsum digit length qLength g1Length g2Length d0Length
    d1Length eLength P hP hscale hG
  have hX : 0 < X := by dsimp only [X]; positivity
  have hPpos : 0 < P := by
    exact (Real.rpow_pos_of_pos hX (17 / 40 : Real)).trans_le hP
  have hQ0 : 0 < Q0 := by dsimp only [Q0, Q1, G1, G2, D0, D1]; positivity
  have hE0 : 0 < E0 := by dsimp only [E0]; positivity
  have hE0One : (1 : Real) ≤ E0 := by exact_mod_cast hE0
  have hEpower : (E0 : Real) ^ (1 - latticeSumSaving) ≤
      (E0 : Real) ^ exponent := by
    apply Real.rpow_le_rpow_of_exponent_le hE0One
    dsimp only [exponent]
    nlinarith [latticeSumSaving_pos]
  have hproduct :
      (Q0 : Real) ^ exponent * (E0 : Real) ^ (1 - latticeSumSaving) ≤
        ((Q0 : Real) * E0) ^ exponent := by
    calc
      (Q0 : Real) ^ exponent * (E0 : Real) ^ (1 - latticeSumSaving) ≤
          (Q0 : Real) ^ exponent * (E0 : Real) ^ exponent := by gcongr
      _ = ((Q0 : Real) * E0) ^ exponent :=
        (Real.mul_rpow (by positivity) (by positivity)).symm
  have hscale' : (Q0 : Real) * E0 ≤ A * (X / P) := by
    norm_num only [Nat.cast_mul] at hscale
    calc
      (Q0 : Real) * E0 = E0 * Q0 := by ring
      _ ≤ A * X / P := hscale
      _ = A * (X / P) := by ring
  have hscalePower : ((Q0 : Real) * E0) ^ exponent ≤
      (A * (X / P)) ^ exponent :=
    Real.rpow_le_rpow (by positivity) hscale' hexponent.le
  calc
    latticeExceptionalSmoothPairSum digit length Q1 G1 G2 D0 D1 E0 ≤
        Csum * ((Q0 : Real) ^ exponent *
          (E0 : Real) ^ (1 - latticeSumSaving)) := by
      simpa only [X, Q1, G1, G2, D0, D1, E0, Q0, exponent] using hraw
    _ ≤ Csum * (((Q0 : Real) * E0) ^ exponent) := by gcongr
    _ ≤ Csum * ((A * (X / P)) ^ exponent) := by gcongr
    _ = C * (X / P) ^ exponent := by
      rw [Real.mul_rpow hA.le (by positivity)]
      dsimp only [C]
      ring

/-- Lemma 14.2's rational-size relation converts the remaining half-saving
into the quarter-saving in Proposition 13.3. -/
theorem latticePropositionScaleConversion
    {A X P R : Real} (hA : 0 ≤ A) (hX : 0 < X) (hP : 0 < P)
    (hR : 0 < R) (hsize : R ≤ A * (X / P) ^ 2) :
    (X / P) ^ (1 - latticeSumSaving / 2) ≤
      A ^ (latticeSumSaving / 4) * X /
        (P * R ^ (latticeSumSaving / 4)) := by
  let Y : Real := X / P
  let quarter : Real := latticeSumSaving / 4
  let exponent : Real := 1 - latticeSumSaving / 2
  have hY : 0 < Y := by dsimp only [Y]; positivity
  have hquarter : 0 < quarter := by
    dsimp only [quarter]
    positivity [latticeSumSaving_pos]
  have hRpower : 0 < R ^ quarter := Real.rpow_pos_of_pos hR quarter
  have hsizePower : R ^ quarter ≤ (A * Y ^ 2) ^ quarter := by
    apply Real.rpow_le_rpow hR.le
    · simpa only [Y] using hsize
    · exact hquarter.le
  have hsquare : (Y ^ 2) ^ quarter = Y ^ (2 * quarter) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_mul hY.le (2 : Real) quarter).symm
  have hmul : Y ^ exponent * R ^ quarter ≤ A ^ quarter * Y := by
    calc
      Y ^ exponent * R ^ quarter ≤
          Y ^ exponent * (A * Y ^ 2) ^ quarter := by gcongr
      _ = Y ^ exponent * (A ^ quarter * (Y ^ 2) ^ quarter) := by
        rw [Real.mul_rpow hA (sq_nonneg Y)]
      _ = A ^ quarter * (Y ^ exponent * Y ^ (2 * quarter)) := by
        rw [hsquare]
        ring
      _ = A ^ quarter * Y := by
        rw [← Real.rpow_add hY]
        have hexponents : exponent + 2 * quarter = 1 := by
          dsimp only [exponent, quarter]
          ring
        rw [hexponents, Real.rpow_one]
  change Y ^ exponent ≤ A ^ quarter * X / (P * R ^ quarter)
  calc
    Y ^ exponent ≤ A ^ quarter * Y / R ^ quarter :=
      (le_div_iff₀ hRpower).2 hmul
    _ = A ^ quarter * X / (P * R ^ quarter) := by
      dsimp only [Y]
      field_simp

/-- The full unblocked scale aggregation used after the Lemma 14.3
outer decomposition. -/
theorem exists_latticeExceptionalSmoothPairSum_le_propositionScale
    (loss : Nat) :
    ∃ C : Real, 0 < C ∧
      ∀ (digit : Fin 10)
        (length qLength g1Length g2Length d0Length d1Length eLength : Nat)
        (P Qband Eband : Real),
        let X : Real := ((10 ^ length : Nat) : Real)
        let A : Real := ((10 ^ loss : Nat) : Real)
        let Q1 : Nat := 10 ^ qLength
        let G1 : Nat := 10 ^ g1Length
        let G2 : Nat := 10 ^ g2Length
        let D0 : Nat := 10 ^ d0Length
        let D1 : Nat := 10 ^ d1Length
        let E0 : Nat := 10 ^ eLength
        let Q0 : Nat := Q1 * G1 * G2 * D0 * D1
        X ^ (17 / 40 : Real) ≤ P →
        ((E0 * Q0 : Nat) : Real) ≤ A * X / P →
        (G1 : Real) ≤ A * G2 →
        1 ≤ Qband →
        0 ≤ Eband →
        Qband + Eband ≤ A * (X / P) ^ 2 →
        latticeExceptionalSmoothPairSum digit length Q1 G1 G2 D0 D1 E0 ≤
          C * X / (P * (Qband + Eband) ^ (latticeSumSaving / 4)) := by
  obtain ⟨Cscale, hCscale, hscaleBound⟩ :=
    exists_latticeExceptionalSmoothPairSum_le_sourceScale loss
  let A : Real := ((10 ^ loss : Nat) : Real)
  let quarter : Real := latticeSumSaving / 4
  let C : Real := Cscale * A ^ quarter
  have hA : 0 < A := by dsimp only [A]; positivity
  have hC : 0 < C := by dsimp only [C, quarter]; positivity
  refine ⟨C, hC, ?_⟩
  intro digit length qLength g1Length g2Length d0Length d1Length eLength
    P Qband Eband
  dsimp only
  intro hP hsource hG hQband hEband hsize
  let X : Real := ((10 ^ length : Nat) : Real)
  let Q1 : Nat := 10 ^ qLength
  let G1 : Nat := 10 ^ g1Length
  let G2 : Nat := 10 ^ g2Length
  let D0 : Nat := 10 ^ d0Length
  let D1 : Nat := 10 ^ d1Length
  let E0 : Nat := 10 ^ eLength
  let Q0 : Nat := Q1 * G1 * G2 * D0 * D1
  change ((E0 * Q0 : Nat) : Real) ≤ A * X / P at hsource
  change (G1 : Real) ≤ A * G2 at hG
  have hX : 0 < X := by dsimp only [X]; positivity
  have hPpos : 0 < P :=
    (Real.rpow_pos_of_pos hX (17 / 40 : Real)).trans_le hP
  have hR : 0 < Qband + Eband := by linarith
  have hconversion := latticePropositionScaleConversion hA.le hX hPpos hR hsize
  have hraw := hscaleBound digit length qLength g1Length g2Length
    d0Length d1Length eLength P hP hsource hG
  calc
    latticeExceptionalSmoothPairSum digit length Q1 G1 G2 D0 D1 E0 ≤
        Cscale * (X / P) ^ (1 - latticeSumSaving / 2) := by
      simpa only [X, Q1, G1, G2, D0, D1, E0, Q0] using hraw
    _ ≤ Cscale *
        (A ^ quarter * X / (P * (Qband + Eband) ^ quarter)) := by
      dsimp only [quarter]
      gcongr
    _ = C * X / (P * (Qband + Eband) ^ (latticeSumSaving / 4)) := by
      dsimp only [C, quarter]
      ring

end

end PrimesRestrictedDigits
