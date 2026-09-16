import PrimesRestrictedDigits.LatticeEstimates.ExceptionalSourceBound
import PrimesRestrictedDigits.LatticeEstimates.FinalSourceScales
/-!
# The final lattice-sum estimate

This file proves the corrected quantitative conclusion of published Lemma 14.4 for the literal
source sums.
-/
namespace PrimesRestrictedDigits
noncomputable section
/-- The corrected source-facing conclusion of published Lemma 14.4. -/
theorem exists_latticeExceptionalProductMinimum_le (loss : Nat) :
    ∃ C : Real, 0 < C ∧
      ∀ (digit : Fin 10)
        (length qLength g1Length g2Length d0Length d1Length eLength : Nat)
        (d0 d1 : Nat) (P : Real),
        let X : Real := ((10 ^ length : Nat) : Real)
        let A : Real := ((10 ^ loss : Nat) : Real)
        let Q1 : Nat := 10 ^ qLength
        let G1 : Nat := 10 ^ g1Length
        let G2 : Nat := 10 ^ g2Length
        let D0 : Nat := 10 ^ d0Length
        let D1 : Nat := 10 ^ d1Length
        let E0 : Nat := 10 ^ eLength
        let Q0 : Nat := Q1 * G1 * G2 * D0 * D1
        X ^ (17 / 40 : Real) <= P ->
        ((E0 * Q0 : Nat) : Real) <= A * X / P ->
        (G1 : Real) <= A * G2 ->
        d0 ∈ latticeFactorTenBand D0 ->
        d1 ∈ latticeFactorTenBand D1 ->
        (∃ u : Nat, d0 ∣ 10 ^ u) ->
        (∃ u : Nat, d1 ∣ 10 ^ u) ->
        latticeExceptionalProductMinimum digit length d0 d1 Q1 G1 G2 E0 <=
          C * ((Q0 : Real) ^ (1 - latticeSumSaving) *
            (E0 : Real) ^ (1 - latticeSumSaving)) := by
  let A : Real := ((10 ^ loss : Nat) : Real)
  have hA : 1 <= A := by
    dsimp only [A]
    exact_mod_cast Nat.one_le_pow loss 10 (by norm_num)
  obtain ⟨Cscalar, hCscalar, hscalar⟩ :=
    exists_latticeFinalScalarBound A hA
  obtain ⟨Ctwo, hCtwo, htwo⟩ :=
    exists_latticeSTwo_le_hybridBound latticeSumSaving latticeSumSaving_pos
  obtain ⟨Cthree, hCthree, hthree⟩ :=
    exists_latticeSThree_le_sourceBound latticeSumSaving A
      latticeSumSaving_pos latticeSumSaving_le_exceptionalGap
      (Real.zero_lt_one.trans_le hA)
  let Cone : Real := 4 * hybridConstant *
    (A ^ largeSieveAlpha + A * A ^ largeSieveSigma)
  let CaltRaw : Real :=
    72000 * largeSieveSamplingConstant ^ 2 * (1 + 2 * A) ^ 2 *
      (1 + A) * (3 + A ^ largeSieveSigma)
  let Calt : Real := CaltRaw * (A ^ hybridResidualGrowth + A)
  let K : Real := max 1 (max Cone (max Calt (max Ctwo Cthree)))
  let C : Real := K ^ 2 * Cscalar
  have hK : 0 < K := lt_of_lt_of_le Real.zero_lt_one (le_max_left _ _)
  have hC : 0 < C := mul_pos (sq_pos_of_pos hK) hCscalar
  refine ⟨C, hC, ?_⟩
  intro digit length qLength g1Length g2Length d0Length d1Length eLength
    d0 d1 P
  dsimp only
  intro hPscale hsourceScale hGscale hd0Band hd1Band hd0Smooth hd1Smooth
  let X : Real := ((10 ^ length : Nat) : Real)
  let Q1 : Nat := 10 ^ qLength
  let G1 : Nat := 10 ^ g1Length
  let G2 : Nat := 10 ^ g2Length
  let D0 : Nat := 10 ^ d0Length
  let D1 : Nat := 10 ^ d1Length
  let E0 : Nat := 10 ^ eLength
  let Q0 : Nat := Q1 * G1 * G2 * D0 * D1
  let S1 : Real := latticeSOne digit length (d0 * d1) Q1 G1 E0
  let S2 : Real := latticeSTwo digit length d0 Q1 G2 E0
  let S3 : Real := latticeSThree digit length d0 Q1 G2 E0
  change ((E0 * Q0 : Nat) : Real) <= A * X / P at hsourceScale
  change (G1 : Real) <= A * G2 at hGscale
  have hX : 1 <= X := by
    dsimp only [X]
    exact_mod_cast Nat.one_le_pow length 10 (by norm_num)
  have hQ1 : 0 < Q1 := by dsimp only [Q1]; positivity
  have hG1 : 0 < G1 := by dsimp only [G1]; positivity
  have hG2 : 0 < G2 := by dsimp only [G2]; positivity
  have hD0 : 0 < D0 := by dsimp only [D0]; positivity
  have hD1 : 0 < D1 := by dsimp only [D1]; positivity
  have hE0 : 0 < E0 := by dsimp only [E0]; positivity
  have hQ0 : 0 < Q0 := by
    dsimp only [Q0]
    positivity
  have hP : 1 <= P := by
    calc
      (1 : Real) = 1 ^ (17 / 40 : Real) := by rw [Real.one_rpow]
      _ <= X ^ (17 / 40 : Real) :=
        Real.rpow_le_rpow (by norm_num) hX (by norm_num)
      _ <= P := hPscale
  have hd0Data := mem_latticeFactorTenBand_iff.mp hd0Band
  have hd1Data := mem_latticeFactorTenBand_iff.mp hd1Band
  have hd0 : 0 < d0 := lt_of_lt_of_le Nat.zero_lt_one hd0Data.1
  have hd1 : 0 < d1 := lt_of_lt_of_le Nat.zero_lt_one hd1Data.1
  have hd0D0 : d0 <= D0 := hd0Data.2.1
  have hd1D1 : d1 <= D1 := hd1Data.2.1
  have hdD : d0 * d1 <= D0 * D1 := Nat.mul_le_mul hd0D0 hd1D1
  obtain ⟨u0, hu0⟩ := hd0Smooth
  obtain ⟨u1, hu1⟩ := hd1Smooth
  have hdvd : d0 * d1 ∣ 10 ^ (u0 + u1) := by
    rw [pow_add]
    exact Nat.mul_dvd_mul hu0 hu1
  have hDScale :
      (((E0 * (D0 * D1) : Nat) : Real)) <= A * X / P := by
    have hDQ : E0 * (D0 * D1) <= E0 * Q0 := by
      apply Nat.mul_le_mul_left E0
      dsimp only [Q0]
      have hfactor : 1 <= Q1 * G1 * G2 :=
        Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.mul_ne_zero hQ1.ne' hG1.ne') hG2.ne')
      calc
        D0 * D1 = 1 * (D0 * D1) := by ring
        _ <= (Q1 * G1 * G2) * (D0 * D1) := Nat.mul_le_mul_right _ hfactor
        _ = Q1 * G1 * G2 * D0 * D1 := by ring
    have hDQReal :
        ((E0 * (D0 * D1) : Nat) : Real) <= ((E0 * Q0 : Nat) : Real) := by
      exact_mod_cast hDQ
    exact hDQReal.trans hsourceScale
  have hlength : d0Length + d1Length + eLength <= length + loss := by
    apply finalSourceLengthBudget hP
    simpa only [A, X, D0, D1, E0, Nat.cast_mul, mul_comm, mul_left_comm,
      mul_assoc] using hDScale
  have hS1Nonneg : 0 <= S1 := by
    dsimp only [S1]
    exact latticeSOne_nonneg ..
  have hS2Nonneg : 0 <= S2 := by
    dsimp only [S2]
    exact latticeSTwo_nonneg ..
  have hS3Nonneg : 0 <= S3 := by
    dsimp only [S3]
    exact latticeSThree_nonneg ..
  let M : Real := (Q0 : Real) * E0
  let T1 : Real := (((D0 * D1 * Q1 * G1 ^ 2 : Nat) : Real) * E0)
  have hM : 1 <= M := by
    dsimp only [M]
    have hQ0One : (1 : Real) <= Q0 := by exact_mod_cast hQ0
    have hE0One : (1 : Real) <= E0 := by exact_mod_cast hE0
    calc
      (1 : Real) <= E0 := hE0One
      _ = 1 * E0 := by ring
      _ <= (Q0 : Real) * E0 :=
        mul_le_mul_of_nonneg_right hQ0One (by positivity)
  have hMscale : M <= A * X / P := by
    dsimp only [M]
    simpa only [Nat.cast_mul, mul_comm] using hsourceScale
  have hT1Nonneg : 0 <= T1 := by dsimp only [T1]; positivity
  have hT1M : T1 <= A * M := by
    have hcommon :
        0 <= ((D0 : Real) * D1 * Q1 * G1 * E0) := by positivity
    calc
      T1 = ((D0 : Real) * D1 * Q1 * G1 * E0) * G1 := by
        dsimp only [T1]
        norm_num only [Nat.cast_mul, Nat.cast_pow]
        ring
      _ <= ((D0 : Real) * D1 * Q1 * G1 * E0) * (A * G2) :=
        mul_le_mul_of_nonneg_left hGscale hcommon
      _ = A * M := by
        dsimp only [M, Q0]
        norm_num only [Nat.cast_mul]
        ring
  have hS1StandardRaw :
      S1 <= 4 * hybridConstant * latticeHybridTarget length T1 := by
    have hraw := latticeSOne_le_hybridBound digit length (d0 * d1)
      (D0 * D1) Q1 G1 E0 (Nat.mul_pos hd0 hd1) hG1 hE0 hdD
    simpa only [S1, T1, Nat.cast_mul, mul_assoc] using hraw
  have htargetOne :
      latticeHybridTarget length T1 <=
        (A ^ largeSieveAlpha + A * A ^ largeSieveSigma) *
          M ^ largeSieveAlpha :=
    latticeHybridTarget_le_finalStandard hA hM hP hT1Nonneg hT1M hMscale
  have hS1StandardFinal :
      S1 <= Cone * M ^ largeSieveAlpha := by
    calc
      S1 <= 4 * hybridConstant * latticeHybridTarget length T1 :=
        hS1StandardRaw
      _ <= 4 * hybridConstant *
          ((A ^ largeSieveAlpha + A * A ^ largeSieveSigma) *
            M ^ largeSieveAlpha) := by
        exact mul_le_mul_of_nonneg_left htargetOne (by
          norm_num [hybridConstant])
      _ = Cone * M ^ largeSieveAlpha := by
        dsimp only [Cone]
        ring
  let D : Real := (D0 : Real) * D1
  let L : Real := ((Q1 * G1 ^ 2 : Nat) : Real)
  have hD : 1 <= D := by
    dsimp only [D]
    have hD0One : (1 : Real) <= D0 := by exact_mod_cast hD0
    have hD1One : (1 : Real) <= D1 := by exact_mod_cast hD1
    calc
      (1 : Real) <= D1 := hD1One
      _ = 1 * D1 := by ring
      _ <= (D0 : Real) * D1 :=
        mul_le_mul_of_nonneg_right hD0One (by positivity)
  have hL : 0 <= L := by dsimp only [L]; positivity
  have hLQ : L <= A * (Q0 : Real) := by
    calc
      L = L * 1 := by ring
      _ <= L * D := mul_le_mul_of_nonneg_left hD hL
      _ <= A * (Q0 : Real) := by
        dsimp only [L, D, Q0]
        norm_num only [Nat.cast_mul, Nat.cast_pow]
        calc
          ((Q1 : Real) * G1 ^ 2) * ((D0 : Real) * D1) =
              ((Q1 : Real) * G1 * (D0 : Real) * D1) * G1 := by ring
          _ <= ((Q1 : Real) * G1 * (D0 : Real) * D1) * (A * G2) := by
            gcongr
          _ = A * ((Q1 : Real) * G1 * G2 * D0 * D1) := by ring
  have hLDQ : L * D <= A * (Q0 : Real) := by
    calc
      L * D = ((Q1 : Real) * G1 * (D0 : Real) * D1) * G1 := by
        dsimp only [L, D]
        norm_num only [Nat.cast_mul, Nat.cast_pow]
        ring
      _ <= ((Q1 : Real) * G1 * (D0 : Real) * D1) * (A * G2) := by
        gcongr
      _ = A * (Q0 : Real) := by
        dsimp only [Q0]
        norm_num only [Nat.cast_mul]
        ring
  have hS1AlternativeRaw :
      S1 <= CaltRaw *
        ((D * (E0 : Real)) ^ largeSieveAlpha * L ^ hybridResidualGrowth +
          (E0 : Real) ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
            X ^ hybridResidualHalfDecay) := by
    have hraw := latticeSOne_le_alternativeHybridBound loss digit
      (length := length) (dLength := d0Length + d1Length)
      (eLength := eLength) (d := d0 * d1) (u := u0 + u1)
      (Q := Q1) (G := G1) hlength (Nat.mul_pos hd0 hd1) (by
        simpa only [pow_add, D0, D1] using hdD) hdvd
    dsimp only at hraw
    simpa only [S1, CaltRaw, A, D, L, X, D0, D1, E0, Q1, G1,
      pow_add, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hraw
  have hAltBranches :
      (D * (E0 : Real)) ^ largeSieveAlpha * L ^ hybridResidualGrowth +
          (E0 : Real) ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
            X ^ hybridResidualHalfDecay <=
        (A ^ hybridResidualGrowth + A) *
          ((Q0 : Real) ^ hybridResidualGrowth *
              (D * (E0 : Real)) ^ largeSieveAlpha +
            (Q0 : Real) * E0 * D ^ (1 / 2 : Real) /
              X ^ hybridResidualHalfDecay) :=
    latticeAlternativeBranches_le_final hA (by exact_mod_cast hQ0)
      (by exact_mod_cast hE0) hD hL (Real.zero_lt_one.trans_le hX) hLQ hLDQ
  have hS1AlternativeFinal :
      S1 <= Calt *
        ((Q0 : Real) ^ hybridResidualGrowth *
            (D * (E0 : Real)) ^ largeSieveAlpha +
          (Q0 : Real) * E0 * D ^ (1 / 2 : Real) /
            X ^ hybridResidualHalfDecay) := by
    calc
      S1 <= CaltRaw *
          ((D * (E0 : Real)) ^ largeSieveAlpha * L ^ hybridResidualGrowth +
            (E0 : Real) ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
              X ^ hybridResidualHalfDecay) := hS1AlternativeRaw
      _ <= CaltRaw * ((A ^ hybridResidualGrowth + A) *
          ((Q0 : Real) ^ hybridResidualGrowth *
              (D * (E0 : Real)) ^ largeSieveAlpha +
            (Q0 : Real) * E0 * D ^ (1 / 2 : Real) /
              X ^ hybridResidualHalfDecay)) := by gcongr
      _ = Calt *
          ((Q0 : Real) ^ hybridResidualGrowth *
              (D * (E0 : Real)) ^ largeSieveAlpha +
            (Q0 : Real) * E0 * D ^ (1 / 2 : Real) /
              X ^ hybridResidualHalfDecay) := by
        dsimp only [Calt]
        ring
  have hS2Raw :
      S2 <= Ctwo * (((Q1 * G2 : Nat) : Real) ^ latticeSumSaving) *
        latticeHybridTarget length
          (((D0 * Q1 ^ 2 * G2 ^ 2 : Nat) : Real) * E0) := by
    dsimp only [S2]
    exact htwo digit length d0 D0 Q1 G2 E0 hd0 hd0D0 hQ1 hG2 hE0
  have hS2Target := finalSourceSTwoTarget_le
    (length := length) (Q1 := Q1) (G1 := G1) (G2 := G2)
    (D0 := D0) (D1 := D1) (E0 := E0) hQ1 hG1 hG2 hD0 hD1
  dsimp only at hS2Target
  have hQProduct : Q1 * G2 <= Q0 := by
    dsimp only [Q0]
    have hfactor : 1 <= G1 * D0 * D1 :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.mul_ne_zero hG1.ne' hD0.ne') hD1.ne')
    calc
      Q1 * G2 = Q1 * G2 * 1 := by ring
      _ <= Q1 * G2 * (G1 * D0 * D1) := Nat.mul_le_mul_left _ hfactor
      _ = Q1 * G1 * G2 * D0 * D1 := by ring
  have hQProductPower :
      (((Q1 * G2 : Nat) : Real) ^ latticeSumSaving) <=
        (Q0 : Real) ^ latticeSumSaving :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQProduct)
      latticeSumSaving_pos.le
  have hS2Final :
      S2 <= Ctwo * (Q0 : Real) ^ latticeSumSaving *
        (((Q0 : Real) ^ 2 * E0 /
            ((D0 : Real) * (D1 : Real) ^ 2 * (G1 : Real) ^ 2)) ^
              largeSieveAlpha +
          (Q0 : Real) ^ 2 * E0 /
            ((D0 : Real) * D1 * G1 * X ^ largeSieveSigma)) := by
    calc
      S2 <= Ctwo * (((Q1 * G2 : Nat) : Real) ^ latticeSumSaving) *
          latticeHybridTarget length
            (((D0 * Q1 ^ 2 * G2 ^ 2 : Nat) : Real) * E0) := hS2Raw
      _ = Ctwo * ((((Q1 * G2 : Nat) : Real) ^ latticeSumSaving) *
          latticeHybridTarget length
            (((D0 * Q1 ^ 2 * G2 ^ 2 : Nat) : Real) * E0)) := by ring
      _ <= Ctwo * ((Q0 : Real) ^ latticeSumSaving *
          latticeHybridTarget length
            (((D0 * Q1 ^ 2 * G2 ^ 2 : Nat) : Real) * E0)) := by
        apply mul_le_mul_of_nonneg_left _ hCtwo.le
        apply mul_le_mul_of_nonneg_right hQProductPower
        unfold latticeHybridTarget
        positivity
      _ = Ctwo * (Q0 : Real) ^ latticeSumSaving *
          latticeHybridTarget length
            (((D0 * Q1 ^ 2 * G2 ^ 2 : Nat) : Real) * E0) := by ring
      _ <= Ctwo * (Q0 : Real) ^ latticeSumSaving *
          (((Q0 : Real) ^ 2 * E0 /
              ((D0 : Real) * (D1 : Real) ^ 2 * (G1 : Real) ^ 2)) ^
                largeSieveAlpha +
            (Q0 : Real) ^ 2 * E0 /
              ((D0 : Real) * D1 * G1 * X ^ largeSieveSigma)) := by
        exact mul_le_mul_of_nonneg_left hS2Target
          (mul_nonneg hCtwo.le (Real.rpow_nonneg (by positivity) _))
  have hS3Final :
      S3 <= Cthree * (X ^ (23 / 80 : Real) +
        (Q0 : Real) * X ^ (23 / 80 : Real) / ((D0 : Real) * D1 * P)) := by
    have hraw := hthree digit length d0 Q1 G1 G2 D0 D1 E0 P
      hd0 hQ1 hG1 hG2 hD0 hD1 hE0 hP hd0D0
    dsimp only at hraw
    have hbound := hraw hsourceScale
    simpa only [S3, Q0, X, Nat.cast_mul, mul_assoc] using hbound
  have hConeK : Cone <= K :=
    le_trans (le_max_left Cone (max Calt (max Ctwo Cthree)))
      (le_max_right 1 (max Cone (max Calt (max Ctwo Cthree))))
  have hCaltK : Calt <= K :=
    le_trans (le_trans (le_max_left Calt (max Ctwo Cthree))
      (le_max_right Cone (max Calt (max Ctwo Cthree))))
      (le_max_right 1 (max Cone (max Calt (max Ctwo Cthree))))
  have hCtwoK : Ctwo <= K :=
    le_trans (le_trans (le_trans (le_max_left Ctwo Cthree)
      (le_max_right Calt (max Ctwo Cthree)))
      (le_max_right Cone (max Calt (max Ctwo Cthree))))
      (le_max_right 1 (max Cone (max Calt (max Ctwo Cthree))))
  have hCthreeK : Cthree <= K :=
    le_trans (le_trans (le_trans (le_max_right Ctwo Cthree)
      (le_max_right Calt (max Ctwo Cthree)))
      (le_max_right Cone (max Calt (max Ctwo Cthree))))
      (le_max_right 1 (max Cone (max Calt (max Ctwo Cthree))))
  have hnormalize {value coefficient bound : Real}
      (hvalue : 0 <= value) (hbound : 0 <= bound)
      (hcoefficient : coefficient <= K)
      (hraw : value <= coefficient * bound) :
      value / K <= bound := by
    apply (div_le_iff₀ hK).2
    simpa only [mul_comm] using
      hraw.trans (mul_le_mul_of_nonneg_right hcoefficient hbound)
  have hS1StandardNorm : S1 / K <= M ^ largeSieveAlpha :=
    hnormalize hS1Nonneg (by positivity) hConeK hS1StandardFinal
  have hS1AlternativeNorm : S1 / K <=
      (Q0 : Real) ^ hybridResidualGrowth *
          (D * (E0 : Real)) ^ largeSieveAlpha +
        (Q0 : Real) * E0 * D ^ (1 / 2 : Real) /
          X ^ hybridResidualHalfDecay :=
    hnormalize hS1Nonneg (by positivity) hCaltK hS1AlternativeFinal
  have hS2Norm : S2 / K <= (Q0 : Real) ^ latticeSumSaving *
      (((Q0 : Real) ^ 2 * E0 /
          ((D0 : Real) * (D1 : Real) ^ 2 * (G1 : Real) ^ 2)) ^
            largeSieveAlpha +
        (Q0 : Real) ^ 2 * E0 /
          ((D0 : Real) * D1 * G1 * X ^ largeSieveSigma)) :=
    hnormalize hS2Nonneg (by positivity) hCtwoK (by
      simpa only [mul_assoc] using hS2Final)
  have hS3Norm : S3 / K <= X ^ (23 / 80 : Real) +
      (Q0 : Real) * X ^ (23 / 80 : Real) / ((D0 : Real) * D1 * P) :=
    hnormalize hS3Nonneg (by positivity) hCthreeK hS3Final
  have hnormalized := hscalar X P (Q0 : Real) E0 D0 D1 G1
    (S1 / K) (S2 / K) (S3 / K) hX hP (by exact_mod_cast hQ0)
    (by exact_mod_cast hE0) (by exact_mod_cast hD0) (by exact_mod_cast hD1)
    (by exact_mod_cast hG1) hPscale hMscale (by positivity) (by positivity)
    (by positivity) (by simpa only [M] using hS1StandardNorm)
    (by simpa only [D] using hS1AlternativeNorm)
    hS2Norm hS3Norm
  change min (S1 * S2) (S1 * S3) <=
    C * ((Q0 : Real) ^ (1 - latticeSumSaving) *
      (E0 : Real) ^ (1 - latticeSumSaving))
  have hfirstScale :
      S1 * S2 = K ^ 2 * ((S1 / K) * (S2 / K)) := by
    field_simp
  have hsecondScale :
      S1 * S3 = K ^ 2 * ((S1 / K) * (S3 / K)) := by
    field_simp
  rw [hfirstScale, hsecondScale]
  rw [← mul_min_of_nonneg _ _ (sq_nonneg K)]
  calc
    K ^ 2 * min ((S1 / K) * (S2 / K)) ((S1 / K) * (S3 / K)) <=
        K ^ 2 * (Cscalar * ((Q0 : Real) ^ (1 - latticeSumSaving) *
          (E0 : Real) ^ (1 - latticeSumSaving))) := by gcongr
    _ = C * ((Q0 : Real) ^ (1 - latticeSumSaving) *
        (E0 : Real) ^ (1 - latticeSumSaving)) := by
      dsimp only [C]
      ring
end
end PrimesRestrictedDigits
