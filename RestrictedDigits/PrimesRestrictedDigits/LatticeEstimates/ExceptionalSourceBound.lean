import PrimesRestrictedDigits.LatticeEstimates.ExceptionalSum

/-!
# Source-scale exceptional lattice bound

This file inserts the literal Lemma 14.4 scale relation into the sharp `S3` estimate. The real
parameter `P` represents the source product `N*K`.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem latticeSourceErrorScale_le
    {A P X : Real} {d Q1 G1 G2 D0 D1 E0 Q0 : Nat}
    (hX : 0 < X) (hP : 0 < P)
    (hG1 : 0 < G1) (hD0 : 0 < D0) (hD1 : 0 < D1)
    (hdD0 : d <= D0)
    (hQ0 : Q0 = Q1 * G1 * G2 * D0 * D1)
    (hscale : ((E0 * Q0 : Nat) : Real) <= A * X / P) :
    ((E0 * d * Q1 ^ 2 * G2 ^ 2 : Nat) : Real) / X <=
      A * (Q0 : Real) / (((D0 * D1 : Nat) : Real) * P) := by
  have hG1One : 1 <= G1 := hG1
  have hD1One : 1 <= D1 := hD1
  have hfactorNat : d * Q1 ^ 2 * G2 ^ 2 * (D0 * D1) <= Q0 ^ 2 := by
    rw [hQ0]
    calc
      d * Q1 ^ 2 * G2 ^ 2 * (D0 * D1) <=
          D0 * Q1 ^ 2 * G2 ^ 2 * (D0 * D1) := by gcongr
      _ <= (Q1 * G1 * G2 * D0 * D1) ^ 2 := by
        have hG1Sq : 1 <= G1 ^ 2 := Nat.one_le_pow 2 G1 hG1
        have hD1Sq : D1 <= D1 ^ 2 := by
          simpa only [pow_two, one_mul] using Nat.mul_le_mul_right D1 hD1One
        have htail : D1 <= G1 ^ 2 * D1 ^ 2 := by
          calc
            D1 <= D1 ^ 2 := hD1Sq
            _ = 1 * D1 ^ 2 := by ring
            _ <= G1 ^ 2 * D1 ^ 2 := Nat.mul_le_mul_right _ hG1Sq
        calc
          D0 * Q1 ^ 2 * G2 ^ 2 * (D0 * D1) =
              (Q1 ^ 2 * G2 ^ 2 * D0 ^ 2) * D1 := by ring
          _ <= (Q1 ^ 2 * G2 ^ 2 * D0 ^ 2) * (G1 ^ 2 * D1 ^ 2) :=
            Nat.mul_le_mul_left _ htail
          _ = (Q1 * G1 * G2 * D0 * D1) ^ 2 := by ring
  have hfactorReal :
      ((E0 * (d * Q1 ^ 2 * G2 ^ 2 * (D0 * D1)) : Nat) : Real) <=
        ((E0 * Q0 ^ 2 : Nat) : Real) := by
    exact_mod_cast Nat.mul_le_mul_left E0 hfactorNat
  have hD : (0 : Real) < ((D0 * D1 : Nat) : Real) := by positivity
  have hraw :
      ((E0 * d * Q1 ^ 2 * G2 ^ 2 : Nat) : Real) / X <=
        (((E0 * Q0 : Nat) : Real) / X) *
          ((Q0 : Real) / ((D0 * D1 : Nat) : Real)) := by
    have hleft :
        ((E0 * d * Q1 ^ 2 * G2 ^ 2 : Nat) : Real) / X =
          ((E0 * (d * Q1 ^ 2 * G2 ^ 2 * (D0 * D1)) : Nat) : Real) /
            (X * ((D0 * D1 : Nat) : Real)) := by
      norm_num only [Nat.cast_mul, Nat.cast_pow]
      field_simp
    have hright :
        (((E0 * Q0 : Nat) : Real) / X) *
            ((Q0 : Real) / ((D0 * D1 : Nat) : Real)) =
          ((E0 * Q0 ^ 2 : Nat) : Real) /
            (X * ((D0 * D1 : Nat) : Real)) := by
      norm_num only [Nat.cast_mul, Nat.cast_pow]
      field_simp
    rw [hleft, hright]
    exact (div_le_div_iff_of_pos_right (mul_pos hX hD)).2 hfactorReal
  have hscaleDiv : ((E0 * Q0 : Nat) : Real) / X <= A / P := by
    apply (div_le_iff₀ hX).2
    calc
      ((E0 * Q0 : Nat) : Real) <= A * X / P := hscale
      _ = (A / P) * X := by ring
  calc
    ((E0 * d * Q1 ^ 2 * G2 ^ 2 : Nat) : Real) / X <=
        (((E0 * Q0 : Nat) : Real) / X) *
          ((Q0 : Real) / ((D0 * D1 : Nat) : Real)) := hraw
    _ <= (A / P) * ((Q0 : Real) / ((D0 * D1 : Nat) : Real)) :=
      mul_le_mul_of_nonneg_right hscaleDiv (by positivity)
    _ = A * (Q0 : Real) / (((D0 * D1 : Nat) : Real) * P) := by
      field_simp

private theorem latticeSourceQZero_le
    {A P X : Real} {E0 Q0 : Nat}
    (hA : 0 < A) (hP : 1 <= P) (hX : 0 < X) (hE0 : 0 < E0)
    (hscale : ((E0 * Q0 : Nat) : Real) <= A * X / P) :
    (Q0 : Real) <= A * X := by
  have hQ0E : (Q0 : Real) <= ((E0 * Q0 : Nat) : Real) := by
    have hQ0ENat : Q0 <= E0 * Q0 := by
      calc
        Q0 = 1 * Q0 := by ring
        _ <= E0 * Q0 := Nat.mul_le_mul_right Q0 hE0
    exact_mod_cast hQ0ENat
  have hdiv : A * X / P <= A * X := by
    apply (div_le_iff₀ (lt_of_lt_of_le Real.zero_lt_one hP)).2
    nlinarith [mul_pos hA hX]
  exact hQ0E.trans (hscale.trans hdiv)

private theorem latticeSourceRpow_absorb
    {A X Q rho gap exponent : Real}
    (hA : 0 < A) (hX : 1 <= X) (hQNonneg : 0 <= Q)
    (hQ : Q <= A * X)
    (hrho : 0 < rho) (hrhoGap : rho <= gap) :
    Q ^ rho * X ^ (exponent - gap) <= A ^ rho * X ^ exponent := by
  have hXPos : 0 < X := Real.zero_lt_one.trans_le hX
  have hQPower : Q ^ rho <= (A * X) ^ rho :=
    Real.rpow_le_rpow hQNonneg hQ hrho.le
  have hExponent : rho + (exponent - gap) <= exponent := by linarith
  calc
    Q ^ rho * X ^ (exponent - gap) <=
        (A * X) ^ rho * X ^ (exponent - gap) :=
      mul_le_mul_of_nonneg_right hQPower (Real.rpow_nonneg hXPos.le _)
    _ = A ^ rho * (X ^ rho * X ^ (exponent - gap)) := by
      rw [Real.mul_rpow hA.le hXPos.le]
      ring
    _ = A ^ rho * X ^ (rho + (exponent - gap)) := by
      rw [Real.rpow_add hXPos]
    _ <= A ^ rho * X ^ exponent :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX hExponent)
        (Real.rpow_nonneg hA.le _)

/-- Equation (14.8) with every source-scale constant explicit. The output
constant depends only on the fixed divisor exponent and scale coefficient. -/
theorem exists_latticeSThree_le_sourceBound
    (rho A : Real) (hrho : 0 < rho)
    (hrhoGap : rho <= 127 / 5334560) (hA : 0 < A) :
    ∃ C : Real, 0 < C ∧
      ∀ (digit : Fin 10) (length d Q1 G1 G2 D0 D1 E0 : Nat) (P : Real),
        0 < d -> 0 < Q1 -> 0 < G1 -> 0 < G2 ->
        0 < D0 -> 0 < D1 -> 0 < E0 -> 1 <= P -> d <= D0 ->
        let Q0 : Nat := Q1 * G1 * G2 * D0 * D1
        ((E0 * Q0 : Nat) : Real) <=
            A * ((10 ^ length : Nat) : Real) / P ->
          latticeSThree digit length d Q1 G2 E0 <=
            C * ((((10 ^ length : Nat) : Real) ^ (23 / 80 : Real)) +
              (Q0 : Real) *
                (((10 ^ length : Nat) : Real) ^ (23 / 80 : Real)) /
                  (((D0 * D1 : Nat) : Real) * P)) := by
  obtain ⟨Cgeneric, hCgeneric, hgeneric⟩ :=
    exists_latticeSThree_le_generic rho hrho
  let C : Real := Cgeneric * max 1 A * A ^ rho
  have hmax : 0 < max 1 A := lt_of_lt_of_le Real.zero_lt_one (le_max_left _ _)
  have hApower : 0 < A ^ rho := Real.rpow_pos_of_pos hA rho
  refine ⟨C, mul_pos (mul_pos hCgeneric hmax) hApower, ?_⟩
  intro digit length d Q1 G1 G2 D0 D1 E0 P
    hd hQ1 hG1 hG2 hD0 hD1 hE0 hP hdD0
  dsimp only
  intro hscale
  let X : Real := ((10 ^ length : Nat) : Real)
  let Q0 : Nat := Q1 * G1 * G2 * D0 * D1
  let T : Real := ((E0 * d * Q1 ^ 2 * G2 ^ 2 : Nat) : Real) / X
  let Z : Real := (Q0 : Real) / (((D0 * D1 : Nat) : Real) * P)
  have hX : 0 < X := by positivity
  have hXOne : 1 <= X := by
    change (1 : Real) <= ((10 ^ length : Nat) : Real)
    exact_mod_cast Nat.one_le_pow length 10 (by norm_num)
  have hPPos : 0 < P := Real.zero_lt_one.trans_le hP
  have herror : T <= A * Z := by
    dsimp only [T, Z, X, Q0]
    have h := latticeSourceErrorScale_le
      hX hPPos hG1 hD0 hD1 hdD0 rfl hscale
    convert h using 1; ring
  have hQ0AX : (Q0 : Real) <= A * X := by
    exact latticeSourceQZero_le hA hP hX hE0 hscale
  have hQProductNat : Q1 * G2 <= Q0 := by
    dsimp only [Q0]
    have hfactor : 1 <= G1 * D0 * D1 :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
        (Nat.mul_ne_zero hG1.ne' hD0.ne') hD1.ne')
    calc
      Q1 * G2 = Q1 * G2 * 1 := by ring
      _ <= Q1 * G2 * (G1 * D0 * D1) := Nat.mul_le_mul_left _ hfactor
      _ = Q1 * G1 * G2 * D0 * D1 := by ring
  have hQProduct : ((Q1 * G2 : Nat) : Real) <= (Q0 : Real) := by
    exact_mod_cast hQProductNat
  have hmainPower :
      (((Q1 * G2 : Nat) : Real) ^ rho) *
          X ^ ((23 / 80 : Real) - 127 / 5334560) <=
        A ^ rho * X ^ (23 / 80 : Real) := by
    have hfirst := Real.rpow_le_rpow (by positivity) hQProduct hrho.le
    calc
      (((Q1 * G2 : Nat) : Real) ^ rho) *
          X ^ ((23 / 80 : Real) - 127 / 5334560) <=
        (Q0 : Real) ^ rho *
          X ^ ((23 / 80 : Real) - 127 / 5334560) :=
        mul_le_mul_of_nonneg_right hfirst (Real.rpow_nonneg hX.le _)
      _ <= A ^ rho * X ^ (23 / 80 : Real) :=
        latticeSourceRpow_absorb hA hXOne (by positivity) hQ0AX hrho hrhoGap
  have herrorFactor : 1 + T <= max 1 A * (1 + Z) := by
    have hOneMax : (1 : Real) <= max 1 A := le_max_left _ _
    have hAMax : A <= max 1 A := le_max_right _ _
    have hZ : 0 <= Z := by positivity
    calc
      1 + T <= 1 + A * Z := by linarith
      _ <= max 1 A + max 1 A * Z :=
        add_le_add hOneMax (mul_le_mul_of_nonneg_right hAMax hZ)
      _ = max 1 A * (1 + Z) := by ring
  have hraw := hgeneric digit length d Q1 G2 E0 hd hQ1 hG2
  calc
    latticeSThree digit length d Q1 G2 E0 <=
        Cgeneric * (((Q1 * G2 : Nat) : Real) ^ rho) * (1 + T) *
          X ^ ((23 / 80 : Real) - 127 / 5334560) := by
      simpa only [T, X] using hraw
    _ <= Cgeneric * (((Q1 * G2 : Nat) : Real) ^ rho) *
        (max 1 A * (1 + Z)) *
          X ^ ((23 / 80 : Real) - 127 / 5334560) := by
      gcongr
    _ = Cgeneric * max 1 A * (1 + Z) *
        ((((Q1 * G2 : Nat) : Real) ^ rho) *
          X ^ ((23 / 80 : Real) - 127 / 5334560)) := by ring
    _ <= Cgeneric * max 1 A * (1 + Z) *
        (A ^ rho * X ^ (23 / 80 : Real)) := by
      gcongr
    _ = C * (X ^ (23 / 80 : Real) +
        (Q0 : Real) * X ^ (23 / 80 : Real) /
          (((D0 * D1 : Nat) : Real) * P)) := by
      dsimp only [C, Z]
      ring

end

end PrimesRestrictedDigits
