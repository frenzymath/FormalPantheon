import PrimesRestrictedDigits.LatticeEstimates.FinalSOne
import PrimesRestrictedDigits.LatticeEstimates.FinalScalar

/-!
# Source normalization for the final lattice estimate

These scalar bridges convert the exact estimates to the coefficient-normalized hypotheses of
`exists_latticeFinalScalarBound`.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Equation (14.9)'s tail is absorbed into its head at the source scale. -/
theorem latticeHybridTarget_le_finalStandard
    {length : Nat} {A M T P : Real}
    (hA : 1 <= A) (hM : 1 <= M) (hP : 1 <= P)
    (hT : 0 <= T) (hTM : T <= A * M)
    (hscale : M <= A * ((10 ^ length : Nat) : Real) / P) :
    latticeHybridTarget length T <=
      (A ^ largeSieveAlpha + A * A ^ largeSieveSigma) *
        M ^ largeSieveAlpha := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 <= X := by
    dsimp only [X]
    exact_mod_cast Nat.one_le_pow length 10 (by norm_num)
  have hXPos : 0 < X := Real.zero_lt_one.trans_le hX
  have hA0 : 0 <= A := le_trans (by norm_num) hA
  have hM0 : 0 <= M := le_trans (by norm_num) hM
  have hscale' : M <= A * X := by
    calc
      M <= A * X / P := hscale
      _ <= A * X := by
        apply (div_le_iff₀ (Real.zero_lt_one.trans_le hP)).2
        nlinarith [mul_nonneg hA0 hXPos.le]
  have hhead : T ^ largeSieveAlpha <=
      A ^ largeSieveAlpha * M ^ largeSieveAlpha := by
    calc
      T ^ largeSieveAlpha <= (A * M) ^ largeSieveAlpha :=
        Real.rpow_le_rpow hT hTM largeSieveAlpha_nonneg
      _ = A ^ largeSieveAlpha * M ^ largeSieveAlpha :=
        Real.mul_rpow hA0 hM0
  have hscalePower :
      M ^ largeSieveSigma / X ^ largeSieveSigma <=
        A ^ largeSieveSigma := by
    have hexponent :
        largeSieveSigma * (1 - (0 : Real)) <= largeSieveSigma := by
      simp
    exact latticeScale_rpow_div_rpow_le hA0 hX hM0
      largeSieveSigma_nonneg (by simpa using hscale') hexponent
  have hsplit :
      M = M ^ largeSieveAlpha * M ^ largeSieveSigma := by
    calc
      M = M ^ (1 : Real) := (Real.rpow_one M).symm
      _ = M ^ (largeSieveAlpha + largeSieveSigma) := by
        congr 1
        norm_num [largeSieveAlpha, largeSieveSigma]
      _ = M ^ largeSieveAlpha * M ^ largeSieveSigma :=
        Real.rpow_add (Real.zero_lt_one.trans_le hM) _ _
  have htail : T * X ^ (-largeSieveSigma) <=
      (A * A ^ largeSieveSigma) * M ^ largeSieveAlpha := by
    rw [Real.rpow_neg hXPos.le]
    calc
      T * (X ^ largeSieveSigma)⁻¹ <=
          (A * M) * (X ^ largeSieveSigma)⁻¹ := by gcongr
      _ = (A * (M ^ largeSieveAlpha * M ^ largeSieveSigma)) *
          (X ^ largeSieveSigma)⁻¹ :=
        congrArg (fun z : Real => (A * z) * (X ^ largeSieveSigma)⁻¹) hsplit
      _ = A * M ^ largeSieveAlpha *
          (M ^ largeSieveSigma / X ^ largeSieveSigma) := by
        ring
      _ <= A * M ^ largeSieveAlpha * A ^ largeSieveSigma := by gcongr
      _ = (A * A ^ largeSieveSigma) * M ^ largeSieveAlpha := by ring
  change latticeHybridTarget length T <= _
  unfold latticeHybridTarget
  change T ^ largeSieveAlpha + T * X ^ (-largeSieveSigma) <= _
  calc
    T ^ largeSieveAlpha + T * X ^ (-largeSieveSigma) <=
        A ^ largeSieveAlpha * M ^ largeSieveAlpha +
          (A * A ^ largeSieveSigma) * M ^ largeSieveAlpha :=
      add_le_add hhead htail
    _ = (A ^ largeSieveAlpha + A * A ^ largeSieveSigma) *
        M ^ largeSieveAlpha := by ring

/-- The two Alternative Hybrid Bound branches have the source's `Q0,D,E`
shape once `L<=A*Q` and `L*D<=A*Q` are made explicit. -/
theorem latticeAlternativeBranches_le_final
    {A Q E D L X : Real}
    (hA : 1 <= A) (hQ : 1 <= Q) (hE : 1 <= E)
    (hD : 1 <= D) (hL : 0 <= L) (hX : 0 < X)
    (hLQ : L <= A * Q) (hLDQ : L * D <= A * Q) :
    (D * E) ^ largeSieveAlpha * L ^ hybridResidualGrowth +
        E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
          X ^ hybridResidualHalfDecay <=
      (A ^ hybridResidualGrowth + A) *
        (Q ^ hybridResidualGrowth * (D * E) ^ largeSieveAlpha +
          Q * E * D ^ (1 / 2 : Real) /
            X ^ hybridResidualHalfDecay) := by
  have hA0 : 0 <= A := le_trans (by norm_num) hA
  have hQ0 : 0 <= Q := le_trans (by norm_num) hQ
  have hE0 : 0 <= E := le_trans (by norm_num) hE
  have hD0 : 0 <= D := le_trans (by norm_num) hD
  have hLPower : L ^ hybridResidualGrowth <=
      A ^ hybridResidualGrowth * Q ^ hybridResidualGrowth := by
    calc
      L ^ hybridResidualGrowth <= (A * Q) ^ hybridResidualGrowth :=
        Real.rpow_le_rpow hL hLQ (by
          norm_num [hybridResidualGrowth])
      _ = A ^ hybridResidualGrowth * Q ^ hybridResidualGrowth :=
        Real.mul_rpow hA0 hQ0
  have hfirst :
      (D * E) ^ largeSieveAlpha * L ^ hybridResidualGrowth <=
        A ^ hybridResidualGrowth *
          (Q ^ hybridResidualGrowth * (D * E) ^ largeSieveAlpha) := by
    calc
      (D * E) ^ largeSieveAlpha * L ^ hybridResidualGrowth <=
          (D * E) ^ largeSieveAlpha *
            (A ^ hybridResidualGrowth * Q ^ hybridResidualGrowth) := by gcongr
      _ = A ^ hybridResidualGrowth *
          (Q ^ hybridResidualGrowth * (D * E) ^ largeSieveAlpha) := by ring
  have hEPower : E ^ (5 / 6 : Real) <= E := by
    calc
      E ^ (5 / 6 : Real) <= E ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le hE (by norm_num)
      _ = E := Real.rpow_one _
  have hDsplit : D ^ (3 / 2 : Real) = D ^ (1 / 2 : Real) * D := by
    calc
      D ^ (3 / 2 : Real) = D ^ ((1 / 2 : Real) + 1) := by norm_num
      _ = D ^ (1 / 2 : Real) * D ^ (1 : Real) :=
        Real.rpow_add (Real.zero_lt_one.trans_le hD) _ _
      _ = D ^ (1 / 2 : Real) * D := by rw [Real.rpow_one]
  have hsecondNumerator :
      E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L <=
        A * (Q * E * D ^ (1 / 2 : Real)) := by
    rw [hDsplit]
    calc
      E ^ (5 / 6 : Real) * (D ^ (1 / 2 : Real) * D) * L <=
          E * (D ^ (1 / 2 : Real) * D) * L := by gcongr
      _ = E * D ^ (1 / 2 : Real) * (L * D) := by ring
      _ <= E * D ^ (1 / 2 : Real) * (A * Q) := by gcongr
      _ = A * (Q * E * D ^ (1 / 2 : Real)) := by ring
  have hsecond :
      E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
          X ^ hybridResidualHalfDecay <=
        A * (Q * E * D ^ (1 / 2 : Real) /
          X ^ hybridResidualHalfDecay) := by
    calc
      E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
          X ^ hybridResidualHalfDecay <=
        (A * (Q * E * D ^ (1 / 2 : Real))) /
          X ^ hybridResidualHalfDecay :=
        div_le_div_of_nonneg_right hsecondNumerator (by positivity)
      _ = A * (Q * E * D ^ (1 / 2 : Real) /
          X ^ hybridResidualHalfDecay) := by ring
  calc
    (D * E) ^ largeSieveAlpha * L ^ hybridResidualGrowth +
        E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
          X ^ hybridResidualHalfDecay <=
      A ^ hybridResidualGrowth *
          (Q ^ hybridResidualGrowth * (D * E) ^ largeSieveAlpha) +
        A * (Q * E * D ^ (1 / 2 : Real) /
          X ^ hybridResidualHalfDecay) := add_le_add hfirst hsecond
    _ <= (A ^ hybridResidualGrowth + A) *
        (Q ^ hybridResidualGrowth * (D * E) ^ largeSieveAlpha +
          Q * E * D ^ (1 / 2 : Real) /
            X ^ hybridResidualHalfDecay) := by
      have hfirstTerm :
          0 <= Q ^ hybridResidualGrowth * (D * E) ^ largeSieveAlpha := by
        positivity
      have hsecondTerm :
          0 <= Q * E * D ^ (1 / 2 : Real) /
            X ^ hybridResidualHalfDecay := by positivity
      nlinarith [Real.rpow_nonneg hA0 hybridResidualGrowth]

end

end PrimesRestrictedDigits
