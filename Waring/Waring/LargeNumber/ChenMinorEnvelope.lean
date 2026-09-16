import Waring.Analytic.ChenTenMinorPointwise
import Waring.Analytic.ChenTenMajorArcTranslation
import Waring.LargeNumber.ChenMinorNumerics

/-!
# The corrected pointwise envelope for Chen's minor arcs

This replaces the invalid fifteenth-power split in English equation (44) and
Chinese equation (34) [CHEN1964-EN, p. 1568; CHEN1964-ZH, p. 734; D-016].
-/

set_option autoImplicit false

namespace Waring.LargeNumber

noncomputable section

/-- The corrected Lemma 9 term in the common minor-arc bound. -/
def chenMinorPrimaryTerm (P : Nat) : Real :=
  (2 : Real) ^ (6 / 8 : Real) * (161 : Real) ^ (1 / 16 : Real) *
    (P : Real) ^ (19 / 20 : Real) *
      (Real.log P + 4) ^ (15 / 16 : Real)

/-- The phase-perturbation term in the common minor-arc bound. -/
def chenMinorSecondaryTerm (P : Nat) : Real :=
  (P : Real) ^ (24 / 25 : Real)

/-- The valid fifteenth-power envelope replacing the false power split in
the source's final equation. -/
def chenMinorFifteenthEnvelope (P : Nat) : Real :=
  max (((15 / 14 : Real) * chenMinorPrimaryTerm P) ^ 15)
    ((15 * chenMinorSecondaryTerm P) ^ 15)

/-- The corrected Lemma 9 primary term is nonnegative. -/
theorem chenMinorPrimaryTerm_nonneg (P : Nat) :
    0 ≤ chenMinorPrimaryTerm P := by
  unfold chenMinorPrimaryTerm
  positivity

/-- The phase-perturbation term is nonnegative. -/
theorem chenMinorSecondaryTerm_nonneg (P : Nat) :
    0 ≤ chenMinorSecondaryTerm P := by
  unfold chenMinorSecondaryTerm
  positivity

/-- The maximum defining the corrected fifteenth-power envelope is nonnegative. -/
theorem chenMinorFifteenthEnvelope_nonneg (P : Nat) :
    0 ≤ chenMinorFifteenthEnvelope P := by
  unfold chenMinorFifteenthEnvelope
  exact (pow_nonneg
    (mul_nonneg (by norm_num) (chenMinorPrimaryTerm_nonneg P)) 15).trans
      (le_max_left _ _)

/-- Every representation integrand on a minor arc is bounded by the corrected
fifteenth-power envelope. -/
theorem norm_chenTenRepresentationIntegrand_le_minorEnvelope
    {P : Nat} (hP : 10 ^ 157 ≤ P) (N : Nat) {alpha : Real}
    (halpha : alpha ∈ Analytic.chenTenMinorArcs P) :
    ‖Analytic.chenTenRepresentationIntegrand P N alpha‖ ≤
      chenMinorFifteenthEnvelope P := by
  have hpointwise :=
    Analytic.norm_fifthPowerExponentialSum_le_of_mem_chenTenMinorArcs
      hP halpha
  have hpower :
      ‖Analytic.fifthPowerExponentialSum P alpha‖ ^ 15 ≤
        (chenMinorPrimaryTerm P + chenMinorSecondaryTerm P) ^ 15 := by
    apply pow_le_pow_left₀ (norm_nonneg _) _ 15
    simpa [chenMinorPrimaryTerm, chenMinorSecondaryTerm] using hpointwise
  calc
    ‖Analytic.chenTenRepresentationIntegrand P N alpha‖ =
        ‖Analytic.fifthPowerExponentialSum P alpha‖ ^ 15 := by
      unfold Analytic.chenTenRepresentationIntegrand
      rw [norm_mul, norm_pow]
      have hphase := Analytic.norm_chenTenTargetPhase N alpha
      have hphase' :
          ‖Complex.exp
            (-2 * Real.pi * Complex.I * (alpha * (N : Real)))‖ = 1 := by
        simpa [Analytic.chenTenTargetPhase] using hphase
      rw [hphase']
      ring
    _ ≤ (chenMinorPrimaryTerm P + chenMinorSecondaryTerm P) ^ 15 := hpower
    _ ≤ chenMinorFifteenthEnvelope P := by
      exact add_pow_fifteen_le_max_scaled
        (chenMinorPrimaryTerm_nonneg P)
        (chenMinorSecondaryTerm_nonneg P)

end

end Waring.LargeNumber
