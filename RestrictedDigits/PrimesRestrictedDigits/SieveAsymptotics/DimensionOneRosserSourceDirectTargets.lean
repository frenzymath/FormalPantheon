import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceDirectScalar
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeed
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceTargets

/-!
# Direct source targets above the selected cutoff

The rank-uniform high-seed estimate at the current coordinate is converted to both source
targets on the `s0 <= s` branch.
-/

namespace PrimesRestrictedDigits

private theorem sourceDirectNormalizedBoundary_lt_target
    {failure V D L s model aux : Real}
    (hV : 0 <= V) (hD : 1 <= D) (hLExp : Real.exp 1 <= L)
    (hs : 1 <= s) (hmodel : 0 <= model) (haux : 0 <= aux)
    (hfailure : failure < V / s ^ 2 * (aux * L ^ (-3 / 8 : Real))) :
    failure < V / s * (model + D * (L ^ (-1 / 3 : Real) * aux)) := by
  have hL : 0 < L := (Real.exp_pos 1).trans_le hLExp
  have hLone : 1 <= L := by
    have honeExp : 1 <= Real.exp 1 := Real.one_le_exp (by norm_num)
    exact honeExp.trans hLExp
  have hsPos : 0 < s := zero_lt_one.trans_le hs
  have hreserve : L ^ (-1 / 24 : Real) <= 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hLone (by norm_num)
  have hdecay0 : 0 <= L ^ (-1 / 3 : Real) :=
    (Real.rpow_pos_of_pos hL _).le
  have hpower : L ^ (-3 / 8 : Real) =
      L ^ (-1 / 3 : Real) * L ^ (-1 / 24 : Real) := by
    rw [<- Real.rpow_add hL]
    congr 1
    ring
  have hratio : L ^ (-1 / 24 : Real) / s <= D := by
    calc
      L ^ (-1 / 24 : Real) / s <= 1 :=
        (div_le_one hsPos).2 (hreserve.trans hs)
      _ <= D := hD
  have hsource0 : 0 <= L ^ (-1 / 3 : Real) * aux :=
    mul_nonneg hdecay0 haux
  have hscaled := mul_le_mul_of_nonneg_left hratio hsource0
  have hinner : (aux * L ^ (-3 / 8 : Real)) / s <=
      model + D * (L ^ (-1 / 3 : Real) * aux) := by
    calc
      (aux * L ^ (-3 / 8 : Real)) / s =
          (L ^ (-1 / 3 : Real) * aux) *
            (L ^ (-1 / 24 : Real) / s) := by rw [hpower]; ring
      _ <= (L ^ (-1 / 3 : Real) * aux) * D := hscaled
      _ <= model + D * (L ^ (-1 / 3 : Real) * aux) := by nlinarith
  calc
    failure < V / s ^ 2 * (aux * L ^ (-3 / 8 : Real)) := hfailure
    _ = V / s * ((aux * L ^ (-3 / 8 : Real)) / s) := by
      field_simp [hsPos.ne']
    _ <= V / s * (model + D * (L ^ (-1 / 3 : Real) * aux)) :=
      mul_le_mul_of_nonneg_left hinner (div_nonneg hV hsPos.le)

/-- The direct source branch supplies both sign targets at every rank. -/
theorem exists_dimensionOneRosserSourceDirectTargets_ge :
    exists S : Real, Real.exp 5000 + 1 <= S /\
      forall (P : Finset Nat) (R : Nat) {D level z s s0 : Real},
        1 <= D ->
        (forall p, p ∈ P -> p.Prime) ->
        2 <= level -> 2 <= z ->
        s = Real.log level / Real.log z ->
        S <= s0 -> s0 <= s -> Real.exp 1 <= Real.log level ->
        s0 ^ 50 = Real.log level *
          (Real.log (Real.log level)) ^ 3 ->
        dimensionOneRosserSourceUpperTarget P D R level z s /\
          dimensionOneRosserSourceLowerTarget P D R level z s := by
  obtain ⟨_C, S, _hC, hS, hscalar⟩ :=
    exists_dimensionOneRosserSeedEnvelope_sourceNormalized_ge
  refine ⟨S, hS, ?_⟩
  intro P R D level z s s0 hD hprime hlevel hz hs hs0Tail hs0s hLExp hsource
  have hsTail : S <= s := hs0Tail.trans hs0s
  have hsLarge : Real.exp 5000 + 1 <= s := hS.trans hsTail
  have hsPos : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hsOne : 1 <= s := by
    have hlargeOne : 1 < Real.exp 5000 + 1 := by
      linarith [Real.exp_pos 5000]
    exact hlargeOne.le.trans hsLarge
  have hs0Nonneg : 0 <= s0 := by
    have hs0Large : Real.exp 5000 + 1 <= s0 := hS.trans hs0Tail
    exact (dimensionOneRosserSeed_pos hs0Large).le
  have hpow : s0 ^ (50 : Nat) <= s ^ (50 : Nat) :=
    pow_le_pow_left₀ hs0Nonneg hs0s 50
  have hdom : Real.log level * (Real.log (Real.log level)) ^ 3 <= s ^ 50 := by
    rw [<- hsource]
    exact hpow
  have hLPos : 0 < Real.log level :=
    (Real.exp_pos 1).trans_le hLExp
  have hlogLOne : 1 <= Real.log (Real.log level) :=
    (Real.le_log_iff_exp_le hLPos).2 hLExp
  have hLleDom : Real.log level <=
      Real.log level * (Real.log (Real.log level)) ^ 3 := by
    calc
      Real.log level = Real.log level * 1 := by ring
      _ <= Real.log level * (Real.log (Real.log level)) ^ 3 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hlogLOne) hLPos.le
  have hpowStep : s ^ 50 <= s ^ 51 := by
    calc
      s ^ 50 = s ^ 50 * 1 := by ring
      _ <= s ^ 50 * s :=
        mul_le_mul_of_nonneg_left hsOne (pow_nonneg hsPos.le 50)
      _ = s ^ 51 := by ring
  have hband : Real.log level <= s ^ 51 :=
    hLleDom.trans (hdom.trans hpowStep)
  have hV : 0 <= sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
    (sieveDensityBelow_reciprocal_pos P z hprime).le
  have hupperRaw := dimensionOneRosserUpperFailurePartialSum_lt_seedEnvelope
    P R hprime hlevel hz hs hsLarge hband
  have hlowerRaw := dimensionOneRosserLowerFailurePartialSum_lt_seedEnvelope
    P R hprime hlevel hz hs hsLarge hband
  have hnormalized := hscalar hsTail hLExp hdom
  have houtside : 0 < sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s ^ 2 :=
    div_pos (sieveDensityBelow_reciprocal_pos P z hprime) (pow_pos hsPos 2)
  have hupper : upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
      level z R <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s ^ 2 *
        ((dimensionOneRosserArtificialFactor (Real.log level) 0 s *
          dimensionOneDelayScaledPlus s) *
          (Real.log level) ^ (-3 / 8 : Real)) :=
    hupperRaw.trans (mul_lt_mul_of_pos_left hnormalized.1 houtside)
  have hlower : lowerRosserFailurePartialSum P (fun p => (p : Real)⁻¹)
      level z R <
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s ^ 2 *
        ((dimensionOneRosserArtificialFactor (Real.log level) 0 s *
          dimensionOneDelayScaledMinus s) *
          (Real.log level) ^ (-3 / 8 : Real)) :=
    hlowerRaw.trans (mul_lt_mul_of_pos_left hnormalized.2 houtside)
  constructor
  · unfold dimensionOneRosserSourceUpperTarget
    apply sourceDirectNormalizedBoundary_lt_target
      (aux := dimensionOneRosserArtificialFactor (Real.log level) 0 s *
        dimensionOneDelayScaledPlus s) hV hD hLExp hsOne
      (dimensionOneRosserModelPlusPartialSum_nonneg R s)
      (mul_nonneg (Real.exp_pos _).le
        (dimensionOneDelayScaledPlus_pos hsPos).le)
    simpa only [dimensionOneRosserSourcePlusProfile,
      dimensionOneRosserPlusArtificialAux, mul_assoc] using hupper
  · unfold dimensionOneRosserSourceLowerTarget
    apply sourceDirectNormalizedBoundary_lt_target
      (aux := dimensionOneRosserArtificialFactor (Real.log level) 0 s *
        dimensionOneDelayScaledMinus s) hV hD hLExp hsOne
      (dimensionOneRosserModelMinusPartialSum_nonneg R s)
      (mul_nonneg (Real.exp_pos _).le
        (dimensionOneDelayScaledMinus_pos hsPos).le)
    simpa only [dimensionOneRosserSourceMinusProfile,
      dimensionOneRosserMinusArtificialAux, mul_assoc] using hlower

end PrimesRestrictedDigits
