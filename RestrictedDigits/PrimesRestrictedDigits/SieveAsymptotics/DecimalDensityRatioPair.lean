import PrimesRestrictedDigits.SieveAsymptotics.DecimalDensityRatio
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedScalars
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserLogTransform

/-!
# Pairwise decimal density ratios at the fixed Rosser splice

This packages one decimal dimension-one constant on every ordered pair of cutoffs and derives
the exact outer/fixed-splice normalization data.
-/

namespace PrimesRestrictedDigits

/-- A single coefficient controls every ordered pair of density cutoffs in a
closed real interval. -/
def sieveDensityRatioPairwiseBound
    (P : Finset Nat) (K lower upper : Real) : Prop :=
  forall (x y : Real), lower <= x -> x <= y -> y <= upper ->
    sieveDensityBelow P (fun p => (p : Real)⁻¹) x /
        sieveDensityBelow P (fun p => (p : Real)⁻¹) y <=
      (Real.log y / Real.log x) * (1 + K / Real.log x)

/-- A strict density-ratio estimate for one supplied coefficient extends to
weakly ordered cutoff pairs by treating the equality pair directly. -/
theorem sieveDensityRatioPairwiseBound_of_strict_on
    (P : Finset Nat) {K lower upper : Real}
    (hK : 0 <= K) (hprime : forall p, p ∈ P -> p.Prime)
    (hlower : 2 <= lower)
    (hStrict : forall x y : Real,
      lower <= x -> x < y -> y <= upper ->
      sieveDensityBelow P (fun p => (p : Real)⁻¹) x /
          sieveDensityBelow P (fun p => (p : Real)⁻¹) y <
        (Real.log y / Real.log x) * (1 + K / Real.log x)) :
    sieveDensityRatioPairwiseBound P K lower upper := by
  intro x y hlowerX hxy hyUpper
  rcases hxy.eq_or_lt with hxy | hxy
  · subst y
    have hxTwo : 2 <= x := hlower.trans hlowerX
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hV := sieveDensityBelow_reciprocal_pos P x hprime
    rw [div_self hV.ne', div_self hlogx.ne']
    have hquotient : 0 <= K / Real.log x := div_nonneg hK hlogx.le
    nlinarith
  · exact (hStrict x y hlowerX hxy hyUpper).le

/-- One decimal dimension-one coefficient controls all ordered cutoff pairs,
including equality. -/
theorem exists_decimalSieveDensityRatioPairwise_bound :
    exists K : Real, 2 <= K /\
      forall (P : Finset Nat) (lower upper : Real),
        (∀ p ∈ P, p.Prime) ->
        (∀ p ∈ P, ¬p ∣ 10) ->
        2 <= lower -> lower <= upper ->
        sieveDensityRatioPairwiseBound P K lower upper := by
  obtain ⟨K, hK, hRatio⟩ := exists_decimalSieveDensityRatio_bound
  refine ⟨K, hK, ?_⟩
  intro P lower upper hprime hdecimal hlower hlowerUpper
  apply sieveDensityRatioPairwiseBound_of_strict_on P (by linarith) hprime
    hlower
  intro x y hlowerX hxy _hyUpper
  exact hRatio P x y hprime hdecimal (hlower.trans hlowerX) hxy

/-- The arithmetic cutoff corresponding to the fixed bounded-coordinate
splice. -/
noncomputable def dimensionOneRosserFixedSpliceCutoff (level : Real) : Real :=
  level ^ (1 / dimensionOneRosserSecondSplice)

private theorem dimensionOneRosserFixedSplice_pos :
    0 < dimensionOneRosserSecondSplice :=
  zero_lt_one.trans_le one_le_dimensionOneRosserSecondSplice

private theorem level_rpow_one_div_eq_of_log_ratio
    {level z s : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (_hsPos : 0 < s) :
    level ^ (1 / s) = z := by
  have hlevelPos : 0 < level := by linarith
  have hzPos : 0 < z := by linarith
  have hlogLevel : 0 < Real.log level := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  apply Real.strictMonoOn_log.injOn
    (Real.rpow_pos_of_pos hlevelPos _) hzPos
  rw [log_rpow_one_div hlevelPos, hs]
  field_simp [hlogLevel.ne', hlogz.ne', _hsPos.ne']

/-- The distant cutoff lies strictly below the fixed splice cutoff, which is
weakly below the outer cutoff on the bounded coordinate range. -/
theorem dimensionOneRosserFixedSpliceCutoff_order
    {level z s s0 : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsUpper : s <= dimensionOneRosserSecondSplice)
    (hUs0 : dimensionOneRosserSecondSplice < s0) :
    level ^ (1 / s0) < dimensionOneRosserFixedSpliceCutoff level /\
      dimensionOneRosserFixedSpliceCutoff level <= z := by
  have hlevelOne : 1 < level := by linarith
  have hsPos : 0 < s := by linarith
  have hUPos := dimensionOneRosserFixedSplice_pos
  have hinvStrict : 1 / s0 < 1 / dimensionOneRosserSecondSplice :=
    one_div_lt_one_div_of_lt hUPos hUs0
  have hinvWeak : 1 / dimensionOneRosserSecondSplice <= 1 / s :=
    one_div_le_one_div_of_le hsPos hsUpper
  have hzEq := level_rpow_one_div_eq_of_log_ratio hlevel hz hs hsPos
  constructor
  · exact Real.rpow_lt_rpow_of_exponent_lt hlevelOne hinvStrict
  · unfold dimensionOneRosserFixedSpliceCutoff
    calc
      level ^ (1 / dimensionOneRosserSecondSplice) <= level ^ (1 / s) :=
        (Real.strictMono_rpow_of_base_gt_one hlevelOne).monotone hinvWeak
      _ = z := hzEq

/-- Below the fixed coordinate splice, the arithmetic splice cutoff is
strictly below the outer cutoff. -/
theorem dimensionOneRosserFixedSpliceCutoff_lt
    {level z s : Real}
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsUpper : s < dimensionOneRosserSecondSplice) :
    dimensionOneRosserFixedSpliceCutoff level < z := by
  have hlevelOne : 1 < level := by linarith
  have hsPos : 0 < s := by linarith
  have hinvStrict : 1 / dimensionOneRosserSecondSplice < 1 / s :=
    one_div_lt_one_div_of_lt hsPos hsUpper
  unfold dimensionOneRosserFixedSpliceCutoff
  calc
    level ^ (1 / dimensionOneRosserSecondSplice) < level ^ (1 / s) :=
      Real.rpow_lt_rpow_of_exponent_lt hlevelOne hinvStrict
    _ = z := level_rpow_one_div_eq_of_log_ratio hlevel hz hs hsPos

/-- At the fixed coordinate splice, the arithmetic splice cutoff equals the
outer cutoff. -/
theorem dimensionOneRosserFixedSpliceCutoff_eq
    {level z s : Real} (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsUpper : s = dimensionOneRosserSecondSplice) :
    dimensionOneRosserFixedSpliceCutoff level = z := by
  have hsPos : 0 < s := by
    rw [hsUpper]
    exact dimensionOneRosserFixedSplice_pos
  unfold dimensionOneRosserFixedSpliceCutoff
  rw [<- hsUpper]
  exact level_rpow_one_div_eq_of_log_ratio hlevel hz hs hsPos

/-- A pairwise density bound yields the two fixed-splice ratio families, the
cross-cutoff ratio, and its normalized scale conversion. -/
theorem dimensionOneRosserFixedSplice_density_data
    (P : Finset Nat) {K level z s s0 : Real}
    (hprime : ∀ p ∈ P, p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsLower : 2 <= s)
    (hsUpper : s <= dimensionOneRosserSecondSplice)
    (hUs0 : dimensionOneRosserSecondSplice < s0)
    (hPair : sieveDensityRatioPairwiseBound P K
      (level ^ (1 / s0)) z) :
    (forall x, level ^ (1 / s0) <= x ->
      x < dimensionOneRosserFixedSpliceCutoff level ->
      sieveDensityBelow P (fun p => (p : Real)⁻¹) x /
          sieveDensityBelow P (fun p => (p : Real)⁻¹)
            (dimensionOneRosserFixedSpliceCutoff level) <=
        (Real.log (dimensionOneRosserFixedSpliceCutoff level) /
          Real.log x) * (1 + K / Real.log x)) /\
    (forall x, dimensionOneRosserFixedSpliceCutoff level <= x -> x < z ->
      sieveDensityBelow P (fun p => (p : Real)⁻¹) x /
          sieveDensityBelow P (fun p => (p : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x)) /\
    sieveDensityBelow P (fun p => (p : Real)⁻¹)
          (dimensionOneRosserFixedSpliceCutoff level) /
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z <=
      (dimensionOneRosserSecondSplice / s) *
        (1 + K * dimensionOneRosserSecondSplice / Real.log level) /\
    sieveDensityBelow P (fun p => (p : Real)⁻¹)
          (dimensionOneRosserFixedSpliceCutoff level) /
        dimensionOneRosserSecondSplice <=
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
        (1 + K * dimensionOneRosserSecondSplice / Real.log level) := by
  have horder := dimensionOneRosserFixedSpliceCutoff_order
    hlevel hz hs hsLower hsUpper hUs0
  have hlevelPos : 0 < level := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsPos : 0 < s := by linarith
  have hUPos := dimensionOneRosserFixedSplice_pos
  have hlogzEq : Real.log z = Real.log level / s := by
    rw [hs]
    field_simp [hL.ne', hlogz.ne']
  have hlogzU : Real.log (dimensionOneRosserFixedSpliceCutoff level) =
      Real.log level / dimensionOneRosserSecondSplice := by
    unfold dimensionOneRosserFixedSpliceCutoff
    exact log_rpow_one_div hlevelPos
  have hhigh : forall x, level ^ (1 / s0) <= x ->
      x < dimensionOneRosserFixedSpliceCutoff level ->
      sieveDensityBelow P (fun p => (p : Real)⁻¹) x /
          sieveDensityBelow P (fun p => (p : Real)⁻¹)
            (dimensionOneRosserFixedSpliceCutoff level) <=
        (Real.log (dimensionOneRosserFixedSpliceCutoff level) /
          Real.log x) * (1 + K / Real.log x) := by
    intro x hx hxzU
    exact hPair x (dimensionOneRosserFixedSpliceCutoff level)
      hx hxzU.le horder.2
  have houter : forall x, dimensionOneRosserFixedSpliceCutoff level <= x ->
      x < z ->
      sieveDensityBelow P (fun p => (p : Real)⁻¹) x /
          sieveDensityBelow P (fun p => (p : Real)⁻¹) z <=
        (Real.log z / Real.log x) * (1 + K / Real.log x) := by
    intro x hzUx hxz
    exact hPair x z (horder.1.le.trans hzUx) hxz.le le_rfl
  have hcross := hPair (dimensionOneRosserFixedSpliceCutoff level) z
    horder.1.le horder.2 le_rfl
  have hratioExact :
      Real.log z / Real.log (dimensionOneRosserFixedSpliceCutoff level) *
          (1 + K / Real.log (dimensionOneRosserFixedSpliceCutoff level)) =
        (dimensionOneRosserSecondSplice / s) *
          (1 + K * dimensionOneRosserSecondSplice / Real.log level) := by
    rw [hlogzEq, hlogzU]
    field_simp [hL.ne', hsPos.ne', hUPos.ne']
  rw [hratioExact] at hcross
  refine ⟨hhigh, houter, hcross, ?_⟩
  have hVPos := sieveDensityBelow_reciprocal_pos P z hprime
  have hratioMul := mul_le_mul_of_nonneg_left hcross hVPos.le
  have hVzUBound :
      sieveDensityBelow P (fun p => (p : Real)⁻¹)
          (dimensionOneRosserFixedSpliceCutoff level) <=
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z *
          ((dimensionOneRosserSecondSplice / s) *
            (1 + K * dimensionOneRosserSecondSplice / Real.log level)) := by
    calc
      _ = sieveDensityBelow P (fun p => (p : Real)⁻¹) z *
          (sieveDensityBelow P (fun p => (p : Real)⁻¹)
              (dimensionOneRosserFixedSpliceCutoff level) /
            sieveDensityBelow P (fun p => (p : Real)⁻¹) z) := by
        field_simp [hVPos.ne']
      _ <= _ := hratioMul
  apply (div_le_iff₀ hUPos).2
  calc
    sieveDensityBelow P (fun p => (p : Real)⁻¹)
          (dimensionOneRosserFixedSpliceCutoff level) <= _ := hVzUBound
    _ = (sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (1 + K * dimensionOneRosserSecondSplice / Real.log level)) *
        dimensionOneRosserSecondSplice := by
      field_simp [hsPos.ne']

end PrimesRestrictedDigits
