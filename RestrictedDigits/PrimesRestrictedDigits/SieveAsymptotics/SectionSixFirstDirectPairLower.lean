import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstDirectPairFiniteLower

/-!
# Eventual lower bounds for the first direct pair pieces

The finite Buchstab lower bound is combined with the normalized log-prime pair limit and the
explicit summed rough-count error.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 140--141 and 145, Eqs. (6.7), (6.14), and
(6.15).
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace PrimesRestrictedDigits

noncomputable section

private theorem normalizedPrimeLogPairSum_congr
    (a b : Real) (X : Nat) {region : Set (Real × Real)}
    {f g : Real × Real -> Real} (hfg : Set.EqOn f g region) :
    normalizedPrimeLogPairSum a b X region f =
      normalizedPrimeLogPairSum a b X region g := by
  classical
  unfold normalizedPrimeLogPairSum
  apply Finset.sum_congr rfl
  intro pair hpair
  have hpair' := hpair
  unfold normalizedPrimeLogPairIndices at hpair'
  have hregion := (Finset.mem_filter.mp hpair').2
  rw [hfg hregion]

private theorem tendsto_sectionSixFirstPairKernelSum
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {region : Set (Real × Real)}
    (hregion : MeasurableSet region)
    (hbox : region ⊆
      Set.Ioc (sectionSixThetaGap epsilon) (1 / 2) ×ˢ
        Set.Ioc (sectionSixThetaGap epsilon) (1 / 2))
    (hfrontier : volume (frontier region) = 0)
    (extension : BoundedContinuousFunction (Real × Real) Real)
    (hextension : Set.EqOn extension sectionSixFirstPairBuchstabKernel region) :
    Tendsto
      (fun length : Nat =>
        normalizedPrimeLogPairSum (sectionSixThetaGap epsilon) (1 / 2)
          (10 ^ length) region sectionSixFirstPairBuchstabKernel)
      atTop
      (nhds (∫ x in region, sectionSixFirstPairBuchstabKernel x)) := by
  have hgap : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hgapHalf : sectionSixThetaGap epsilon < (1 / 2 : Real) := by
    rw [sectionSixThetaGap_eq]
    linarith
  have hlimit := tendsto_normalizedPrimeLogPairSum_powTen hgap hgapHalf
    hregion hbox hfrontier extension
  have hintegral : (∫ x in region, extension x) =
      ∫ x in region, sectionSixFirstPairBuchstabKernel x :=
    setIntegral_congr_fun hregion fun x hx => hextension hx
  rw [hintegral] at hlimit
  apply hlimit.congr'
  filter_upwards [] with length
  exact normalizedPrimeLogPairSum_congr _ _ _ hextension

private theorem tendsto_sectionSixFirstLowFarKernelSum
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Tendsto
      (fun length : Nat => normalizedPrimeLogPairSum
        (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
        (sectionSixFirstLowFarRegion epsilon)
        sectionSixFirstPairBuchstabKernel)
      atTop (nhds (sectionSixFirstLowFarIntegral epsilon)) := by
  simpa only [sectionSixFirstLowFarIntegral] using
    tendsto_sectionSixFirstPairKernelSum hepsilon hepsilonSmall
      (measurableSet_sectionSixFirstLowFarRegion epsilon)
      (sectionSixFirstLowFarRegion_subset_logBox epsilon hepsilonSmall)
      (volume_frontier_sectionSixFirstLowFarRegion epsilon)
      (sectionSixFirstPairBuchstabKernelExtension epsilon hepsilon
        hepsilonSmall)
      (sectionSixFirstPairBuchstabKernelExtension_eq_on_lowFarRegion
        epsilon hepsilon hepsilonSmall)

private theorem tendsto_sectionSixFirstHighFarKernelSum
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Tendsto
      (fun length : Nat => normalizedPrimeLogPairSum
        (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
        (sectionSixFirstHighFarRegion epsilon)
        sectionSixFirstPairBuchstabKernel)
      atTop (nhds (sectionSixFirstHighFarIntegral epsilon)) := by
  simpa only [sectionSixFirstHighFarIntegral] using
    tendsto_sectionSixFirstPairKernelSum hepsilon hepsilonSmall
      (measurableSet_sectionSixFirstHighFarRegion epsilon)
      (sectionSixFirstHighFarRegion_subset_logBox epsilon)
      (volume_frontier_sectionSixFirstHighFarRegion epsilon)
      (sectionSixFirstPairBuchstabKernelExtension epsilon hepsilon
        hepsilonSmall)
      (sectionSixFirstPairBuchstabKernelExtension_eq_on_highFarRegion
        epsilon hepsilon hepsilonSmall)

private theorem tendsto_sectionSixFirstHighCentralLargeKernelSum
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    Tendsto
      (fun length : Nat => normalizedPrimeLogPairSum
        (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
        (sectionSixFirstHighCentralLargeRegion epsilon)
        sectionSixFirstPairBuchstabKernel)
      atTop (nhds (sectionSixFirstHighCentralLargeIntegral epsilon)) := by
  simpa only [sectionSixFirstHighCentralLargeIntegral] using
    tendsto_sectionSixFirstPairKernelSum hepsilon hepsilonSmall
      (measurableSet_sectionSixFirstHighCentralLargeRegion epsilon)
      (sectionSixFirstHighCentralLargeRegion_subset_logBox epsilon)
      (volume_frontier_sectionSixFirstHighCentralLargeRegion epsilon)
      (sectionSixFirstPairBuchstabKernelExtension epsilon hepsilon
        hepsilonSmall)
      (sectionSixFirstPairBuchstabKernelExtension_eq_on_highCentralLargeRegion
        epsilon hepsilon hepsilonSmall)

private theorem sectionSixFirstDirectPair_lower_of_bounds
    {C epsilon rho integral normalized : Real}
    (hC : 0 <= C) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) (digit : Fin 10)
    (piece : SectionSixFirstPairPiece)
    (hpiece : IsSectionSixFirstDirectPairPiece piece)
    (hmain : sectionSixFirstPairBuchstabMainSum epsilon length piece =
      normalized / Real.log ((10 ^ length : Nat) : Real))
    (hnormalized : normalized <= integral + rho / 2)
    (herrorSmall :
      C * (2 * Real.log 4) ^ 2 /
          (sectionSixThetaGap epsilon ^ 4 *
            Real.log ((10 ^ length : Nat) : Real)) <= rho / 2)
    (hfinite :
      let densityMass : Real :=
        (restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real);
      (-densityMass *
          (sectionSixFirstPairBuchstabMainSum epsilon length piece +
            C * sectionSixFirstPairRoughErrorSum epsilon length piece)) <=
        sectionSixFirstPairPieceSum epsilon digit length piece) :
    let X : Real := ((10 ^ length : Nat) : Real);
    let scale : Real :=
      (restrictedDigitDensity digit : Real) *
        ((paddedRestrictedNumbers digit length).card : Real) / Real.log X;
    (-scale * (integral + rho)) <=
      sectionSixFirstPairPieceSum epsilon digit length piece := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let densityMass : Real := (restrictedDigitDensity digit : Real) *
    ((paddedRestrictedNumbers digit length).card : Real)
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast sectionSixFirst_direct_hXNat hlength
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hgap : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hdensity : (0 : Real) <= (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split <;> norm_num
  have hdensityMass : 0 <= densityMass := by
    dsimp only [densityMass]
    exact mul_nonneg hdensity (by positivity)
  have herror := sectionSixFirstDirectPairRoughErrorSum_le epsilon hepsilon
    hepsilonSmall hlength hpiece
  have herrorScaled :
      C * sectionSixFirstPairRoughErrorSum epsilon length piece <=
        (rho / 2) / Real.log X := by
    calc
      C * sectionSixFirstPairRoughErrorSum epsilon length piece <=
          C * ((2 * Real.log 4) ^ 2 /
            (sectionSixThetaGap epsilon ^ 4 * Real.log X ^ 2)) :=
        mul_le_mul_of_nonneg_left (by simpa only [X] using herror) hC
      _ = (C * (2 * Real.log 4) ^ 2 /
          (sectionSixThetaGap epsilon ^ 4 * Real.log X)) /
            Real.log X := by
        field_simp [hgap.ne', hlogX.ne']
      _ <= (rho / 2) / Real.log X :=
        div_le_div_of_nonneg_right
          (by simpa only [X] using herrorSmall) hlogX.le
  have hbracket :
      sectionSixFirstPairBuchstabMainSum epsilon length piece +
          C * sectionSixFirstPairRoughErrorSum epsilon length piece <=
        (integral + rho) / Real.log X := by
    rw [hmain]
    calc
      normalized / Real.log X +
          C * sectionSixFirstPairRoughErrorSum epsilon length piece <=
        (integral + rho / 2) / Real.log X +
          (rho / 2) / Real.log X :=
        add_le_add (div_le_div_of_nonneg_right hnormalized hlogX.le)
          herrorScaled
      _ = (integral + rho) / Real.log X := by ring
  dsimp only
  change -(densityMass / Real.log X) * (integral + rho) <= _
  calc
    -(densityMass / Real.log X) * (integral + rho) =
        -densityMass * ((integral + rho) / Real.log X) := by ring
    _ <= -densityMass *
        (sectionSixFirstPairBuchstabMainSum epsilon length piece +
          C * sectionSixFirstPairRoughErrorSum epsilon length piece) := by
      simpa only [neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_left hbracket hdensityMass)
    _ <= sectionSixFirstPairPieceSum epsilon digit length piece := by
      simpa only [densityMass] using hfinite

theorem exists_sectionSixFirstDirectPairPieces_lower
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (rho : Real) (hrho : 0 < rho) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length -> ∀ digit : Fin 10,
        let X : Real := ((10 ^ length : Nat) : Real);
        let scale : Real :=
          (restrictedDigitDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X;
        (-scale * (sectionSixFirstLowFarIntegral epsilon + rho)) <=
            sectionSixFirstPairPieceSum epsilon digit length .lowFar ∧
          (-scale * (sectionSixFirstHighFarIntegral epsilon + rho)) <=
            sectionSixFirstPairPieceSum epsilon digit length .highFar ∧
          (-scale *
              (sectionSixFirstHighCentralLargeIntegral epsilon + rho)) <=
            sectionSixFirstPairPieceSum epsilon digit length
              .highCentralLarge := by
  obtain ⟨C, hC, hfinite⟩ :=
    exists_sectionSixFirstDirectPairFiniteLowerConstant
  let lowSum : Nat -> Real := fun length =>
    normalizedPrimeLogPairSum (sectionSixThetaGap epsilon) (1 / 2)
      (10 ^ length) (sectionSixFirstLowFarRegion epsilon)
      sectionSixFirstPairBuchstabKernel
  let highSum : Nat -> Real := fun length =>
    normalizedPrimeLogPairSum (sectionSixThetaGap epsilon) (1 / 2)
      (10 ^ length) (sectionSixFirstHighFarRegion epsilon)
      sectionSixFirstPairBuchstabKernel
  let centralSum : Nat -> Real := fun length =>
    normalizedPrimeLogPairSum (sectionSixThetaGap epsilon) (1 / 2)
      (10 ^ length) (sectionSixFirstHighCentralLargeRegion epsilon)
      sectionSixFirstPairBuchstabKernel
  have hlowTendsto : Tendsto lowSum atTop
      (nhds (sectionSixFirstLowFarIntegral epsilon)) := by
    simpa only [lowSum] using
      tendsto_sectionSixFirstLowFarKernelSum hepsilon hepsilonSmall
  have hhighTendsto : Tendsto highSum atTop
      (nhds (sectionSixFirstHighFarIntegral epsilon)) := by
    simpa only [highSum] using
      tendsto_sectionSixFirstHighFarKernelSum hepsilon hepsilonSmall
  have hcentralTendsto : Tendsto centralSum atTop
      (nhds (sectionSixFirstHighCentralLargeIntegral epsilon)) := by
    simpa only [centralSum] using
      tendsto_sectionSixFirstHighCentralLargeKernelSum hepsilon hepsilonSmall
  have hlow : ∀ᶠ length : Nat in atTop,
      lowSum length <= sectionSixFirstLowFarIntegral epsilon + rho / 2 :=
    (hlowTendsto.eventually_lt_const (by linarith)).mono fun _ h => h.le
  have hhigh : ∀ᶠ length : Nat in atTop,
      highSum length <= sectionSixFirstHighFarIntegral epsilon + rho / 2 :=
    (hhighTendsto.eventually_lt_const (by linarith)).mono fun _ h => h.le
  have hcentral : ∀ᶠ length : Nat in atTop,
      centralSum length <=
          sectionSixFirstHighCentralLargeIntegral epsilon + rho / 2 :=
    (hcentralTendsto.eventually_lt_const (by linarith)).mono fun _ h => h.le
  let X : Nat -> Real := fun length => ((10 ^ length : Nat) : Real)
  let errorCoefficient : Real :=
    C * (2 * Real.log 4) ^ 2 / sectionSixThetaGap epsilon ^ 4
  have hXTendsto : Tendsto X atTop atTop := by
    simpa only [X, Nat.cast_pow, Nat.cast_ofNat] using
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Real) < 10)
  have herrorTendsto : Tendsto
      (fun length : Nat => errorCoefficient / Real.log (X length))
      atTop (nhds 0) :=
    (Real.tendsto_log_atTop.comp hXTendsto).const_div_atTop errorCoefficient
  have herror : ∀ᶠ length : Nat in atTop,
      errorCoefficient / Real.log (X length) <= rho / 2 :=
    (herrorTendsto.eventually_lt_const (by positivity)).mono fun _ h => h.le
  have hevent : ∀ᶠ length : Nat in atTop,
      lowSum length <= sectionSixFirstLowFarIntegral epsilon + rho / 2 ∧
        highSum length <= sectionSixFirstHighFarIntegral epsilon + rho / 2 ∧
        centralSum length <=
          sectionSixFirstHighCentralLargeIntegral epsilon + rho / 2 ∧
        errorCoefficient / Real.log (X length) <= rho / 2 ∧
        1 <= length := by
    filter_upwards [hlow, hhigh, hcentral, herror,
      eventually_ge_atTop (1 : Nat)] with length hlowAt hhighAt hcentralAt
        herrorAt hlength
    exact ⟨hlowAt, hhighAt, hcentralAt, herrorAt, hlength⟩
  obtain ⟨length1, hlength1⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 length1, le_max_left _ _, ?_⟩
  intro length hlength digit
  have hAt := hlength1 length ((le_max_right 1 length1).trans hlength)
  rcases hAt with ⟨hlowAt, hhighAt, hcentralAt, herrorAt, hlengthOne⟩
  have herrorAt' :
      C * (2 * Real.log 4) ^ 2 /
          (sectionSixThetaGap epsilon ^ 4 *
            Real.log ((10 ^ length : Nat) : Real)) <= rho / 2 := by
    convert herrorAt using 1
    simp only [errorCoefficient, X, div_eq_mul_inv, mul_inv_rev]
    ring
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact sectionSixFirstDirectPair_lower_of_bounds hC.le hepsilon
      hepsilonSmall hlengthOne digit .lowFar (Or.inl rfl)
      (sectionSixFirstLowFarBuchstabMainSum_eq epsilon hepsilon
        hepsilonSmall hlengthOne)
      hlowAt herrorAt'
      (hfinite epsilon hepsilon hepsilonSmall hlengthOne digit .lowFar
        (Or.inl rfl))
  · exact sectionSixFirstDirectPair_lower_of_bounds hC.le hepsilon
      hepsilonSmall hlengthOne digit .highFar (Or.inr (Or.inl rfl))
      (sectionSixFirstHighFarBuchstabMainSum_eq epsilon hepsilon
        hepsilonSmall hlengthOne)
      hhighAt herrorAt'
      (hfinite epsilon hepsilon hepsilonSmall hlengthOne digit .highFar
        (Or.inr (Or.inl rfl)))
  · exact sectionSixFirstDirectPair_lower_of_bounds hC.le hepsilon
      hepsilonSmall hlengthOne digit .highCentralLarge
      (Or.inr (Or.inr rfl))
      (sectionSixFirstHighCentralLargeBuchstabMainSum_eq epsilon hepsilon
        hepsilonSmall hlengthOne)
      hcentralAt herrorAt'
      (hfinite epsilon hepsilon hepsilonSmall hlengthOne digit
        .highCentralLarge (Or.inr (Or.inr rfl)))

theorem exists_sectionSixFirstDirectPairPieces_sum_lower
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (rho : Real) (hrho : 0 < rho) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length -> ∀ digit : Fin 10,
        let X : Real := ((10 ^ length : Nat) : Real);
        let scale : Real :=
          (restrictedDigitDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X;
        (-scale *
            (sectionSixFirstLowFarIntegral epsilon +
              sectionSixFirstHighFarIntegral epsilon +
              sectionSixFirstHighCentralLargeIntegral epsilon + rho)) <=
          sectionSixFirstPairPieceSum epsilon digit length .lowFar +
            sectionSixFirstPairPieceSum epsilon digit length .highFar +
            sectionSixFirstPairPieceSum epsilon digit length
              .highCentralLarge := by
  obtain ⟨length0, hlength0, hlower⟩ :=
    exists_sectionSixFirstDirectPairPieces_lower epsilon hepsilon
      hepsilonSmall (rho / 3) (by positivity)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  have hpieces := hlower length hlength digit
  dsimp only at hpieces ⊢
  rcases hpieces with ⟨hlow, hhigh, hcentral⟩
  calc
    _ =
        (-((restrictedDigitDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log ((10 ^ length : Nat) : Real)) *
            (sectionSixFirstLowFarIntegral epsilon + rho / 3)) +
          (-((restrictedDigitDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log ((10 ^ length : Nat) : Real)) *
            (sectionSixFirstHighFarIntegral epsilon + rho / 3)) +
          (-((restrictedDigitDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log ((10 ^ length : Nat) : Real)) *
            (sectionSixFirstHighCentralLargeIntegral epsilon + rho / 3)) := by
          ring
    _ <= sectionSixFirstPairPieceSum epsilon digit length .lowFar +
          sectionSixFirstPairPieceSum epsilon digit length .highFar +
          sectionSixFirstPairPieceSum epsilon digit length
            .highCentralLarge := add_le_add (add_le_add hlow hhigh) hcentral

end

end PrimesRestrictedDigits
