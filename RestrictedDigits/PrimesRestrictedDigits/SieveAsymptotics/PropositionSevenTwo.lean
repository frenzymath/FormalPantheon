import PrimesRestrictedDigits.SieveAsymptotics.TypeIIArityOne
import PrimesRestrictedDigits.SieveAsymptotics.TypeIICellSupportMass
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionCardinalityAssembly
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionInteriorFamily
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRemainderMass
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIWeakSmallProductTail
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIWeakSmallProductTailScalars

/-!
# Proposition 7.2: the Type II estimate

This combines the corrected finite support sandwich, the interior and remainder family
estimates, the weak small-product tail, and the explicit one-prime branch. It is the
fixed-length decimal form of published Proposition 7.2.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The original region support is already contained in Maynard's ambient
carrier at the same natural cutoff. -/
theorem typeIIOriginalRegionSupport_filter_ambient_eq_self
    (XNat : Nat) {ell : Nat} (region : Set (Fin ell -> Real)) :
    (typeIIOriginalRegionSupport XNat region).filter
        (fun n => n ∈ maynardAmbientCarrier (XNat : Real)) =
      typeIIOriginalRegionSupport XNat region := by
  apply Finset.filter_eq_self.mpr
  intro n hn
  rw [mem_maynardAmbientCarrier]
  exact_mod_cast (mem_typeIIOriginalRegionSupport.mp hn).1

/-- Published Proposition 7.2 at decimal powers of ten. The coefficient is
fixed from the source region and eta before the global convenience margin,
threshold, decimal length, and excluded digit. -/
theorem exists_typeIIRegionEstimate_eta_upper
    (eta : Real) (heta : 0 < eta)
    {k : Nat} {region : Set (Fin (k + 1) -> Real)}
    (hregion : IsTypeIISourceRegion eta region)
    (hell : (((k + 1 : Nat) : Real) ≤ 2 / eta))
    (presentation : TypeIIAffineHalfspacePresentation region) :
    ∃ CregionEta : Real, 0 < CregionEta ∧
      ∀ epsilon : Real, 0 < epsilon ->
        IsTypeIIRegionConvenient epsilon region ->
        ∃ length0 : Nat, 1 ≤ length0 ∧
          ∀ length : Nat, length0 ≤ length ->
          ∀ digit : Fin 10,
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let delta : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let support : Finset Nat :=
              typeIIOriginalRegionSupport XNat region
            |((support.filter fun n => n ∈ A).card : Real) -
                (restrictedDigitDensity digit : Real) *
                  (A.card : Real) / X * (support.card : Real)| ≤
              CregionEta * delta * (A.card : Real) / Real.log X := by
  obtain ⟨scaleLength, hscaleLength, hscale⟩ :=
    exists_typeIIWeakSmallProductScaleThreshold
  cases k with
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      intro epsilon hepsilon hconvenient
      refine ⟨scaleLength, hscaleLength, ?_⟩
      intro length hlength digit
      let XNat : Nat := 10 ^ length
      let X : Real := (XNat : Real)
      let delta : Real := majorArcM2LogLogDelta XNat
      let A : Finset Nat := paddedRestrictedNumbers digit length
      let support : Finset Nat :=
        typeIIOriginalRegionSupport XNat region
      change |((support.filter fun n => n ∈ A).card : Real) -
          (restrictedDigitDensity digit : Real) *
            (A.card : Real) / X * (support.card : Real)| ≤
        1 * delta * (A.card : Real) / Real.log X
      have hregionEmpty : region = ∅ :=
        typeIIRegion_eq_empty_of_arity_one hepsilon hregion hconvenient
      have hsupportEmpty : support = ∅ := by
        dsimp only [support]
        rw [hregionEmpty]
        simp [typeIIOriginalRegionSupport, typeIIOriginalRegionPredicate]
      have hscaleAt := hscale length hlength
      have hXOne : (1 : Real) < X := by
        dsimp only [X, XNat]
        linarith [hscaleAt.1]
      have hlog : 0 < Real.log X := Real.log_pos hXOne
      have hdelta : 0 < delta := by
        simpa only [delta, XNat] using hscaleAt.2.1
      rw [hsupportEmpty]
      simp only [Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
        mul_zero, sub_self, abs_zero, one_mul]
      exact div_nonneg (mul_nonneg hdelta.le (by positivity)) hlog.le
  | succ k =>
      have hk : 1 ≤ k + 1 := by omega
      obtain ⟨Cinterior, hCinterior, hinterior⟩ :=
        exists_typeIIInteriorRegionFamilyError_eta_upper eta heta
      obtain ⟨Cremainder, hCremainder, hremainder⟩ :=
        exists_typeIIRemainderRegionFamilyMass_eta_upper eta heta hk
          hregion hell presentation
      obtain ⟨Ctail, hCtail, tailLength, htailLength, htail⟩ :=
        exists_typeIIWeakSmallProductTail_upper
      let CregionEta : Real := Cinterior + Cremainder + Ctail
      have hCregionEta : 0 < CregionEta := by
        dsimp only [CregionEta]
        positivity
      refine ⟨CregionEta, hCregionEta, ?_⟩
      intro epsilon hepsilon hconvenient
      obtain ⟨interiorLength, hinteriorLength, hinteriorAt⟩ :=
        hinterior epsilon hepsilon
      obtain ⟨remainderLength, hremainderLength, hremainderAt⟩ :=
        hremainder epsilon hepsilon hconvenient
      let length0 : Nat := max interiorLength
        (max remainderLength (max tailLength scaleLength))
      have hlength0 : 1 ≤ length0 :=
        hinteriorLength.trans <| by
          dsimp only [length0]
          exact Nat.le_max_left _ _
      refine ⟨length0, hlength0, ?_⟩
      intro length hlength digit
      have hinteriorLengthAt : interiorLength ≤ length :=
        (Nat.le_max_left interiorLength
          (max remainderLength (max tailLength scaleLength))).trans hlength
      have hremainderLengthAt : remainderLength ≤ length :=
        (Nat.le_max_left remainderLength (max tailLength scaleLength)).trans
          ((Nat.le_max_right interiorLength
            (max remainderLength (max tailLength scaleLength))).trans hlength)
      have htailLengthAt : tailLength ≤ length :=
        (Nat.le_max_left tailLength scaleLength).trans
          ((Nat.le_max_right remainderLength
            (max tailLength scaleLength)).trans
              ((Nat.le_max_right interiorLength
                (max remainderLength (max tailLength scaleLength))).trans
                  hlength))
      have hscaleLengthAt : scaleLength ≤ length :=
        (Nat.le_max_right tailLength scaleLength).trans
          ((Nat.le_max_right remainderLength
            (max tailLength scaleLength)).trans
              ((Nat.le_max_right interiorLength
                (max remainderLength (max tailLength scaleLength))).trans
                  hlength))
      let XNat : Nat := 10 ^ length
      let X : Real := (XNat : Real)
      let delta : Real := majorArcM2LogLogDelta XNat
      let A : Finset Nat := paddedRestrictedNumbers digit length
      let B : Finset Nat := maynardAmbientCarrier X
      let support : Finset Nat :=
        typeIIOriginalRegionSupport XNat region
      let interiorAnchors : Finset (Fin (k + 1) -> Nat) :=
        typeIIInteriorCubeAnchors delta region
      let remainderAnchors : Finset (Fin (k + 1) -> Nat) :=
        typeIIRemainderCubeAnchors delta region
      let supportCount : (Fin (k + 1) -> Nat) -> Finset Nat -> Real :=
        fun anchor C => typeIICellSupportCount XNat
          (scaledNaturalCubeAnchor delta anchor) delta eta C
      let lambda : Real :=
        (restrictedDigitDensity digit : Real) * (A.card : Real) / X
      let targetScale : Real := delta * (A.card : Real) / Real.log X
      change |((support.filter fun n => n ∈ A).card : Real) -
          lambda * (support.card : Real)| ≤
        CregionEta * delta * (A.card : Real) / Real.log X
      have hscaleAt := hscale length hscaleLengthAt
      have hXPos : 0 < X := by
        dsimp only [X, XNat]
        linarith [hscaleAt.1]
      have hdelta : 0 < delta := by
        simpa only [delta, XNat] using hscaleAt.2.1
      have hdeltaHalf : delta ≤ 1 / 2 := by
        simpa only [delta, XNat] using hscaleAt.2.2.1
      have hlengthOne : 1 ≤ length :=
        hinteriorLength.trans hinteriorLengthAt
      have hXNat : 1 < XNat := by
        dsimp only [XNat]
        exact Nat.one_lt_pow (by omega : length ≠ 0)
          (by norm_num : 1 < (10 : Nat))
      have hlambda : 0 ≤ lambda := by
        have hdensity :
            0 ≤ (restrictedDigitDensity digit : Real) :=
          restrictedDigitDensity_nonneg digit
        dsimp only [lambda]
        positivity
      have hfinite := typeIIOriginalRegionDiscrepancy_le
        (XNat := XNat) (k := k + 1) (eta := eta) (delta := delta)
        (lambda := lambda) A B hXNat heta hdelta hdeltaHalf hlambda hregion
      dsimp only at hfinite
      rw [typeIIOriginalRegionSupport_filter_ambient_eq_self XNat region]
        at hfinite
      have hinteriorBound := hinteriorAt length hinteriorLengthAt digit
        (k + 1) region hregion hconvenient hk hell
      have hremainderBound := hremainderAt length hremainderLengthAt digit
      have htailBound := htail length htailLengthAt digit
      have hinteriorBound' :
          (∑ anchor ∈ interiorAnchors,
            |supportCount anchor A - lambda * supportCount anchor B|) ≤
            Cinterior * targetScale := by
        simpa only [interiorAnchors, supportCount, lambda, targetScale,
          typeIICellSupportCount, XNat, X, delta, A, B] using hinteriorBound
      have hremainderBound' :
          remainderAnchors.sum (fun anchor =>
              supportCount anchor A + lambda * supportCount anchor B) ≤
            Cremainder * targetScale := by
        have hraw :
            remainderAnchors.sum (fun anchor =>
                supportCount anchor A + lambda * supportCount anchor B) ≤
              Cremainder * delta * (A.card : Real) / Real.log X := by
          simpa only [remainderAnchors, supportCount, lambda,
            XNat, X, delta, A, B] using hremainderBound
        calc
          remainderAnchors.sum (fun anchor =>
              supportCount anchor A + lambda * supportCount anchor B) ≤
            Cremainder * delta * (A.card : Real) / Real.log X := hraw
          _ = Cremainder * targetScale := by
            dsimp only [targetScale]
            ring
      have htailBound' :
          ((A \ typeIINearXCarrier XNat delta).card : Real) +
              lambda * ((B \ typeIINearXCarrier XNat delta).card : Real) ≤
            Ctail * targetScale := by
        have hraw :
            ((A \ typeIINearXCarrier XNat delta).card : Real) +
                lambda *
                  ((B \ typeIINearXCarrier XNat delta).card : Real) ≤
              Ctail * delta * (A.card : Real) / Real.log X := by
          simpa only [lambda, XNat, X, delta, A, B] using htailBound
        calc
          ((A \ typeIINearXCarrier XNat delta).card : Real) +
              lambda *
                ((B \ typeIINearXCarrier XNat delta).card : Real) ≤
            Ctail * delta * (A.card : Real) / Real.log X := hraw
          _ = Ctail * targetScale := by
            dsimp only [targetScale]
            ring
      apply hfinite.trans
      calc
        (∑ anchor ∈ interiorAnchors,
              |supportCount anchor A - lambda * supportCount anchor B|) +
            remainderAnchors.sum (fun anchor =>
              supportCount anchor A + lambda * supportCount anchor B) +
            (((A \ typeIINearXCarrier XNat delta).card : Real) +
              lambda *
                ((B \ typeIINearXCarrier XNat delta).card : Real)) ≤
          Cinterior * targetScale + Cremainder * targetScale +
            Ctail * targetScale :=
          add_le_add (add_le_add hinteriorBound' hremainderBound')
            htailBound'
        _ = CregionEta * delta * (A.card : Real) / Real.log X := by
          dsimp only [CregionEta, targetScale]
          ring

end

end PrimesRestrictedDigits
