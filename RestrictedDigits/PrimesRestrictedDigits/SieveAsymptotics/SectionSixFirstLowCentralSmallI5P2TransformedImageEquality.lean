import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P2TransformedGeometry
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P2AffineMeasureTransport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Fixed-delta P2 transformed-domain image equality

This module combines the P2 inequalities with the affine transport maps. It proves only the
exact image and inverse-preimage equalities at `delta = 1 / 1000000`; no measure, integration,
or cap claim is made.

Sources: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

set_option autoImplicit false

open Set

namespace PrimesRestrictedDigits

noncomputable section

private abbrev d744Delta : Real := 1 / 1000000
private abbrev d744A : Real := sectionSixThetaOne d744Delta
private abbrev d744Beta : Real := sectionSixThetaTwo d744Delta
private abbrev d744Gap : Real := sectionSixThetaGap d744Delta
private abbrev d744C : Real := 16 / 25

def sectionSixFirstLowCentralSmallI5P2Target :
    Set SectionSixAffineT :=
  sectionSixFirstLowCentralSmallUniformOuterRegion (1 / 1000000 : Real) ∩
    sectionSixFirstLowCentralSmallI5PairPattern (2 : Fin 4)

def sectionSixFirstLowCentralSmallI5P2Domain :
    Set SectionSixAffineT := {z |
  let d := z.1.1.1
  let r := z.1.1.2
  let s := z.1.2
  let q := z.2
  sectionSixThetaGap (1 / 1000000 : Real) ≤ d ∧
    d < sectionSixThetaOne (1 / 1000000 : Real) / 2 ∧
    0 < r ∧ 0 < q ∧ q ≤ s ∧ s ≤ r ∧
    2 * d + r + s < sectionSixThetaOne (1 / 1000000 : Real) ∧
    2 * r + d < 16 / 25 - sectionSixThetaTwo (1 / 1000000 : Real) ∧
    q ≤ (1 - sectionSixThetaTwo (1 / 1000000 : Real) - 3 * d - r - s) / 2}

private def d744Phi (z : SectionSixAffineT) : SectionSixAffineT :=
  sectionSixP2Phi d744Beta z

private def d744Psi (x : SectionSixAffineT) : SectionSixAffineT :=
  sectionSixP2Psi d744Beta x

private theorem d744Phi_image_subset_target :
    d744Phi '' sectionSixFirstLowCentralSmallI5P2Domain ⊆
      sectionSixFirstLowCentralSmallI5P2Target := by
  rintro x ⟨z, hz, rfl⟩
  change d744Gap ≤ z.1.1.1 ∧ z.1.1.1 < d744A / 2 ∧
      0 < z.1.1.2 ∧ 0 < z.2 ∧ z.2 ≤ z.1.2 ∧ z.1.2 ≤ z.1.1.2 ∧
      2 * z.1.1.1 + z.1.1.2 + z.1.2 < d744A ∧
      2 * z.1.1.2 + z.1.1.1 < d744C - d744Beta ∧
      z.2 ≤ (1 - d744Beta - 3 * z.1.1.1 - z.1.1.2 - z.1.2) / 2 at hz
  rcases hz with ⟨hd, hdHalf, hr, hq, hqs, hsr, hlow, hsq, hcap⟩
  have h := sectionSixFirstLowCentralSmallI5P2Transformed_converse
    (d := z.1.1.1) (r := z.1.1.2) (s := z.1.2) (q := z.2)
    hd hdHalf hr hq hqs hsr hlow hsq hcap
  simpa [sectionSixFirstLowCentralSmallI5P2Target, d744Phi,
    sectionSixP2Phi, sub_eq_add_neg, d744Beta, d744Delta,
    sectionSixThetaTwo] using h

private theorem d744Target_subset_phi_image :
    sectionSixFirstLowCentralSmallI5P2Target ⊆
      d744Phi '' sectionSixFirstLowCentralSmallI5P2Domain := by
  rintro x ⟨houter, hpat⟩
  have hg := sectionSixFirstLowCentralSmallI5P2Transformed_geometry houter hpat
  dsimp at hg
  rcases hg with ⟨hd, hdHalf, hq, hqs, hsr, hlow, hsq, hcap⟩
  let z : SectionSixAffineT := (((d744Beta - x.1.1.1,
      x.1.1.2 - (d744Beta - x.1.1.1)),
      x.1.2 - (d744Beta - x.1.1.1)),
      x.2 - (d744Beta - x.1.1.1))
  have hr : 0 < x.1.1.2 - (d744Beta - x.1.1.1) := by
    linarith
  have hz : z ∈ sectionSixFirstLowCentralSmallI5P2Domain := by
    change d744Gap ≤ z.1.1.1 ∧ z.1.1.1 < d744A / 2 ∧
      0 < z.1.1.2 ∧ 0 < z.2 ∧ z.2 ≤ z.1.2 ∧ z.1.2 ≤ z.1.1.2 ∧
      2 * z.1.1.1 + z.1.1.2 + z.1.2 < d744A ∧
      2 * z.1.1.2 + z.1.1.1 < d744C - d744Beta ∧
      z.2 ≤ (1 - d744Beta - 3 * z.1.1.1 - z.1.1.2 - z.1.2) / 2
    exact ⟨hd, hdHalf, hr, hq, hqs, hsr, hlow, hsq, hcap⟩
  refine ⟨z, hz, ?_⟩
  dsimp [z, d744Phi, sectionSixP2Phi]
  ext <;> ring

private theorem d744Phi_image_eq_target :
    d744Phi '' sectionSixFirstLowCentralSmallI5P2Domain =
      sectionSixFirstLowCentralSmallI5P2Target :=
  Set.Subset.antisymm d744Phi_image_subset_target d744Target_subset_phi_image

theorem sectionSixFirstLowCentralSmallI5P2Phi_image_eq_target :
    sectionSixP2Phi (sectionSixThetaTwo (1 / 1000000 : Real)) ''
        sectionSixFirstLowCentralSmallI5P2Domain =
      sectionSixFirstLowCentralSmallI5P2Target :=
  by simpa [d744Phi, d744Beta] using d744Phi_image_eq_target

theorem sectionSixFirstLowCentralSmallI5P2Psi_preimage_target_eq_domain :
    (sectionSixP2Psi (sectionSixThetaTwo (1 / 1000000 : Real))) ⁻¹'
        sectionSixFirstLowCentralSmallI5P2Domain =
      sectionSixFirstLowCentralSmallI5P2Target := by
  ext x
  constructor
  · intro hx
    change d744Psi x ∈ sectionSixFirstLowCentralSmallI5P2Domain at hx
    have htarget : d744Phi (d744Psi x) ∈
        sectionSixFirstLowCentralSmallI5P2Target := by
      rw [← d744Phi_image_eq_target]
      exact ⟨d744Psi x, hx, rfl⟩
    simpa [d744Phi, d744Psi, sectionSixP2Phi_comp_Psi] using htarget
  · intro hx
    have h := d744Target_subset_phi_image hx
    rcases h with ⟨z, hz, hzEq⟩
    change d744Psi x ∈ sectionSixFirstLowCentralSmallI5P2Domain
    rw [show d744Psi x = z by
      apply_fun d744Psi at hzEq
      symm
      simpa [d744Phi, d744Psi, sectionSixP2Psi_comp_Phi] using hzEq]
    exact hz

end
end PrimesRestrictedDigits
