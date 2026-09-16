import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5PairPatterns
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstUniformIntegralRegions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# P2 transformed-domain geometry

This module exports the fixed-delta affine geometry for the low-central-small P2 pattern. It
contains no measure transport, Jacobian, kernel estimate, finite subdivision, or I5 cap.
Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

set_option autoImplicit false

open Set
namespace PrimesRestrictedDigits

noncomputable section

private abbrev δ : Real := 1 / 1000000
private abbrev A : Real := sectionSixThetaOne δ
private abbrev β : Real := sectionSixThetaTwo δ
private abbrev g : Real := sectionSixThetaGap δ
private abbrev C : Real := 16 / 25

theorem sectionSixFirstLowCentralSmallI5P2Transformed_geometry
    {x : (((Real × Real) × Real) × Real)}
    (houter : x ∈ sectionSixFirstLowCentralSmallUniformOuterRegion δ)
    (hpat : x ∈ sectionSixFirstLowCentralSmallI5PairPattern (2 : Fin 4)) :
    let u := x.1.1.1
    let v := x.1.1.2
    let w := x.1.2
    let t := x.2
    let d := β - u
    let r := v - d
    let s := w - d
    let q := t - d
    g ≤ d ∧ d < A / 2 ∧ 0 < q ∧ q ≤ s ∧ s ≤ r ∧
      2 * d + r + s < A ∧ 2 * r + d < C - β ∧
      q ≤ (1 - β - 3 * d - r - s) / 2 := by
  rcases houter with ⟨hgap, htw, hwv, hvu, huA, huv, hsq, hcap,
    hA, hB, hC, hD, hE⟩
  change β < x.1.1.1 + x.1.2 ∧
      β < x.1.1.1 + x.2 ∧
      x.1.1.2 + x.1.2 < A ∧
      x.1.1.2 + x.2 < A ∧
      x.1.2 + x.2 < A at hpat
  dsimp
  have hg : 0 < g := by
    norm_num [δ, sectionSixThetaGap, sectionSixThetaOne,
      sectionSixThetaTwo]
  have hAβ : A < β := by
    norm_num [A, β, δ, sectionSixThetaOne, sectionSixThetaTwo]
  have hd : g ≤ β - x.1.1.1 := by
    norm_num [g, A, β, δ, sectionSixThetaGap, sectionSixThetaOne,
      sectionSixThetaTwo] at hgap huA ⊢
    linarith
  have hdHalf : β - x.1.1.1 < A / 2 := by
    have hvgt : β - x.1.1.1 < x.1.1.2 := by
      linarith [hpat.2, hwv]
    have hwgt : β - x.1.1.1 < x.1.2 := by linarith [hpat.1]
    linarith [hpat.2.1, hvgt, hwgt]
  have hq : 0 < x.2 - (β - x.1.1.1) := by linarith [hpat.2]
  have hs : 0 < x.1.2 - (β - x.1.1.1) := by linarith [hpat.1]
  have hr : 0 < x.1.1.2 - (β - x.1.1.1) := by
    linarith [hpat.2]
  have hqs : x.2 - (β - x.1.1.1) ≤
      x.1.2 - (β - x.1.1.1) := by linarith [htw]
  have hsr : x.1.2 - (β - x.1.1.1) ≤
      x.1.1.2 - (β - x.1.1.1) := by linarith [hwv]
  have hlow : 2 * (β - x.1.1.1) +
      (x.1.1.2 - (β - x.1.1.1)) +
      (x.1.2 - (β - x.1.1.1)) < A := by
    linarith [hpat.2.1]
  have hsq' : 2 * (x.1.1.2 - (β - x.1.1.1)) +
      (β - x.1.1.1) < C - β := by
    norm_num [C, β, δ, sectionSixThetaTwo] at hsq ⊢
    linarith
  have hcap' : x.2 - (β - x.1.1.1) ≤
      (1 - β - 3 * (β - x.1.1.1) -
        (x.1.1.2 - (β - x.1.1.1)) -
        (x.1.2 - (β - x.1.1.1))) / 2 := by
    linarith [hcap]
  exact ⟨hd, hdHalf, hq, hqs, hsr, hlow, hsq', hcap'⟩

theorem sectionSixFirstLowCentralSmallI5P2Transformed_converse
    {d r s q : Real}
    (hd : g ≤ d) (hdHalf : d < A / 2)
    (hr : 0 < r) (hq : 0 < q) (hqs : q ≤ s) (hsr : s ≤ r)
    (hlow : 2 * d + r + s < A)
    (hsq : 2 * r + d < C - β)
    (hcap : q ≤ (1 - β - 3 * d - r - s) / 2) :
    let x : (((Real × Real) × Real) × Real) :=
      (((β - d, d + r), d + s), d + q)
    x ∈ sectionSixFirstLowCentralSmallUniformOuterRegion δ ∧
      x ∈ sectionSixFirstLowCentralSmallI5PairPattern (2 : Fin 4) := by
  dsimp
  have hg : 0 < g := by
    norm_num [δ, sectionSixThetaGap, sectionSixThetaOne,
      sectionSixThetaTwo]
  have hAβ : A < β := by
    norm_num [A, β, δ, sectionSixThetaOne, sectionSixThetaTwo]
  have hβ : β = 212499 / 500000 := by
    norm_num [β, δ, sectionSixThetaTwo]
  have hA : A = 180001 / 500000 := by
    norm_num [A, δ, sectionSixThetaOne]
  have hg' : g = 16249 / 250000 := by
    norm_num [g, δ, sectionSixThetaGap, sectionSixThetaOne,
      sectionSixThetaTwo]
  have hdU : β - d ≤ A := by linarith
  have hRorder : r ≤ β - 2 * d := by
    have hdSmall : d < β - C / 3 := by
      norm_num [A, β, C, δ, sectionSixThetaOne, sectionSixThetaTwo]
      linarith
    linarith
  have horder : d + q ≤ d + s ∧ d + s ≤ d + r ∧
      d + r ≤ β - d := by
    refine ⟨by linarith, by linarith, ?_⟩
    linarith
  have hs : 0 < s := lt_of_lt_of_le hq hqs
  have hcap' : (β - d) + (d + r) + (d + s) + 2 * (d + q) ≤ 1 := by
    linarith
  have hlow' : β < (β - d) + (d + r) := by linarith
  have hsq' : (β - d) + 2 * (d + r) < C := by linarith
  have hpair₁ : β < (β - d) + (d + s) := by linarith
  have hpair₂ : β < (β - d) + (d + q) := by linarith
  have hpair₃ : (d + r) + (d + s) < A := by linarith
  have hpair₄ : (d + r) + (d + q) < A := by linarith
  have hpair₅ : (d + s) + (d + q) < A := by
    linarith
  have houter :
      (((β - d, d + r), d + s), d + q) ∈
        sectionSixFirstLowCentralSmallUniformOuterRegion δ := by
    have hgap' : sectionSixThetaGap δ < d + q := by
      norm_num [g, δ, sectionSixThetaGap, sectionSixThetaOne,
        sectionSixThetaTwo] at hd hq ⊢
      linarith
    have hn1 : (β - d) + (d + s) ∉
        Set.Icc (sectionSixThetaOne δ) (sectionSixThetaTwo δ) := by
      intro h
      norm_num [A, β, δ, sectionSixThetaOne, sectionSixThetaTwo] at h hpair₁
      linarith
    have hn2 : (β - d) + (d + q) ∉
        Set.Icc (sectionSixThetaOne δ) (sectionSixThetaTwo δ) := by
      intro h
      norm_num [A, β, δ, sectionSixThetaOne, sectionSixThetaTwo] at h hpair₂
      linarith
    have hn3 : (d + r) + (d + s) ∉
        Set.Icc (sectionSixThetaOne δ) (sectionSixThetaTwo δ) := by
      intro h
      norm_num [A, β, δ, sectionSixThetaOne, sectionSixThetaTwo] at h hpair₃
      linarith
    have hn4 : (d + r) + (d + q) ∉
        Set.Icc (sectionSixThetaOne δ) (sectionSixThetaTwo δ) := by
      intro h
      norm_num [A, β, δ, sectionSixThetaOne, sectionSixThetaTwo] at h hpair₄
      linarith
    have hn5 : (d + s) + (d + q) ∉
        Set.Icc (sectionSixThetaOne δ) (sectionSixThetaTwo δ) := by
      intro h
      norm_num [A, β, δ, sectionSixThetaOne, sectionSixThetaTwo] at h hpair₅
      linarith
    exact ⟨hgap', horder.1, horder.2.1, horder.2.2, hdU,
      hlow', hsq', hcap', hn1, hn2, hn3, hn4, hn5⟩
  have hpat :
      (((β - d, d + r), d + s), d + q) ∈
        sectionSixFirstLowCentralSmallI5PairPattern (2 : Fin 4) := by
    change β < (β - d) + (d + s) ∧
      β < (β - d) + (d + q) ∧
      (d + r) + (d + s) < A ∧
      (d + r) + (d + q) < A ∧
      (d + s) + (d + q) < A
    exact ⟨hpair₁, hpair₂, hpair₃, hpair₄, hpair₅⟩
  exact ⟨houter, hpat⟩

theorem sectionSixFirstLowCentralSmallI5P2Transformed_projection_bounds
    {x : (((Real × Real) × Real) × Real)}
    (houter : x ∈ sectionSixFirstLowCentralSmallUniformOuterRegion δ)
    (hpat : x ∈ sectionSixFirstLowCentralSmallI5PairPattern (2 : Fin 4)) :
    let d := β - x.1.1.1
    let r := x.1.1.2 - d
    let _s := x.1.2 - d
    let _q := x.2 - d
    r < A - 2 * d ∧ r < (C - β - d) / 2 := by
  rcases sectionSixFirstLowCentralSmallI5P2Transformed_geometry houter hpat with
    ⟨hd, hdHalf, hq, hqs, hsr, hlow, hsq, hcap⟩
  dsimp
  have hs : 0 < x.1.2 - (β - x.1.1.1) := lt_of_lt_of_le hq hqs
  constructor
  · linarith
  · norm_num [A, C, β, δ, sectionSixThetaOne, sectionSixThetaTwo] at hsq ⊢
    linarith

theorem sectionSixFirstLowCentralSmallI5P2_source_walls
    {x : (((Real × Real) × Real) × Real)}
    (houter : x ∈ sectionSixFirstLowCentralSmallUniformOuterRegion δ) :
    let u := x.1.1.1
    let v := x.1.1.2
    let w := x.1.2
    u + v < 1 - β ∧ u + v + 2 * w < 1 := by
  rcases houter with ⟨hgap, htw, hwv, hvu, huA, huv, hsq, hcap,
    hA, hB, hC, hD, hE⟩
  dsimp
  have hvA : x.1.1.2 ≤ A := hvu.trans huA
  constructor
  · have hhalf : 2 * (x.1.1.1 + x.1.1.2) < C + A := by
      norm_num [A, C, δ, sectionSixThetaOne] at hsq huA ⊢
      linarith
    norm_num [A, β, C, δ, sectionSixThetaOne,
      sectionSixThetaTwo] at hhalf ⊢
    linarith
  · have hwv' : x.1.2 ≤ x.1.1.2 := hwv
    linarith [hsq, hvA]

theorem sectionSixFirstLowCentralSmallI5P2_argument_range
    {x : (((Real × Real) × Real) × Real)}
    (houter : x ∈ sectionSixFirstLowCentralSmallUniformOuterRegion δ)
    (hpat : x ∈ sectionSixFirstLowCentralSmallI5PairPattern (2 : Fin 4)) :
    let u := x.1.1.1
    let v := x.1.1.2
    let w := x.1.2
    let t := x.2
    1 ≤ (1 - u - v - w - t) / t ∧
      (1 - u - v - w - t) / t < 7 := by
  rcases houter with ⟨hgap, htw, hwv, hvu, huA, huv, hsq, hcap,
    hA, hB, hC, hD, hE⟩
  change β < x.1.1.1 + x.1.2 ∧
      β < x.1.1.1 + x.2 ∧
      x.1.1.2 + x.1.2 < A ∧
      x.1.1.2 + x.2 < A ∧
      x.1.2 + x.2 < A at hpat
  have hhigh := hpat.2.1
  dsimp
  have htPos : 0 < x.2 := by
    have hg : 0 < g := by
      norm_num [g, δ, sectionSixThetaGap, sectionSixThetaOne,
        sectionSixThetaTwo]
    linarith
  constructor
  · apply (le_div_iff₀ htPos).2
    linarith
  · apply (div_lt_iff₀ htPos).2
    have hg : g = 16249 / 250000 := by
      norm_num [g, δ, sectionSixThetaGap, sectionSixThetaOne,
        sectionSixThetaTwo]
    have hbeta : β = 212499 / 500000 := by
      norm_num [β, δ, sectionSixThetaTwo]
    have hsum : 1 < x.1.1.1 + x.1.1.2 + x.1.2 + 8 * x.2 := by
      norm_num [hg, hbeta] at hgap ⊢
      linarith [hhigh]
    linarith [hsum]

end
end PrimesRestrictedDigits
