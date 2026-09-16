import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5PairPatterns
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1AffineMeasureTransportD806
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
/-! # SectionSixFirstLowCentralSmallI5P1TransformedGeometryD807 -/

set_option autoImplicit false
set_option warningAsError true

open Set

namespace PrimesRestrictedDigits

noncomputable section

/-!
# fixed-delta P1 transformed geometry

This module exposes the fixed-delta HLLLL target, three closed transformed overcover pieces,
the one-way inverse-map cover, and redundant order walls. It deliberately contains no measure,
Jacobian, Fubini, kernel, replay, cap estimate, source equality, or full-I5 theorem.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

def sectionSixFirstLowCentralSmallI5P1D807Delta : Real := 1 / 1000000

def sectionSixFirstLowCentralSmallI5P1D807A : Real :=
  sectionSixThetaOne sectionSixFirstLowCentralSmallI5P1D807Delta

def sectionSixFirstLowCentralSmallI5P1D807Beta : Real :=
  sectionSixThetaTwo sectionSixFirstLowCentralSmallI5P1D807Delta

def sectionSixFirstLowCentralSmallI5P1D807Gap : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Beta -
    sectionSixFirstLowCentralSmallI5P1D807A

def sectionSixFirstLowCentralSmallI5P1D807Square : Real := 16 / 25

def sectionSixFirstLowCentralSmallI5P1D807D0 : Real :=
  2 * sectionSixFirstLowCentralSmallI5P1D807Gap

def sectionSixFirstLowCentralSmallI5P1D807Ds : Real :=
  sectionSixFirstLowCentralSmallI5P1D807A +
    sectionSixFirstLowCentralSmallI5P1D807Beta -
    sectionSixFirstLowCentralSmallI5P1D807Square

def sectionSixFirstLowCentralSmallI5P1D807Dr : Real :=
  (2 * sectionSixFirstLowCentralSmallI5P1D807A +
      sectionSixFirstLowCentralSmallI5P1D807Beta -
      sectionSixFirstLowCentralSmallI5P1D807Square) / 3

def sectionSixFirstLowCentralSmallI5P1D807D1 : Real :=
  sectionSixFirstLowCentralSmallI5P1D807A / 2

def sectionSixFirstLowCentralSmallI5P1D807H (d : Real) : Real :=
  (sectionSixFirstLowCentralSmallI5P1D807Square -
      sectionSixFirstLowCentralSmallI5P1D807Beta - d) / 2

def sectionSixFirstLowCentralSmallI5P1D807L (d : Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D807A - 2 * d

theorem sectionSixFirstLowCentralSmallI5P1D807_constants :
    sectionSixFirstLowCentralSmallI5P1D807A = 180001 / 500000 ∧
      sectionSixFirstLowCentralSmallI5P1D807Beta = 212499 / 500000 ∧
      sectionSixFirstLowCentralSmallI5P1D807Gap = 16249 / 250000 ∧
      sectionSixFirstLowCentralSmallI5P1D807D0 = 16249 / 125000 ∧
      sectionSixFirstLowCentralSmallI5P1D807Ds = 29 / 200 ∧
      sectionSixFirstLowCentralSmallI5P1D807Dr = 84167 / 500000 ∧
      sectionSixFirstLowCentralSmallI5P1D807D1 = 180001 / 1000000 := by
  norm_num [sectionSixFirstLowCentralSmallI5P1D807D1,
    sectionSixFirstLowCentralSmallI5P1D807Dr,
    sectionSixFirstLowCentralSmallI5P1D807Ds,
    sectionSixFirstLowCentralSmallI5P1D807D0,
    sectionSixFirstLowCentralSmallI5P1D807Gap,
    sectionSixFirstLowCentralSmallI5P1D807A,
    sectionSixFirstLowCentralSmallI5P1D807Beta,
    sectionSixFirstLowCentralSmallI5P1D807Square,
    sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaOne,
    sectionSixThetaTwo]

def sectionSixFirstLowCentralSmallI5P1D807Target : Set SectionSixP1AffineT :=
  sectionSixFirstLowCentralSmallUniformOuterRegion
      sectionSixFirstLowCentralSmallI5P1D807Delta ∩
    sectionSixFirstLowCentralSmallI5PairPattern (1 : Fin 4)

def sectionSixFirstLowCentralSmallI5P1D807Piece0 : Set SectionSixP1AffineT :=
  {z | z.1.1.1 ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807D0
        sectionSixFirstLowCentralSmallI5P1D807Ds ∧
      z.1.1.2 ∈ Set.Icc 0
        (sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1) ∧
      z.1.2 ∈ Set.Icc 0 z.1.1.2 ∧
      z.2 ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807Gap
        (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)}

def sectionSixFirstLowCentralSmallI5P1D807Piece1 : Set SectionSixP1AffineT :=
  {z | z.1.1.1 ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807Ds
        sectionSixFirstLowCentralSmallI5P1D807Dr ∧
      z.1.1.2 ∈ Set.Icc 0
        (sectionSixFirstLowCentralSmallI5P1D807H z.1.1.1) ∧
      z.1.2 ∈ Set.Icc 0
        (min z.1.1.2
          (sectionSixFirstLowCentralSmallI5P1D807L z.1.1.1 - z.1.1.2)) ∧
      z.2 ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807Gap
        (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)}

def sectionSixFirstLowCentralSmallI5P1D807Piece2 : Set SectionSixP1AffineT :=
  {z | z.1.1.1 ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807Dr
        sectionSixFirstLowCentralSmallI5P1D807D1 ∧
      z.1.1.2 ∈ Set.Icc 0
        (sectionSixFirstLowCentralSmallI5P1D807L z.1.1.1) ∧
      z.1.2 ∈ Set.Icc 0
        (min z.1.1.2
          (sectionSixFirstLowCentralSmallI5P1D807L z.1.1.1 - z.1.1.2)) ∧
      z.2 ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807Gap
        (z.1.1.1 - sectionSixFirstLowCentralSmallI5P1D807Gap)}

private theorem sectionSixFirstLowCentralSmallI5P1D807_forward_bounds
    {u v w t : Real}
    (houter : (((u, v), w), t) ∈
      sectionSixFirstLowCentralSmallUniformOuterRegion
        sectionSixFirstLowCentralSmallI5P1D807Delta)
    (hpat : (((u, v), w), t) ∈
      sectionSixFirstLowCentralSmallI5PairPattern (1 : Fin 4)) :
    let d := sectionSixFirstLowCentralSmallI5P1D807Beta - u
    let r := v - d
    let s := w - d
    sectionSixFirstLowCentralSmallI5P1D807D0 < d ∧
      d < sectionSixFirstLowCentralSmallI5P1D807D1 ∧
      0 < r ∧
      r < sectionSixFirstLowCentralSmallI5P1D807H d ∧
      0 < s ∧ s ≤ r ∧
      s < sectionSixFirstLowCentralSmallI5P1D807L d - r ∧
      sectionSixFirstLowCentralSmallI5P1D807Gap < t ∧
      t < d - sectionSixFirstLowCentralSmallI5P1D807Gap := by
  rcases houter with ⟨hgap, htw, hwv, hvu, huA, huv, hsq, hcap,
    hA, hB, hC, hD, hE⟩
  change sectionSixFirstLowCentralSmallI5P1D807Beta < u + w ∧
      u + t < sectionSixFirstLowCentralSmallI5P1D807A ∧
      v + w < sectionSixFirstLowCentralSmallI5P1D807A ∧
      v + t < sectionSixFirstLowCentralSmallI5P1D807A ∧
      w + t < sectionSixFirstLowCentralSmallI5P1D807A at hpat
  dsimp
  have hg : 0 < sectionSixFirstLowCentralSmallI5P1D807Gap := by
    norm_num [sectionSixFirstLowCentralSmallI5P1D807Gap,
      sectionSixFirstLowCentralSmallI5P1D807A,
      sectionSixFirstLowCentralSmallI5P1D807Beta,
      sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaGap,
      sectionSixThetaOne, sectionSixThetaTwo]
  have hAβ : sectionSixFirstLowCentralSmallI5P1D807A <
      sectionSixFirstLowCentralSmallI5P1D807Beta := by
    norm_num [sectionSixFirstLowCentralSmallI5P1D807A,
      sectionSixFirstLowCentralSmallI5P1D807Beta,
      sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaOne,
      sectionSixThetaTwo]
  have hr : 0 < v - (sectionSixFirstLowCentralSmallI5P1D807Beta - u) := by
    linarith [huv]
  have hs : 0 < w - (sectionSixFirstLowCentralSmallI5P1D807Beta - u) := by
    linarith [hpat.1]
  have htUpper : t <
      (sectionSixFirstLowCentralSmallI5P1D807Beta - u) -
        sectionSixFirstLowCentralSmallI5P1D807Gap := by
    norm_num [sectionSixFirstLowCentralSmallI5P1D807A,
      sectionSixFirstLowCentralSmallI5P1D807Beta,
      sectionSixFirstLowCentralSmallI5P1D807Gap,
      sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaGap,
      sectionSixThetaOne, sectionSixThetaTwo] at hpat ⊢
    linarith [hpat.2.1]
  have hgap' : sectionSixFirstLowCentralSmallI5P1D807Gap < t := by
    simpa [sectionSixFirstLowCentralSmallI5P1D807Gap,
      sectionSixFirstLowCentralSmallI5P1D807A,
      sectionSixFirstLowCentralSmallI5P1D807Beta,
      sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaGap,
      sectionSixThetaOne, sectionSixThetaTwo] using hgap
  have hdLower : 2 * sectionSixFirstLowCentralSmallI5P1D807Gap <
      sectionSixFirstLowCentralSmallI5P1D807Beta - u := by
    linarith [hgap', htUpper]
  have hsum : 2 * (sectionSixFirstLowCentralSmallI5P1D807Beta - u) +
      (v - (sectionSixFirstLowCentralSmallI5P1D807Beta - u)) +
      (w - (sectionSixFirstLowCentralSmallI5P1D807Beta - u)) <
      sectionSixFirstLowCentralSmallI5P1D807A := by
    linarith [hpat.2.2.1]
  have hdUpper : sectionSixFirstLowCentralSmallI5P1D807Beta - u <
      sectionSixFirstLowCentralSmallI5P1D807A / 2 := by
    linarith [hsum, hr, hs]
  have hsq' : v - (sectionSixFirstLowCentralSmallI5P1D807Beta - u) <
      sectionSixFirstLowCentralSmallI5P1D807H
        (sectionSixFirstLowCentralSmallI5P1D807Beta - u) := by
    norm_num [sectionSixFirstLowCentralSmallI5P1D807H,
      sectionSixFirstLowCentralSmallI5P1D807Square,
      sectionSixFirstLowCentralSmallI5P1D807Beta,
      sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaTwo] at hsq ⊢
    linarith
  have hrlow : v - (sectionSixFirstLowCentralSmallI5P1D807Beta - u) <
      sectionSixFirstLowCentralSmallI5P1D807L
        (sectionSixFirstLowCentralSmallI5P1D807Beta - u) := by
    norm_num [sectionSixFirstLowCentralSmallI5P1D807L,
      sectionSixFirstLowCentralSmallI5P1D807A] at hsum ⊢
    linarith [hsum, hs]
  have hsr : w - (sectionSixFirstLowCentralSmallI5P1D807Beta - u) ≤
      v - (sectionSixFirstLowCentralSmallI5P1D807Beta - u) := by
    linarith [hwv]
  have hslow : w - (sectionSixFirstLowCentralSmallI5P1D807Beta - u) <
      sectionSixFirstLowCentralSmallI5P1D807L
        (sectionSixFirstLowCentralSmallI5P1D807Beta - u) -
        (v - (sectionSixFirstLowCentralSmallI5P1D807Beta - u)) := by
    norm_num [sectionSixFirstLowCentralSmallI5P1D807L,
      sectionSixFirstLowCentralSmallI5P1D807A] at hpat ⊢
    linarith [hpat.2.2.1]
  refine ⟨?_, ?_, hr, ?_, hs, hsr, ?_, hgap', htUpper⟩
  · simpa [sectionSixFirstLowCentralSmallI5P1D807D0] using hdLower
  · simpa [sectionSixFirstLowCentralSmallI5P1D807D1] using hdUpper
  · exact hsq'
  · exact hslow

theorem sectionSixFirstLowCentralSmallI5P1D807_transformed_bounds
    {x : SectionSixP1AffineT} (hx : x ∈
      sectionSixFirstLowCentralSmallI5P1D807Target) :
    let d := sectionSixFirstLowCentralSmallI5P1D807Beta - x.1.1.1
    let r := x.1.1.2 - d
    let s := x.1.2 - d
    sectionSixFirstLowCentralSmallI5P1D807D0 < d ∧
      d < sectionSixFirstLowCentralSmallI5P1D807D1 ∧
      0 < r ∧
      r < sectionSixFirstLowCentralSmallI5P1D807H d ∧
      0 < s ∧ s ≤ r ∧
      s < sectionSixFirstLowCentralSmallI5P1D807L d - r ∧
      sectionSixFirstLowCentralSmallI5P1D807Gap < x.2 ∧
      x.2 < d - sectionSixFirstLowCentralSmallI5P1D807Gap := by
  rcases x with ⟨⟨⟨u, v⟩, w⟩, t⟩
  exact sectionSixFirstLowCentralSmallI5P1D807_forward_bounds hx.1 hx.2

private theorem sectionSixFirstLowCentralSmallI5P1D807_map_formula
    (u v w t : Real) :
    sectionSixP1SharpPsiD806
        sectionSixFirstLowCentralSmallI5P1D807Beta (((u, v), w), t) =
      (((sectionSixFirstLowCentralSmallI5P1D807Beta - u,
          v - (sectionSixFirstLowCentralSmallI5P1D807Beta - u)),
          w - (sectionSixFirstLowCentralSmallI5P1D807Beta - u)), t) := by
  simp [sectionSixP1SharpPsiD806]
  ring_nf
  simp

theorem sectionSixFirstLowCentralSmallI5P1D807_target_to_closed_cover :
    sectionSixP1SharpPsiD806
        sectionSixFirstLowCentralSmallI5P1D807Beta ''
      sectionSixFirstLowCentralSmallI5P1D807Target ⊆
    sectionSixFirstLowCentralSmallI5P1D807Piece0 ∪
      sectionSixFirstLowCentralSmallI5P1D807Piece1 ∪
      sectionSixFirstLowCentralSmallI5P1D807Piece2 := by
  rintro y ⟨x, hx, rfl⟩
  rcases x with ⟨⟨⟨u, v⟩, w⟩, t⟩
  have hb := sectionSixFirstLowCentralSmallI5P1D807_forward_bounds hx.1 hx.2
  dsimp at hb
  rw [sectionSixFirstLowCentralSmallI5P1D807_map_formula]
  rcases hb with ⟨hd0, hd1, hr0, hrH, hs0, hsr, hsL, ht0, ht1⟩
  by_cases hds : sectionSixFirstLowCentralSmallI5P1D807Beta - u ≤
      sectionSixFirstLowCentralSmallI5P1D807Ds
  · left
    left
    change _ ∧ _ ∧ _ ∧ _
    refine ⟨⟨le_of_lt hd0, hds⟩, ⟨le_of_lt hr0, le_of_lt hrH⟩,
      ⟨le_of_lt hs0, hsr⟩, ⟨le_of_lt ht0, le_of_lt ht1⟩⟩
  · have hds' : sectionSixFirstLowCentralSmallI5P1D807Ds <
        sectionSixFirstLowCentralSmallI5P1D807Beta - u := lt_of_not_ge hds
    by_cases hdr : sectionSixFirstLowCentralSmallI5P1D807Beta - u ≤
        sectionSixFirstLowCentralSmallI5P1D807Dr
    · left
      right
      change _ ∧ _ ∧ _ ∧ _
      have hsmin : w - (sectionSixFirstLowCentralSmallI5P1D807Beta - u) ≤
          min (v - (sectionSixFirstLowCentralSmallI5P1D807Beta - u))
            (sectionSixFirstLowCentralSmallI5P1D807L
              (sectionSixFirstLowCentralSmallI5P1D807Beta - u) -
              (v - (sectionSixFirstLowCentralSmallI5P1D807Beta - u))) := by
        exact le_min hsr (le_of_lt hsL)
      refine ⟨⟨le_of_lt hds', hdr⟩, ⟨le_of_lt hr0, le_of_lt hrH⟩,
        ⟨le_of_lt hs0, hsmin⟩, ⟨le_of_lt ht0, le_of_lt ht1⟩⟩
    · right
      change _ ∧ _ ∧ _ ∧ _
      have hdr' : sectionSixFirstLowCentralSmallI5P1D807Dr <
          sectionSixFirstLowCentralSmallI5P1D807Beta - u := lt_of_not_ge hdr
      have hrL : v - (sectionSixFirstLowCentralSmallI5P1D807Beta - u) <
          sectionSixFirstLowCentralSmallI5P1D807L
            (sectionSixFirstLowCentralSmallI5P1D807Beta - u) := by
        linarith [hs0, hsL]
      have hsmin : w - (sectionSixFirstLowCentralSmallI5P1D807Beta - u) ≤
          min (v - (sectionSixFirstLowCentralSmallI5P1D807Beta - u))
            (sectionSixFirstLowCentralSmallI5P1D807L
              (sectionSixFirstLowCentralSmallI5P1D807Beta - u) -
              (v - (sectionSixFirstLowCentralSmallI5P1D807Beta - u))) := by
        exact le_min hsr (le_of_lt hsL)
      refine ⟨⟨le_of_lt hdr', le_of_lt hd1⟩,
        ⟨le_of_lt hr0, le_of_lt hrL⟩, ⟨le_of_lt hs0, hsmin⟩,
        ⟨le_of_lt ht0, le_of_lt ht1⟩⟩

theorem sectionSixFirstLowCentralSmallI5P1D807_v_lt_u
    {d r : Real}
    (hd : sectionSixFirstLowCentralSmallI5P1D807D0 < d)
    (hr : r < sectionSixFirstLowCentralSmallI5P1D807L d) :
    d + r < sectionSixFirstLowCentralSmallI5P1D807Beta - d := by
  have hpos : 0 < sectionSixFirstLowCentralSmallI5P1D807D0 := by
    norm_num [sectionSixFirstLowCentralSmallI5P1D807D0,
      sectionSixFirstLowCentralSmallI5P1D807Gap,
      sectionSixFirstLowCentralSmallI5P1D807A,
      sectionSixFirstLowCentralSmallI5P1D807Beta,
      sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaOne,
      sectionSixThetaTwo]
  have hAB : sectionSixFirstLowCentralSmallI5P1D807A <
      sectionSixFirstLowCentralSmallI5P1D807Beta := by
    norm_num [sectionSixFirstLowCentralSmallI5P1D807A,
      sectionSixFirstLowCentralSmallI5P1D807Beta,
      sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaOne,
      sectionSixThetaTwo]
  have hdpos : 0 < d := lt_trans hpos hd
  dsimp [sectionSixFirstLowCentralSmallI5P1D807L] at hr
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D807_t_lt_w
    {d s t : Real}
    (hg : 0 < sectionSixFirstLowCentralSmallI5P1D807Gap)
    (ht1 : t < d - sectionSixFirstLowCentralSmallI5P1D807Gap)
    (hs : 0 < s) :
    t < d + s := by
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D807_u_lt_A
    {d : Real}
    (hd : sectionSixFirstLowCentralSmallI5P1D807D0 < d) :
    sectionSixFirstLowCentralSmallI5P1D807Beta - d <
      sectionSixFirstLowCentralSmallI5P1D807A := by
  have hg : 0 < sectionSixFirstLowCentralSmallI5P1D807Gap := by
    norm_num [sectionSixFirstLowCentralSmallI5P1D807Gap,
      sectionSixFirstLowCentralSmallI5P1D807A,
      sectionSixFirstLowCentralSmallI5P1D807Beta,
      sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaOne,
      sectionSixThetaTwo]
  have hrel : sectionSixFirstLowCentralSmallI5P1D807Beta -
      sectionSixFirstLowCentralSmallI5P1D807Gap =
      sectionSixFirstLowCentralSmallI5P1D807A := by
    simp [sectionSixFirstLowCentralSmallI5P1D807Gap]
  have hpos : 0 < sectionSixFirstLowCentralSmallI5P1D807D0 := by
    dsimp [sectionSixFirstLowCentralSmallI5P1D807D0]
    nlinarith [hg]
  have hdg : sectionSixFirstLowCentralSmallI5P1D807Gap < d := by
    have : 2 * sectionSixFirstLowCentralSmallI5P1D807Gap < d := by
      simpa [sectionSixFirstLowCentralSmallI5P1D807D0] using hd
    linarith
  linarith

end
end PrimesRestrictedDigits
