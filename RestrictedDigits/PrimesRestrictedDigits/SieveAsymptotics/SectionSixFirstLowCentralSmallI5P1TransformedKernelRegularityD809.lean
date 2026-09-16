import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1FiniteCoverTransportD808
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallQuadrupleRegions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1TransformedKernelRegularityD809 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

/-!
# P1 transformed kernel regularity

This fixed-delta module proves that every closed piece lies in a common compact carrier on
which the pullback of the native P1 Buchstab kernel is continuous, integrable, and
nonnegative. It then specializes one-way finite-cover inequality. It contains no numerical
integral cap, replay certificate, source-region equality, or full-I5 assertion.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

private abbrev d809Beta : Real := sectionSixFirstLowCentralSmallI5P1D807Beta
private abbrev d809Gap : Real := sectionSixFirstLowCentralSmallI5P1D807Gap
private abbrev d809A : Real := sectionSixFirstLowCentralSmallI5P1D807A
private abbrev d809D0 : Real := sectionSixFirstLowCentralSmallI5P1D807D0
private abbrev d809Ds : Real := sectionSixFirstLowCentralSmallI5P1D807Ds
private abbrev d809Dr : Real := sectionSixFirstLowCentralSmallI5P1D807Dr
private abbrev d809D1 : Real := sectionSixFirstLowCentralSmallI5P1D807D1
private abbrev Q : Real := sectionSixFirstLowCentralSmallI5P1D807Square
private abbrev d809H : Real -> Real := sectionSixFirstLowCentralSmallI5P1D807H
private abbrev d809L : Real -> Real := sectionSixFirstLowCentralSmallI5P1D807L

private theorem d809Constants :
    d809A = 180001 / 500000 ∧ d809Beta = 212499 / 500000 ∧
      d809Gap = 16249 / 250000 ∧ d809D0 = 16249 / 125000 ∧
      d809Ds = 29 / 200 ∧ d809Dr = 84167 / 500000 ∧
      d809D1 = 180001 / 1000000 ∧ Q = 16 / 25 := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨hA, hbeta, hgap, hD0, hDs, hDr, hD1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [d809A] using hA
  · simpa [d809Beta] using hbeta
  · simpa [d809Gap] using hgap
  · simpa [d809D0] using hD0
  · simpa [d809Ds] using hDs
  · simpa [d809Dr] using hDr
  · simpa [d809D1] using hD1
  · norm_num [Q, sectionSixFirstLowCentralSmallI5P1D807Square]

private theorem d809CapMargin : d809Beta + 3 * d809A / 2 - 2 * d809Gap = 835009 / 1000000 := by
  rcases d809Constants with ⟨hA, hbeta, hgap, hD0, hDs, hDr, hD1, hQ⟩
  norm_num [hA, hbeta, hgap]

private theorem d809CapArithmetic {d r s t : Real}
    (hd : d <= d809D1) (hrs : r + s <= d809L d) (ht : t <= d - d809Gap) :
    d809Beta + d + r + s + 2 * t <= 835009 / 1000000 := by
  have hD1 : d809D1 = d809A / 2 := by
    rcases d809Constants with ⟨hA, hbeta, hgap, hD0, hDs, hDr, hD1, hQ⟩
    rw [hD1, hA]
    norm_num
  have hcap : d809Beta + d + r + s + 2 * t <= d809Beta + d809A + d - 2 * d809Gap := by
    change r + s <= d809A - 2 * d at hrs
    change t <= d - d809Gap at ht
    linarith [hrs, ht]
  have hlast : d809Beta + d809A + d - 2 * d809Gap <= d809Beta + 3 * d809A / 2 - 2 * d809Gap := by
    linarith [hd, hD1]
  exact (hcap.trans hlast).trans_eq d809CapMargin

private theorem d809PhiCapFormula (d r s t : Real) :
    let z : SectionSixP1AffineT := (((d, r), s), t)
    (sectionSixP1SharpPhiD806 d809Beta z).1.1.1 +
        (sectionSixP1SharpPhiD806 d809Beta z).1.1.2 +
        (sectionSixP1SharpPhiD806 d809Beta z).1.2 +
        2 * (sectionSixP1SharpPhiD806 d809Beta z).2 =
      d809Beta + d + r + s + 2 * t := by
  dsimp
  simp [sectionSixP1SharpPhiD806]
  ring

private theorem d809RatioGeOne {d r s t : Real}
    (ht : 0 < t) (hcap : d809Beta + d + r + s + 2 * t <= 1) :
    1 <= (1 - d809Beta - d - r - s - t) / t := by
  rw [le_div_iff₀ ht]
  linarith

private theorem d809EndpointConstants :
    0 < d809D0 ∧ 0 < d809Gap ∧ 0 < d809Beta - d809D1 ∧
      d809Beta + 3 * d809A / 2 - 2 * d809Gap < (1 : Real) := by
  rcases d809Constants with ⟨hA, hbeta, hgap, hD0, hDs, hDr, hD1, hQ⟩
  norm_num [hA, hbeta, hgap, hD0, hD1]

private theorem d809P0RplusSLeL {d r s : Real}
    (hd : d <= d809Ds) (hr : r <= d809H d) (hsr : s <= r) :
    r + s <= d809L d := by
  rcases d809Constants with ⟨hA, hbeta, hgap, hD0, hDs, hDr, hD1, hQ⟩
  change r <= (Q - d809Beta - d) / 2 at hr
  change r + s <= d809A - 2 * d
  rw [hDs] at hd
  rw [hQ, hbeta] at hr
  rw [hA]
  linarith

private theorem d809P1OrP2RplusSLeL {d r s : Real}
    (hs : s <= min r (d809L d - r)) : r + s <= d809L d := by
  have hs' := (le_min_iff.mp hs).2
  linarith

private theorem d809AllPieceRplusSLeL (i : Fin 3) {z : SectionSixP1AffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P1D808Piece i) :
    z.1.1.2 + z.1.2 <= d809L z.1.1.1 := by
  fin_cases i
  · change z ∈ sectionSixFirstLowCentralSmallI5P1D807Piece0 at hz
    rcases hz with ⟨hd, hr, hs, ht⟩
    rcases hd with ⟨hd0, hds⟩
    rcases hr with ⟨hr0, hrH⟩
    rcases hs with ⟨hs0, hsr⟩
    exact d809P0RplusSLeL hds hrH hsr
  · change z ∈ sectionSixFirstLowCentralSmallI5P1D807Piece1 at hz
    rcases hz with ⟨hd, hr, hs, ht⟩
    rcases hs with ⟨hs0, hsmin⟩
    exact d809P1OrP2RplusSLeL hsmin
  · change z ∈ sectionSixFirstLowCentralSmallI5P1D807Piece2 at hz
    rcases hz with ⟨hd, hr, hs, ht⟩
    rcases hs with ⟨hs0, hsmin⟩
    exact d809P1OrP2RplusSLeL hsmin

private theorem d809ConstantsOrder :
    d809D0 <= d809Ds ∧ d809Ds <= d809Dr ∧ d809Dr <= d809D1 ∧ 0 < d809D0 ∧ 0 < d809A ∧ 0 < d809Gap ∧
      0 < d809D1 - d809Gap ∧ d809Gap <= d809D1 - d809Gap := by
  rcases d809Constants with ⟨hA, hbeta, hgap, hD0, hDs, hDr, hD1, hQ⟩
  norm_num [hA, hgap, hD0, hDs, hDr, hD1]

private theorem d809HceilLeA {d : Real} (hd : d809D0 <= d) : d809H d <= d809A := by
  rcases d809Constants with ⟨hA, hbeta, hgap, hD0, hDs, hDr, hD1, hQ⟩
  change (Q - d809Beta - d) / 2 <= d809A
  rw [hQ, hbeta, hA]
  norm_num [hD0] at hd ⊢
  linarith

private theorem d809LceilLeA {d : Real} (hd : 0 <= d) : d809L d <= d809A := by
  change d809A - 2 * d <= d809A
  linarith

private theorem d809AllPieceInBox (i : Fin 3) {z : SectionSixP1AffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P1D808Piece i) :
    z.1.1.1 ∈ Set.Icc d809D0 d809D1 ∧ z.1.1.2 ∈ Set.Icc 0 d809A ∧
      z.1.2 ∈ Set.Icc 0 d809A ∧ z.2 ∈ Set.Icc d809Gap (d809D1 - d809Gap) := by
  fin_cases i
  · change z ∈ sectionSixFirstLowCentralSmallI5P1D807Piece0 at hz
    rcases hz with ⟨hd, hr, hs, ht⟩
    rcases hd with ⟨hd0, hds⟩
    rcases hr with ⟨hr0, hrH⟩
    rcases hs with ⟨hs0, hsr⟩
    rcases ht with ⟨htg, htt⟩
    rcases d809ConstantsOrder with ⟨h0s, hsrng, hrd1, hD0pos, hApos, hgpos,
      hD1Gpos, hGG⟩
    have hd1 : z.1.1.1 <= d809D1 := by linarith [hds, hsrng, hrd1]
    have hrlA : z.1.1.2 <= d809A := hrH.trans (d809HceilLeA hd0)
    have hslA : z.1.2 <= d809A := hsr.trans hrlA
    have htt' : z.2 <= d809D1 - d809Gap := by
      have hd1' : z.1.1.1 <= d809D1 := by linarith [hds, hrd1]
      linarith
    exact ⟨⟨hd0, hd1⟩, ⟨hr0, hrlA⟩, ⟨hs0, hslA⟩, ⟨htg, htt'⟩⟩
  · change z ∈ sectionSixFirstLowCentralSmallI5P1D807Piece1 at hz
    rcases hz with ⟨hd, hr, hs, ht⟩
    rcases hd with ⟨hd0, hdr⟩
    rcases hr with ⟨hr0, hrH⟩
    rcases hs with ⟨hs0, hsmin⟩
    rcases ht with ⟨htg, htt⟩
    rcases d809ConstantsOrder with ⟨h0s, hsrng, hrd1, hD0pos, hApos, hgpos,
      hD1Gpos, hGG⟩
    have hd0' : d809D0 <= z.1.1.1 := h0s.trans hd0
    have hd1 : z.1.1.1 <= d809D1 := by linarith [hdr, hrd1]
    have hrlA : z.1.1.2 <= d809A := hrH.trans (d809HceilLeA hd0')
    have hslr : z.1.2 <= z.1.1.2 := (le_min_iff.mp hsmin).1
    have hslA : z.1.2 <= d809A := hslr.trans hrlA
    have htt' : z.2 <= d809D1 - d809Gap := by linarith
    exact ⟨⟨hd0', hd1⟩, ⟨hr0, hrlA⟩, ⟨hs0, hslA⟩, ⟨htg, htt'⟩⟩
  · change z ∈ sectionSixFirstLowCentralSmallI5P1D807Piece2 at hz
    rcases hz with ⟨hd, hr, hs, ht⟩
    rcases hd with ⟨hd0, hd1⟩
    rcases hr with ⟨hr0, hrL⟩
    rcases hs with ⟨hs0, hsmin⟩
    rcases ht with ⟨htg, htt⟩
    rcases d809ConstantsOrder with ⟨h0s, hsrng, hrd1, hD0pos, hApos, hgpos,
      hD1Gpos, hGG⟩
    have hd0' : d809D0 <= z.1.1.1 := h0s.trans (hsrng.trans hd0)
    have hd0nonneg : 0 <= z.1.1.1 := by linarith [hd0', hD0pos]
    have hrlA : z.1.1.2 <= d809A := hrL.trans (d809LceilLeA hd0nonneg)
    have hslr : z.1.2 <= z.1.1.2 := (le_min_iff.mp hsmin).1
    have hslA : z.1.2 <= d809A := hslr.trans hrlA
    have htt' : z.2 <= d809D1 - d809Gap := by linarith
    exact ⟨⟨hd0', hd1⟩, ⟨hr0, hrlA⟩, ⟨hs0, hslA⟩, ⟨htg, htt'⟩⟩

def sectionSixFirstLowCentralSmallI5P1D809BaseBox : Set SectionSixP1AffineT :=
  ((Set.Icc d809D0 d809D1 ×ˢ Set.Icc 0 d809A) ×ˢ Set.Icc 0 d809A) ×ˢ
    Set.Icc d809Gap (d809D1 - d809Gap)

def sectionSixFirstLowCentralSmallI5P1D809Cap : Set SectionSixP1AffineT := {z |
  d809Beta + z.1.1.1 + z.1.1.2 + z.1.2 + 2 * z.2 <= 1}

/- The physical terminal wall is written through the affine image first;
   the following equality records its explicit pullback rather than silently
   replacing the source-oriented predicate by an algebraic abbreviation. -/
def sectionSixFirstLowCentralSmallI5P1D809PhysicalCap : Set SectionSixP1AffineT := {z |
  let y := sectionSixP1SharpPhiD806 sectionSixFirstLowCentralSmallI5P1D807Beta z
  y.1.1.1 + y.1.1.2 + y.1.2 + 2 * y.2 <= 1}

theorem sectionSixFirstLowCentralSmallI5P1D809_physical_cap_eq_cap :
    sectionSixFirstLowCentralSmallI5P1D809PhysicalCap =
      sectionSixFirstLowCentralSmallI5P1D809Cap := by
  ext z
  simp [sectionSixFirstLowCentralSmallI5P1D809PhysicalCap,
    sectionSixFirstLowCentralSmallI5P1D809Cap, sectionSixP1SharpPhiD806]
  ring_nf

theorem sectionSixFirstLowCentralSmallI5P1D809_cap_margin :
    sectionSixFirstLowCentralSmallI5P1D807Beta +
        3 * sectionSixFirstLowCentralSmallI5P1D807A / 2 -
        2 * sectionSixFirstLowCentralSmallI5P1D807Gap =
      (835009 / 1000000 : Real) ∧
      sectionSixFirstLowCentralSmallI5P1D807Beta +
        3 * sectionSixFirstLowCentralSmallI5P1D807A / 2 -
        2 * sectionSixFirstLowCentralSmallI5P1D807Gap < 1 := by
  constructor
  · simpa [d809Beta, d809A, d809Gap] using d809CapMargin
  · norm_num [sectionSixFirstLowCentralSmallI5P1D807Gap,
      sectionSixFirstLowCentralSmallI5P1D807A,
      sectionSixFirstLowCentralSmallI5P1D807Beta,
      sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaOne,
      sectionSixThetaTwo]

def sectionSixFirstLowCentralSmallI5P1D809Carrier : Set SectionSixP1AffineT := sectionSixFirstLowCentralSmallI5P1D809BaseBox ∩ sectionSixFirstLowCentralSmallI5P1D809Cap

theorem sectionSixFirstLowCentralSmallI5P1D809_piece_cap (i : Fin 3) {z : SectionSixP1AffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P1D808Piece i) :
    z ∈ sectionSixFirstLowCentralSmallI5P1D809Cap := by
  have hbox := d809AllPieceInBox i hz
  have hsum := d809AllPieceRplusSLeL i hz
  have hpiece : z.2 <= z.1.1.1 - d809Gap := by
    fin_cases i <;>
      (change z ∈ _ at hz
       rcases hz with ⟨hd, hr, hs, ht⟩
       exact ht.2)
  change d809Beta + z.1.1.1 + z.1.1.2 + z.1.2 + 2 * z.2 <= 1
  have hbound := d809CapArithmetic hbox.1.2 hsum hpiece
  norm_num at hbound ⊢
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D809_piece_cap_strict
    (i : Fin 3) {z : SectionSixP1AffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P1D808Piece i) :
    sectionSixFirstLowCentralSmallI5P1D807Beta + z.1.1.1 + z.1.1.2 +
      z.1.2 + 2 * z.2 < 1 := by
  have hbox := d809AllPieceInBox i hz
  have hsum := d809AllPieceRplusSLeL i hz
  have hpiece : z.2 <= z.1.1.1 - d809Gap := by
    fin_cases i <;>
      (change z ∈ _ at hz
       rcases hz with ⟨hd, hr, hs, ht⟩
       exact ht.2)
  have hbound := d809CapArithmetic hbox.1.2 hsum hpiece
  have hstrict : d809Beta + z.1.1.1 + z.1.1.2 + z.1.2 + 2 * z.2 < 1 := by
    exact lt_of_le_of_lt hbound (by norm_num)
  simpa [d809Beta] using hstrict

theorem sectionSixFirstLowCentralSmallI5P1D809_piece_subset_carrier (i : Fin 3) :
    sectionSixFirstLowCentralSmallI5P1D808Piece i ⊆ sectionSixFirstLowCentralSmallI5P1D809Carrier := by
  intro z hz
  have hbox := d809AllPieceInBox i hz
  have hcap := sectionSixFirstLowCentralSmallI5P1D809_piece_cap i hz
  rcases hbox with ⟨⟨hd0, hd1⟩, ⟨hr0, hrA⟩, ⟨hs0, hsA⟩, ⟨ht0, ht1⟩⟩
  have hbase : z ∈ sectionSixFirstLowCentralSmallI5P1D809BaseBox := by
    simp only [sectionSixFirstLowCentralSmallI5P1D809BaseBox, mem_prod, mem_Icc]
    exact ⟨⟨⟨⟨hd0, hd1⟩, hr0, hrA⟩, hs0, hsA⟩, ht0, ht1⟩
  exact ⟨hbase, hcap⟩

private theorem d809BaseBoxCompact : IsCompact sectionSixFirstLowCentralSmallI5P1D809BaseBox := by
  exact (((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).prod
    isCompact_Icc)

private theorem d809CapClosed : IsClosed sectionSixFirstLowCentralSmallI5P1D809Cap := by
  unfold sectionSixFirstLowCentralSmallI5P1D809Cap
  apply isClosed_le
  · fun_prop
  · fun_prop

theorem sectionSixFirstLowCentralSmallI5P1D809_carrier_compact : IsCompact sectionSixFirstLowCentralSmallI5P1D809Carrier := by
  exact d809BaseBoxCompact.inter_right d809CapClosed

theorem sectionSixFirstLowCentralSmallI5P1D809_carrier_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P1D809Carrier := by
  exact sectionSixFirstLowCentralSmallI5P1D809_carrier_compact.measurableSet

def sectionSixFirstLowCentralSmallI5P1D809Kernel (z : SectionSixP1AffineT) : Real :=
  sectionSixFirstLowCentralSmallQuadrupleKernel
    (sectionSixP1SharpPhiD806 d809Beta z)

theorem sectionSixFirstLowCentralSmallI5P1D809_kernel_comp_Psi
    {x : SectionSixP1AffineT} :
    sectionSixFirstLowCentralSmallI5P1D809Kernel
        (sectionSixP1SharpPsiD806 sectionSixFirstLowCentralSmallI5P1D807Beta x) =
      sectionSixFirstLowCentralSmallQuadrupleKernel x := by
  unfold sectionSixFirstLowCentralSmallI5P1D809Kernel
  rw [sectionSixP1SharpPhi_comp_PsiD806]

private theorem d809CarrierRatioMem {z : SectionSixP1AffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P1D809Carrier) :
    1 <= (1 - d809Beta - z.1.1.1 - z.1.1.2 - z.1.2 - z.2) / z.2 := by
  have hbox := hz.1
  have hcap := hz.2
  have hparts := by
    simpa only [sectionSixFirstLowCentralSmallI5P1D809BaseBox, mem_prod, mem_Icc, Prod.le_def] using hbox
  have ht : d809Gap <= z.2 := hparts.2.1
  have htpos : 0 < z.2 :=
    lt_of_lt_of_le d809EndpointConstants.2.1 ht
  change d809Beta + z.1.1.1 + z.1.1.2 + z.1.2 + 2 * z.2 <= 1 at hcap
  rw [le_div_iff₀ htpos]
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D809_kernel_continuousOn_carrier :
    ContinuousOn sectionSixFirstLowCentralSmallI5P1D809Kernel sectionSixFirstLowCentralSmallI5P1D809Carrier := by
  unfold sectionSixFirstLowCentralSmallI5P1D809Kernel sectionSixFirstLowCentralSmallQuadrupleKernel
  have hratio : ContinuousOn
      (fun z : SectionSixP1AffineT =>
        (1 - d809Beta - z.1.1.1 - z.1.1.2 - z.1.2 - z.2) / z.2)
      sectionSixFirstLowCentralSmallI5P1D809Carrier := by
    apply ((((continuousOn_const.sub continuousOn_fst.fst.fst).sub
      continuousOn_fst.fst.snd).sub continuousOn_fst.snd).sub
      continuousOn_snd).div continuousOn_snd
    intro z hz
    have hparts := by
      simpa only [sectionSixFirstLowCentralSmallI5P1D809BaseBox, mem_inter_iff, mem_prod, mem_Icc, Prod.le_def]
        using hz
    have ht : d809Gap <= z.2 := hparts.1.2.1
    have htpos : 0 < z.2 :=
      lt_of_lt_of_le d809EndpointConstants.2.1 ht
    exact htpos.ne'
  have hratio_mem : MapsTo
      (fun z : SectionSixP1AffineT =>
        (1 - d809Beta - z.1.1.1 - z.1.1.2 - z.1.2 - z.2) / z.2)
      sectionSixFirstLowCentralSmallI5P1D809Carrier (Ici 1) := by
    intro z hz
    exact d809CarrierRatioMem hz
  have hden : ∀ z ∈ sectionSixFirstLowCentralSmallI5P1D809Carrier,
      (d809Beta - z.1.1.1) * (z.1.1.1 + z.1.1.2) *
          (z.1.1.1 + z.1.2) * z.2 ^ (2 : Nat) ≠ 0 := by
    intro z hz
    have hparts := by
      simpa only [sectionSixFirstLowCentralSmallI5P1D809BaseBox, mem_inter_iff, mem_prod, mem_Icc, Prod.le_def]
        using hz
    have hbase := hparts.1
    have hD1 : z.1.1.1 <= d809D1 := hbase.1.1.1.2
    have hD0 : d809D0 <= z.1.1.1 := hbase.1.1.1.1
    have hr : 0 <= z.1.1.2 := hbase.1.1.2.1
    have hs : 0 <= z.1.2 := hbase.1.2.1
    have ht : d809Gap <= z.2 := hbase.2.1
    have hpos := d809EndpointConstants
    have hu : 0 < d809Beta - z.1.1.1 := by linarith [hpos.2.2.1]
    have hv : 0 < z.1.1.1 + z.1.1.2 := by
      linarith [hD0, hr, hpos.1]
    have hw : 0 < z.1.1.1 + z.1.2 := by
      linarith [hD0, hs, hpos.1]
    have htp : 0 < z.2 := by
      linarith [ht, hpos.2.1]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hu.ne' hv.ne') hw.ne')
      (pow_ne_zero 2 htp.ne')
  have hcont : ContinuousOn
      (fun z : SectionSixP1AffineT =>
        buchstabFunction
          ((1 - d809Beta - z.1.1.1 - z.1.1.2 - z.1.2 - z.2) / z.2) /
          ((d809Beta - z.1.1.1) * (z.1.1.1 + z.1.1.2) *
            (z.1.1.1 + z.1.2) * z.2 ^ (2 : Nat))) sectionSixFirstLowCentralSmallI5P1D809Carrier := by
    refine (continuousOn_buchstabFunction.comp hratio hratio_mem).div ?_ ?_
    · fun_prop
    · exact hden
  convert hcont using 1
  ext z
  simp [sectionSixP1SharpPhiD806]
  ring_nf

theorem sectionSixFirstLowCentralSmallI5P1D809_kernel_integrableOn_piece
    (i : Fin 3) :
    IntegrableOn sectionSixFirstLowCentralSmallI5P1D809Kernel
      (sectionSixFirstLowCentralSmallI5P1D808Piece i) volume := by
  exact sectionSixFirstLowCentralSmallI5P1D809_kernel_continuousOn_carrier
    |>.integrableOn_compact sectionSixFirstLowCentralSmallI5P1D809_carrier_compact
    |>.mono_set (sectionSixFirstLowCentralSmallI5P1D809_piece_subset_carrier i)

theorem sectionSixFirstLowCentralSmallI5P1D809_kernel_nonneg_piece (i : Fin 3) {z : SectionSixP1AffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P1D808Piece i) :
    0 ≤ sectionSixFirstLowCentralSmallI5P1D809Kernel z := by
  have hcarrier := sectionSixFirstLowCentralSmallI5P1D809_piece_subset_carrier i hz
  have hbase := hcarrier.1
  have hcap := hcarrier.2
  have hparts := by
    simpa only [sectionSixFirstLowCentralSmallI5P1D809BaseBox, mem_prod, mem_Icc, Prod.le_def] using hbase
  have hd0 : d809D0 ≤ z.1.1.1 := hparts.1.1.1.1
  have hd1 : z.1.1.1 ≤ d809D1 := hparts.1.1.1.2
  have hr0 : 0 ≤ z.1.1.2 := hparts.1.1.2.1
  have hs0 : 0 ≤ z.1.2 := hparts.1.2.1
  have ht0 : d809Gap ≤ z.2 := hparts.2.1
  have hpos := d809EndpointConstants
  have hu : 0 < d809Beta - z.1.1.1 := by linarith [hpos.2.2.1]
  have hv : 0 < z.1.1.1 + z.1.1.2 := by linarith [hd0, hr0, hpos.1]
  have hw : 0 < z.1.1.1 + z.1.2 := by linarith [hd0, hs0, hpos.1]
  have ht : 0 < z.2 := by linarith [ht0, hpos.2.1]
  have harg : 1 ≤
      (1 - d809Beta - z.1.1.1 - z.1.1.2 - z.1.2 - z.2) / z.2 := by
    change d809Beta + z.1.1.1 + z.1.1.2 + z.1.2 + 2 * z.2 ≤ 1 at hcap
    rw [le_div_iff₀ ht]
    linarith
  have homega : 0 ≤ buchstabFunction
      ((1 - d809Beta - z.1.1.1 - z.1.1.2 - z.1.2 - z.2) / z.2) := by
    linarith [(buchstabFunction_mem_Icc harg).1]
  unfold sectionSixFirstLowCentralSmallI5P1D809Kernel sectionSixFirstLowCentralSmallQuadrupleKernel
  simp only [sectionSixP1SharpPhiD806, Prod.fst_add, Prod.snd_add, zero_add]
  have harg_eq :
      (1 - (d809Beta + -z.1.1.1) - (z.1.1.1 + z.1.1.2) -
          (z.1.1.1 + z.1.2) - z.2) / z.2 =
        (1 - d809Beta - z.1.1.1 - z.1.1.2 - z.1.2 - z.2) / z.2 := by
    ring
  rw [harg_eq]
  apply div_nonneg homega
  exact (mul_pos (mul_pos (mul_pos hu hv) hw) (pow_pos ht 2)).le

theorem sectionSixFirstLowCentralSmallI5P1D809_native_image_integral_le_piece_sum :
    (∫ z in sectionSixP1SharpPsiD806 sectionSixFirstLowCentralSmallI5P1D807Beta ''
        sectionSixFirstLowCentralSmallI5P1D807Target, sectionSixFirstLowCentralSmallI5P1D809Kernel z ∂volume) ≤
      ∑ i : Fin 3, ∫ z in
        sectionSixFirstLowCentralSmallI5P1D808Piece i, sectionSixFirstLowCentralSmallI5P1D809Kernel z ∂volume := by
  apply sectionSixFirstLowCentralSmallI5P1D808_image_integral_le_piece_sum sectionSixFirstLowCentralSmallI5P1D809Kernel
  · exact sectionSixFirstLowCentralSmallI5P1D809_kernel_integrableOn_piece
  · exact sectionSixFirstLowCentralSmallI5P1D809_kernel_nonneg_piece

theorem sectionSixFirstLowCentralSmallI5P1D809_image_integral_eq_native_integral :
    (∫ z in sectionSixP1SharpPsiD806 sectionSixFirstLowCentralSmallI5P1D807Beta ''
        sectionSixFirstLowCentralSmallI5P1D807Target, sectionSixFirstLowCentralSmallI5P1D809Kernel z ∂volume) =
      ∫ x in sectionSixFirstLowCentralSmallI5P1D807Target,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume := by
  rw [sectionSixFirstLowCentralSmallI5P1D808_image_integral_eq_native_integral]
  apply setIntegral_congr_fun
    (sectionSixFirstLowCentralSmallI5PairPatternTarget_measurable (1 : Fin 4))
  intro x hx
  unfold sectionSixFirstLowCentralSmallI5P1D809Kernel
  change sectionSixFirstLowCentralSmallQuadrupleKernel
      (sectionSixP1SharpPhiD806 sectionSixFirstLowCentralSmallI5P1D807Beta
        (sectionSixP1SharpPsiD806 sectionSixFirstLowCentralSmallI5P1D807Beta x)) =
      sectionSixFirstLowCentralSmallQuadrupleKernel x
  rw [sectionSixP1SharpPhi_comp_PsiD806]

theorem sectionSixFirstLowCentralSmallI5P1D809_native_integral_le_piece_sum :
    (∫ x in sectionSixFirstLowCentralSmallI5P1D807Target,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) ≤
      ∑ i : Fin 3, ∫ z in
        sectionSixFirstLowCentralSmallI5P1D808Piece i,
          sectionSixFirstLowCentralSmallI5P1D809Kernel z ∂volume := by
  calc
    (∫ x in sectionSixFirstLowCentralSmallI5P1D807Target,
        sectionSixFirstLowCentralSmallQuadrupleKernel x ∂volume) =
        ∫ z in sectionSixP1SharpPsiD806
          sectionSixFirstLowCentralSmallI5P1D807Beta ''
            sectionSixFirstLowCentralSmallI5P1D807Target,
          sectionSixFirstLowCentralSmallI5P1D809Kernel z ∂volume :=
      (sectionSixFirstLowCentralSmallI5P1D809_image_integral_eq_native_integral).symm
    _ ≤ ∑ i : Fin 3, ∫ z in
        sectionSixFirstLowCentralSmallI5P1D808Piece i,
          sectionSixFirstLowCentralSmallI5P1D809Kernel z ∂volume :=
      sectionSixFirstLowCentralSmallI5P1D809_native_image_integral_le_piece_sum



end
end PrimesRestrictedDigits
