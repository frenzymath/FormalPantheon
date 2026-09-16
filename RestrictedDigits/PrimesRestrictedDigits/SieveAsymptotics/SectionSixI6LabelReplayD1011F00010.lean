import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6NativeChamberReplayD1009
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C053
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C054
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C055
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C056
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C057
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C058
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C059
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C060
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C061
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C062
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C063
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C064

/-!
# Closed I6 native-label bound: F00010
All active chamber proofs are actual kernel-checked imports.
Source: `MAYNARD-PRD-PUBLISHED`, p.144, Eq. (6.13).
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open MeasureTheory
open scoped BigOperators

namespace PrimesRestrictedDigits.SectionSixI6CertificateD1011
namespace F00010

def label : i6D691Label :=
  (false, (2, ![false, false, false, true, false]))

def trees (p : Fin 7 × Fin 7) : RationalTetraClipD1002 16 Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => SectionSixI6CertificateD1010.C053.tree
  | 0, 1 => SectionSixI6CertificateD1010.C054.tree
  | 0, 2 => SectionSixI6CertificateD1010.C055.tree
  | 0, 3 => SectionSixI6CertificateD1010.C056.tree
  | 0, 4 => SectionSixI6CertificateD1010.C057.tree
  | 0, 6 => SectionSixI6CertificateD1010.C058.tree
  | 5, 0 => SectionSixI6CertificateD1010.C059.tree
  | 5, 1 => SectionSixI6CertificateD1010.C060.tree
  | 5, 2 => SectionSixI6CertificateD1010.C061.tree
  | 5, 3 => SectionSixI6CertificateD1010.C062.tree
  | 5, 4 => SectionSixI6CertificateD1010.C063.tree
  | 5, 6 => SectionSixI6CertificateD1010.C064.tree
  | _, _ => .retain 0

def weights (p : Fin 7 × Fin 7) : Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 6 => 0
  | 5, 0 => (236601999279 / 10000000000000)
  | 5, 1 => 0
  | 5, 2 => 0
  | 5, 3 => 0
  | 5, 4 => 0
  | 5, 6 => 0
  | _, _ => 0

def total : Rat := (236601999279 / 10000000000000)

theorem valid (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).coverValid (i6D1005ChamberWalls label p.1 p.2)
      (i6D1006LeafValid label.2.1 p.1 p.2) i6D999OrderedPairRoot = true := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C053.label, SectionSixI6CertificateD1010.C053.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C053.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C054.label, SectionSixI6CertificateD1010.C054.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C054.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C055.label, SectionSixI6CertificateD1010.C055.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C055.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C056.label, SectionSixI6CertificateD1010.C056.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C056.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C057.label, SectionSixI6CertificateD1010.C057.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C057.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C058.label, SectionSixI6CertificateD1010.C058.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C058.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C059.label, SectionSixI6CertificateD1010.C059.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C059.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C060.label, SectionSixI6CertificateD1010.C060.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C060.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C061.label, SectionSixI6CertificateD1010.C061.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C061.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C062.label, SectionSixI6CertificateD1010.C062.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C062.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C063.label, SectionSixI6CertificateD1010.C063.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C063.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C064.label, SectionSixI6CertificateD1010.C064.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C064.valid

theorem replay_eq_weight (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).replayWeightRatD1010 (i6D1005ChamberWalls label p.1 p.2)
      i6D999OrderedPairRoot = weights p := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C053.label, SectionSixI6CertificateD1010.C053.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C053.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C054.label, SectionSixI6CertificateD1010.C054.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C054.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C055.label, SectionSixI6CertificateD1010.C055.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C055.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C056.label, SectionSixI6CertificateD1010.C056.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C056.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C057.label, SectionSixI6CertificateD1010.C057.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C057.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C058.label, SectionSixI6CertificateD1010.C058.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C058.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C059.label, SectionSixI6CertificateD1010.C059.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C059.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C060.label, SectionSixI6CertificateD1010.C060.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C060.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C061.label, SectionSixI6CertificateD1010.C061.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C061.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C062.label, SectionSixI6CertificateD1010.C062.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C062.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C063.label, SectionSixI6CertificateD1010.C063.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C063.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C064.label, SectionSixI6CertificateD1010.C064.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C064.replay

theorem sum_weights :
    ∑ p ∈ i6D1009ActivePairs label, weights p = total := by
  decide +kernel

theorem native_integral_le :
    (∫ x in i6D691NativeTarget label, sectionSixFirstLowBelowQuadrupleKernel x) ≤ (total : Real) := by
  have h := i6D1009NativeTarget_integral_le_replay label trees valid
  have hs : (∑ p ∈ i6D1009ActivePairs label,
      (((trees p).retainedLeaves (i6D1005ChamberWalls label p.1 p.2)
        i6D999OrderedPairRoot).map (fun leaf => leaf.1.volumeRat * leaf.2)).sum : Rat) = total := by
    change (∑ p ∈ i6D1009ActivePairs label,
      (trees p).replayWeightRatD1010 (i6D1005ChamberWalls label p.1 p.2) i6D999OrderedPairRoot) = total
    calc
      _ = ∑ p ∈ i6D1009ActivePairs label, weights p := Finset.sum_congr rfl replay_eq_weight
      _ = total := sum_weights
  simpa only [hs] using h

end F00010
end PrimesRestrictedDigits.SectionSixI6CertificateD1011
