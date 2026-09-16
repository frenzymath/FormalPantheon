import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6NativeChamberReplayD1009
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C046
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C047
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C048
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C049
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C050
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C051
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C052

/-!
# Closed I6 native-label bound: F00000
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
namespace F00000

def label : i6D691Label :=
  (false, (2, ![false, false, false, false, false]))

def trees (p : Fin 7 × Fin 7) : RationalTetraClipD1002 16 Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => SectionSixI6CertificateD1010.C046.tree
  | 0, 1 => SectionSixI6CertificateD1010.C047.tree
  | 0, 2 => SectionSixI6CertificateD1010.C048.tree
  | 0, 3 => SectionSixI6CertificateD1010.C049.tree
  | 0, 4 => SectionSixI6CertificateD1010.C050.tree
  | 0, 5 => SectionSixI6CertificateD1010.C051.tree
  | 0, 6 => SectionSixI6CertificateD1010.C052.tree
  | _, _ => .retain 0

def weights (p : Fin 7 × Fin 7) : Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => (1173758807207 / 50000000000000)
  | 0, 1 => 0
  | 0, 2 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 5 => (610990140501 / 100000000000000)
  | 0, 6 => 0
  | _, _ => 0

def total : Rat := (591701550983 / 20000000000000)

theorem valid (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).coverValid (i6D1005ChamberWalls label p.1 p.2)
      (i6D1006LeafValid label.2.1 p.1 p.2) i6D999OrderedPairRoot = true := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C046.label, SectionSixI6CertificateD1010.C046.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C046.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C047.label, SectionSixI6CertificateD1010.C047.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C047.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C048.label, SectionSixI6CertificateD1010.C048.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C048.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C049.label, SectionSixI6CertificateD1010.C049.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C049.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C050.label, SectionSixI6CertificateD1010.C050.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C050.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C051.label, SectionSixI6CertificateD1010.C051.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C051.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C052.label, SectionSixI6CertificateD1010.C052.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C052.valid

theorem replay_eq_weight (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).replayWeightRatD1010 (i6D1005ChamberWalls label p.1 p.2)
      i6D999OrderedPairRoot = weights p := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C046.label, SectionSixI6CertificateD1010.C046.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C046.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C047.label, SectionSixI6CertificateD1010.C047.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C047.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C048.label, SectionSixI6CertificateD1010.C048.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C048.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C049.label, SectionSixI6CertificateD1010.C049.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C049.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C050.label, SectionSixI6CertificateD1010.C050.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C050.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C051.label, SectionSixI6CertificateD1010.C051.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C051.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C052.label, SectionSixI6CertificateD1010.C052.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C052.replay

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

end F00000
end PrimesRestrictedDigits.SectionSixI6CertificateD1011
