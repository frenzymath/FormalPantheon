import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6NativeChamberReplayD1009
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C108
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C109
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C110
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C111
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C112
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C113
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C114
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C115
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C116
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C117
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C118
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C119
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C120
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C121
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C122

/-!
# Closed I6 native-label bound: T11110
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
namespace T11110

def label : i6D691Label :=
  (true, (2, ![true, true, true, true, false]))

def trees (p : Fin 7 × Fin 7) : RationalTetraClipD1002 16 Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => SectionSixI6CertificateD1010.C108.tree
  | 0, 1 => SectionSixI6CertificateD1010.C109.tree
  | 0, 6 => SectionSixI6CertificateD1010.C110.tree
  | 2, 0 => SectionSixI6CertificateD1010.C111.tree
  | 2, 1 => SectionSixI6CertificateD1010.C112.tree
  | 2, 6 => SectionSixI6CertificateD1010.C113.tree
  | 3, 0 => SectionSixI6CertificateD1010.C114.tree
  | 3, 1 => SectionSixI6CertificateD1010.C115.tree
  | 3, 6 => SectionSixI6CertificateD1010.C116.tree
  | 4, 0 => SectionSixI6CertificateD1010.C117.tree
  | 4, 1 => SectionSixI6CertificateD1010.C118.tree
  | 4, 6 => SectionSixI6CertificateD1010.C119.tree
  | 5, 0 => SectionSixI6CertificateD1010.C120.tree
  | 5, 1 => SectionSixI6CertificateD1010.C121.tree
  | 5, 6 => SectionSixI6CertificateD1010.C122.tree
  | _, _ => .retain 0

def weights (p : Fin 7 × Fin 7) : Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 6 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 6 => 0
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 6 => 0
  | 4, 0 => (37115637 / 100000000000000)
  | 4, 1 => (29418063 / 100000000000000)
  | 4, 6 => (75361047 / 50000000000000)
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 6 => 0
  | _, _ => 0

def total : Rat := (108627897 / 50000000000000)

theorem valid (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).coverValid (i6D1005ChamberWalls label p.1 p.2)
      (i6D1006LeafValid label.2.1 p.1 p.2) i6D999OrderedPairRoot = true := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C108.label, SectionSixI6CertificateD1010.C108.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C108.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C109.label, SectionSixI6CertificateD1010.C109.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C109.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C110.label, SectionSixI6CertificateD1010.C110.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C110.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C111.label, SectionSixI6CertificateD1010.C111.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C111.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C112.label, SectionSixI6CertificateD1010.C112.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C112.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C113.label, SectionSixI6CertificateD1010.C113.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C113.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C114.label, SectionSixI6CertificateD1010.C114.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C114.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C115.label, SectionSixI6CertificateD1010.C115.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C115.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C116.label, SectionSixI6CertificateD1010.C116.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C116.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C117.label, SectionSixI6CertificateD1010.C117.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C117.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C118.label, SectionSixI6CertificateD1010.C118.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C118.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C119.label, SectionSixI6CertificateD1010.C119.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C119.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C120.label, SectionSixI6CertificateD1010.C120.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C120.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C121.label, SectionSixI6CertificateD1010.C121.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C121.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C122.label, SectionSixI6CertificateD1010.C122.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C122.valid

theorem replay_eq_weight (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).replayWeightRatD1010 (i6D1005ChamberWalls label p.1 p.2)
      i6D999OrderedPairRoot = weights p := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C108.label, SectionSixI6CertificateD1010.C108.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C108.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C109.label, SectionSixI6CertificateD1010.C109.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C109.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C110.label, SectionSixI6CertificateD1010.C110.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C110.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C111.label, SectionSixI6CertificateD1010.C111.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C111.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C112.label, SectionSixI6CertificateD1010.C112.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C112.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C113.label, SectionSixI6CertificateD1010.C113.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C113.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C114.label, SectionSixI6CertificateD1010.C114.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C114.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C115.label, SectionSixI6CertificateD1010.C115.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C115.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C116.label, SectionSixI6CertificateD1010.C116.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C116.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C117.label, SectionSixI6CertificateD1010.C117.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C117.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C118.label, SectionSixI6CertificateD1010.C118.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C118.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C119.label, SectionSixI6CertificateD1010.C119.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C119.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C120.label, SectionSixI6CertificateD1010.C120.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C120.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C121.label, SectionSixI6CertificateD1010.C121.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C121.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C122.label, SectionSixI6CertificateD1010.C122.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C122.replay

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

end T11110
end PrimesRestrictedDigits.SectionSixI6CertificateD1011
