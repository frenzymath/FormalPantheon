import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6NativeChamberReplayD1009
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C032
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C033
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C034
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C035
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C036
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C037
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C038
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C039
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C040
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C041
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C042
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C043
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C044
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C045

/-!
# Closed I6 native-label bound: T2
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
namespace T2

def label : i6D691Label :=
  (true, (1, ![true, true, true, true, true]))

def trees (p : Fin 7 × Fin 7) : RationalTetraClipD1002 16 Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => SectionSixI6CertificateD1010.C032.tree
  | 0, 1 => SectionSixI6CertificateD1010.C033.tree
  | 1, 0 => SectionSixI6CertificateD1010.C034.tree
  | 1, 1 => SectionSixI6CertificateD1010.C035.tree
  | 2, 0 => SectionSixI6CertificateD1010.C036.tree
  | 2, 1 => SectionSixI6CertificateD1010.C037.tree
  | 3, 0 => SectionSixI6CertificateD1010.C038.tree
  | 3, 1 => SectionSixI6CertificateD1010.C039.tree
  | 4, 0 => SectionSixI6CertificateD1010.C040.tree
  | 4, 1 => SectionSixI6CertificateD1010.C041.tree
  | 5, 0 => SectionSixI6CertificateD1010.C042.tree
  | 5, 1 => SectionSixI6CertificateD1010.C043.tree
  | 6, 0 => SectionSixI6CertificateD1010.C044.tree
  | 6, 1 => SectionSixI6CertificateD1010.C045.tree
  | _, _ => .retain 0

def weights (p : Fin 7 × Fin 7) : Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 1, 0 => (5309 / 100000000000000)
  | 1, 1 => (19894635159 / 100000000000000)
  | 2, 0 => 0
  | 2, 1 => 0
  | 3, 0 => 0
  | 3, 1 => 0
  | 4, 0 => (7535017 / 50000000000000)
  | 4, 1 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 6, 0 => (146907451 / 195312500000)
  | 6, 1 => (18184640943 / 100000000000000)
  | _, _ => 0

def total : Rat := (113310966357 / 100000000000000)

theorem valid (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).coverValid (i6D1005ChamberWalls label p.1 p.2)
      (i6D1006LeafValid label.2.1 p.1 p.2) i6D999OrderedPairRoot = true := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C032.label, SectionSixI6CertificateD1010.C032.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C032.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C033.label, SectionSixI6CertificateD1010.C033.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C033.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C034.label, SectionSixI6CertificateD1010.C034.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C034.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C035.label, SectionSixI6CertificateD1010.C035.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C035.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C036.label, SectionSixI6CertificateD1010.C036.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C036.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C037.label, SectionSixI6CertificateD1010.C037.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C037.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C038.label, SectionSixI6CertificateD1010.C038.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C038.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C039.label, SectionSixI6CertificateD1010.C039.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C039.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C040.label, SectionSixI6CertificateD1010.C040.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C040.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C041.label, SectionSixI6CertificateD1010.C041.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C041.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C042.label, SectionSixI6CertificateD1010.C042.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C042.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C043.label, SectionSixI6CertificateD1010.C043.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C043.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C044.label, SectionSixI6CertificateD1010.C044.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C044.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C045.label, SectionSixI6CertificateD1010.C045.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C045.valid

theorem replay_eq_weight (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).replayWeightRatD1010 (i6D1005ChamberWalls label p.1 p.2)
      i6D999OrderedPairRoot = weights p := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C032.label, SectionSixI6CertificateD1010.C032.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C032.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C033.label, SectionSixI6CertificateD1010.C033.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C033.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C034.label, SectionSixI6CertificateD1010.C034.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C034.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C035.label, SectionSixI6CertificateD1010.C035.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C035.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C036.label, SectionSixI6CertificateD1010.C036.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C036.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C037.label, SectionSixI6CertificateD1010.C037.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C037.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C038.label, SectionSixI6CertificateD1010.C038.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C038.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C039.label, SectionSixI6CertificateD1010.C039.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C039.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C040.label, SectionSixI6CertificateD1010.C040.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C040.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C041.label, SectionSixI6CertificateD1010.C041.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C041.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C042.label, SectionSixI6CertificateD1010.C042.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C042.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C043.label, SectionSixI6CertificateD1010.C043.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C043.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C044.label, SectionSixI6CertificateD1010.C044.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C044.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C045.label, SectionSixI6CertificateD1010.C045.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C045.replay

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

end T2
end PrimesRestrictedDigits.SectionSixI6CertificateD1011
