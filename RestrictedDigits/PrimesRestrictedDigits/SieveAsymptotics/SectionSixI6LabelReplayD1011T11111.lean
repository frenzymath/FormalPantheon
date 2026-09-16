import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6NativeChamberReplayD1009
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C123
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C124
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C125
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C126
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C127
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C128
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C129
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C130
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C131
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C132
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C133
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C134

/-!
# Closed I6 native-label bound: T11111
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
namespace T11111

def label : i6D691Label :=
  (true, (2, ![true, true, true, true, true]))

def trees (p : Fin 7 × Fin 7) : RationalTetraClipD1002 16 Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => SectionSixI6CertificateD1010.C123.tree
  | 0, 1 => SectionSixI6CertificateD1010.C124.tree
  | 2, 0 => SectionSixI6CertificateD1010.C125.tree
  | 2, 1 => SectionSixI6CertificateD1010.C126.tree
  | 3, 0 => SectionSixI6CertificateD1010.C127.tree
  | 3, 1 => SectionSixI6CertificateD1010.C128.tree
  | 4, 0 => SectionSixI6CertificateD1010.C129.tree
  | 4, 1 => SectionSixI6CertificateD1010.C130.tree
  | 5, 0 => SectionSixI6CertificateD1010.C131.tree
  | 5, 1 => SectionSixI6CertificateD1010.C132.tree
  | 6, 0 => SectionSixI6CertificateD1010.C133.tree
  | 6, 1 => SectionSixI6CertificateD1010.C134.tree
  | _, _ => .retain 0

def weights (p : Fin 7 × Fin 7) : Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 3, 0 => 0
  | 3, 1 => 0
  | 4, 0 => 0
  | 4, 1 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 6, 0 => 0
  | 6, 1 => (2632865161 / 100000000000000)
  | _, _ => 0

def total : Rat := (2632865161 / 100000000000000)

theorem valid (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).coverValid (i6D1005ChamberWalls label p.1 p.2)
      (i6D1006LeafValid label.2.1 p.1 p.2) i6D999OrderedPairRoot = true := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C123.label, SectionSixI6CertificateD1010.C123.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C123.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C124.label, SectionSixI6CertificateD1010.C124.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C124.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C125.label, SectionSixI6CertificateD1010.C125.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C125.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C126.label, SectionSixI6CertificateD1010.C126.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C126.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C127.label, SectionSixI6CertificateD1010.C127.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C127.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C128.label, SectionSixI6CertificateD1010.C128.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C128.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C129.label, SectionSixI6CertificateD1010.C129.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C129.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C130.label, SectionSixI6CertificateD1010.C130.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C130.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C131.label, SectionSixI6CertificateD1010.C131.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C131.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C132.label, SectionSixI6CertificateD1010.C132.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C132.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C133.label, SectionSixI6CertificateD1010.C133.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C133.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C134.label, SectionSixI6CertificateD1010.C134.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C134.valid

theorem replay_eq_weight (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).replayWeightRatD1010 (i6D1005ChamberWalls label p.1 p.2)
      i6D999OrderedPairRoot = weights p := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C123.label, SectionSixI6CertificateD1010.C123.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C123.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C124.label, SectionSixI6CertificateD1010.C124.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C124.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C125.label, SectionSixI6CertificateD1010.C125.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C125.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C126.label, SectionSixI6CertificateD1010.C126.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C126.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C127.label, SectionSixI6CertificateD1010.C127.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C127.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C128.label, SectionSixI6CertificateD1010.C128.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C128.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C129.label, SectionSixI6CertificateD1010.C129.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C129.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C130.label, SectionSixI6CertificateD1010.C130.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C130.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C131.label, SectionSixI6CertificateD1010.C131.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C131.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C132.label, SectionSixI6CertificateD1010.C132.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C132.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C133.label, SectionSixI6CertificateD1010.C133.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C133.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C134.label, SectionSixI6CertificateD1010.C134.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C134.replay

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

end T11111
end PrimesRestrictedDigits.SectionSixI6CertificateD1011
