import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6NativeChamberReplayD1009
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C000
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C001
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C002
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C003
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C004
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C005
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C006
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C007
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C008
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C009
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C010
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C011
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C012
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C013

/-!
# Closed I6 native-label bound: T0
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
namespace T0

def label : i6D691Label :=
  (true, (0, ![true, true, true, true, true]))

def trees (p : Fin 7 × Fin 7) : RationalTetraClipD1002 16 Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => SectionSixI6CertificateD1010.C000.tree
  | 0, 1 => SectionSixI6CertificateD1010.C001.tree
  | 1, 0 => SectionSixI6CertificateD1010.C002.tree
  | 1, 1 => SectionSixI6CertificateD1010.C003.tree
  | 2, 0 => SectionSixI6CertificateD1010.C004.tree
  | 2, 1 => SectionSixI6CertificateD1010.C005.tree
  | 3, 0 => SectionSixI6CertificateD1010.C006.tree
  | 3, 1 => SectionSixI6CertificateD1010.C007.tree
  | 4, 0 => SectionSixI6CertificateD1010.C008.tree
  | 4, 1 => SectionSixI6CertificateD1010.C009.tree
  | 5, 0 => SectionSixI6CertificateD1010.C010.tree
  | 5, 1 => SectionSixI6CertificateD1010.C011.tree
  | 6, 0 => SectionSixI6CertificateD1010.C012.tree
  | 6, 1 => SectionSixI6CertificateD1010.C013.tree
  | _, _ => .retain 0

def weights (p : Fin 7 × Fin 7) : Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 1, 0 => (4166787571 / 50000000000000)
  | 1, 1 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 3, 0 => 0
  | 3, 1 => 0
  | 4, 0 => 0
  | 4, 1 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 6, 0 => 0
  | 6, 1 => 0
  | _, _ => 0

def total : Rat := (4166787571 / 50000000000000)

theorem valid (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).coverValid (i6D1005ChamberWalls label p.1 p.2)
      (i6D1006LeafValid label.2.1 p.1 p.2) i6D999OrderedPairRoot = true := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C000.label, SectionSixI6CertificateD1010.C000.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C000.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C001.label, SectionSixI6CertificateD1010.C001.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C001.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C002.label, SectionSixI6CertificateD1010.C002.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C002.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C003.label, SectionSixI6CertificateD1010.C003.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C003.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C004.label, SectionSixI6CertificateD1010.C004.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C004.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C005.label, SectionSixI6CertificateD1010.C005.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C005.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C006.label, SectionSixI6CertificateD1010.C006.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C006.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C007.label, SectionSixI6CertificateD1010.C007.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C007.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C008.label, SectionSixI6CertificateD1010.C008.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C008.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C009.label, SectionSixI6CertificateD1010.C009.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C009.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C010.label, SectionSixI6CertificateD1010.C010.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C010.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C011.label, SectionSixI6CertificateD1010.C011.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C011.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C012.label, SectionSixI6CertificateD1010.C012.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C012.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C013.label, SectionSixI6CertificateD1010.C013.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C013.valid

theorem replay_eq_weight (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).replayWeightRatD1010 (i6D1005ChamberWalls label p.1 p.2)
      i6D999OrderedPairRoot = weights p := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C000.label, SectionSixI6CertificateD1010.C000.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C000.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C001.label, SectionSixI6CertificateD1010.C001.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C001.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C002.label, SectionSixI6CertificateD1010.C002.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C002.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C003.label, SectionSixI6CertificateD1010.C003.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C003.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C004.label, SectionSixI6CertificateD1010.C004.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C004.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C005.label, SectionSixI6CertificateD1010.C005.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C005.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C006.label, SectionSixI6CertificateD1010.C006.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C006.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C007.label, SectionSixI6CertificateD1010.C007.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C007.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C008.label, SectionSixI6CertificateD1010.C008.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C008.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C009.label, SectionSixI6CertificateD1010.C009.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C009.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C010.label, SectionSixI6CertificateD1010.C010.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C010.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C011.label, SectionSixI6CertificateD1010.C011.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C011.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C012.label, SectionSixI6CertificateD1010.C012.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C012.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C013.label, SectionSixI6CertificateD1010.C013.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C013.replay

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

end T0
end PrimesRestrictedDigits.SectionSixI6CertificateD1011
