import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6NativeChamberReplayD1009
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C065
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C066
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C067
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C068
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C069
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C070
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C071
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C072
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C073
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C074
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C075
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C076

/-!
# Closed I6 native-label bound: T00010
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
namespace T00010

def label : i6D691Label :=
  (true, (2, ![false, false, false, true, false]))

def trees (p : Fin 7 × Fin 7) : RationalTetraClipD1002 16 Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => SectionSixI6CertificateD1010.C065.tree
  | 0, 1 => SectionSixI6CertificateD1010.C066.tree
  | 0, 2 => SectionSixI6CertificateD1010.C067.tree
  | 0, 3 => SectionSixI6CertificateD1010.C068.tree
  | 0, 4 => SectionSixI6CertificateD1010.C069.tree
  | 0, 6 => SectionSixI6CertificateD1010.C070.tree
  | 5, 0 => SectionSixI6CertificateD1010.C071.tree
  | 5, 1 => SectionSixI6CertificateD1010.C072.tree
  | 5, 2 => SectionSixI6CertificateD1010.C073.tree
  | 5, 3 => SectionSixI6CertificateD1010.C074.tree
  | 5, 4 => SectionSixI6CertificateD1010.C075.tree
  | 5, 6 => SectionSixI6CertificateD1010.C076.tree
  | _, _ => .retain 0

def weights (p : Fin 7 × Fin 7) : Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => (1501587027 / 20000000000000)
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 6 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 2 => 0
  | 5, 3 => 0
  | 5, 4 => 0
  | 5, 6 => 0
  | _, _ => 0

def total : Rat := (1501587027 / 20000000000000)

theorem valid (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).coverValid (i6D1005ChamberWalls label p.1 p.2)
      (i6D1006LeafValid label.2.1 p.1 p.2) i6D999OrderedPairRoot = true := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C065.label, SectionSixI6CertificateD1010.C065.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C065.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C066.label, SectionSixI6CertificateD1010.C066.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C066.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C067.label, SectionSixI6CertificateD1010.C067.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C067.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C068.label, SectionSixI6CertificateD1010.C068.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C068.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C069.label, SectionSixI6CertificateD1010.C069.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C069.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C070.label, SectionSixI6CertificateD1010.C070.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C070.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C071.label, SectionSixI6CertificateD1010.C071.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C071.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C072.label, SectionSixI6CertificateD1010.C072.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C072.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C073.label, SectionSixI6CertificateD1010.C073.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C073.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C074.label, SectionSixI6CertificateD1010.C074.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C074.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C075.label, SectionSixI6CertificateD1010.C075.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C075.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C076.label, SectionSixI6CertificateD1010.C076.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C076.valid

theorem replay_eq_weight (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).replayWeightRatD1010 (i6D1005ChamberWalls label p.1 p.2)
      i6D999OrderedPairRoot = weights p := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C065.label, SectionSixI6CertificateD1010.C065.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C065.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C066.label, SectionSixI6CertificateD1010.C066.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C066.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C067.label, SectionSixI6CertificateD1010.C067.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C067.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C068.label, SectionSixI6CertificateD1010.C068.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C068.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C069.label, SectionSixI6CertificateD1010.C069.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C069.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C070.label, SectionSixI6CertificateD1010.C070.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C070.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C071.label, SectionSixI6CertificateD1010.C071.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C071.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C072.label, SectionSixI6CertificateD1010.C072.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C072.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C073.label, SectionSixI6CertificateD1010.C073.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C073.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C074.label, SectionSixI6CertificateD1010.C074.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C074.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C075.label, SectionSixI6CertificateD1010.C075.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C075.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C076.label, SectionSixI6CertificateD1010.C076.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C076.replay

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

end T00010
end PrimesRestrictedDigits.SectionSixI6CertificateD1011
