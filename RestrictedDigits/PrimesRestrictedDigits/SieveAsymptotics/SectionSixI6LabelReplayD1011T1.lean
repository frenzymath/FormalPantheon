import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6NativeChamberReplayD1009
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C014
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C015
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C016
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C017
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C018
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C019
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C020
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C021
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C022
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C023
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C024
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C025
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C026
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C027
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C028
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C029
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C030
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C031

/-!
# Closed I6 native-label bound: T1
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
namespace T1

def label : i6D691Label :=
  (true, (1, ![true, true, true, true, false]))

def trees (p : Fin 7 × Fin 7) : RationalTetraClipD1002 16 Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => SectionSixI6CertificateD1010.C014.tree
  | 0, 1 => SectionSixI6CertificateD1010.C015.tree
  | 0, 6 => SectionSixI6CertificateD1010.C016.tree
  | 1, 0 => SectionSixI6CertificateD1010.C017.tree
  | 1, 1 => SectionSixI6CertificateD1010.C018.tree
  | 1, 6 => SectionSixI6CertificateD1010.C019.tree
  | 2, 0 => SectionSixI6CertificateD1010.C020.tree
  | 2, 1 => SectionSixI6CertificateD1010.C021.tree
  | 2, 6 => SectionSixI6CertificateD1010.C022.tree
  | 3, 0 => SectionSixI6CertificateD1010.C023.tree
  | 3, 1 => SectionSixI6CertificateD1010.C024.tree
  | 3, 6 => SectionSixI6CertificateD1010.C025.tree
  | 4, 0 => SectionSixI6CertificateD1010.C026.tree
  | 4, 1 => SectionSixI6CertificateD1010.C027.tree
  | 4, 6 => SectionSixI6CertificateD1010.C028.tree
  | 5, 0 => SectionSixI6CertificateD1010.C029.tree
  | 5, 1 => SectionSixI6CertificateD1010.C030.tree
  | 5, 6 => SectionSixI6CertificateD1010.C031.tree
  | _, _ => .retain 0

def weights (p : Fin 7 × Fin 7) : Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 6 => 0
  | 1, 0 => (23759 / 1250000000000)
  | 1, 1 => 0
  | 1, 6 => (368331 / 25000000000000)
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 6 => 0
  | 3, 0 => 0
  | 3, 1 => 0
  | 3, 6 => 0
  | 4, 0 => 0
  | 4, 1 => 0
  | 4, 6 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 6 => 0
  | _, _ => 0

def total : Rat := (843511 / 25000000000000)

theorem valid (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).coverValid (i6D1005ChamberWalls label p.1 p.2)
      (i6D1006LeafValid label.2.1 p.1 p.2) i6D999OrderedPairRoot = true := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C014.label, SectionSixI6CertificateD1010.C014.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C014.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C015.label, SectionSixI6CertificateD1010.C015.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C015.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C016.label, SectionSixI6CertificateD1010.C016.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C016.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C017.label, SectionSixI6CertificateD1010.C017.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C017.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C018.label, SectionSixI6CertificateD1010.C018.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C018.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C019.label, SectionSixI6CertificateD1010.C019.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C019.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C020.label, SectionSixI6CertificateD1010.C020.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C020.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C021.label, SectionSixI6CertificateD1010.C021.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C021.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C022.label, SectionSixI6CertificateD1010.C022.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C022.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C023.label, SectionSixI6CertificateD1010.C023.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C023.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C024.label, SectionSixI6CertificateD1010.C024.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C024.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C025.label, SectionSixI6CertificateD1010.C025.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C025.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C026.label, SectionSixI6CertificateD1010.C026.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C026.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C027.label, SectionSixI6CertificateD1010.C027.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C027.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C028.label, SectionSixI6CertificateD1010.C028.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C028.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C029.label, SectionSixI6CertificateD1010.C029.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C029.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C030.label, SectionSixI6CertificateD1010.C030.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C030.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C031.label, SectionSixI6CertificateD1010.C031.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C031.valid

theorem replay_eq_weight (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).replayWeightRatD1010 (i6D1005ChamberWalls label p.1 p.2)
      i6D999OrderedPairRoot = weights p := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C014.label, SectionSixI6CertificateD1010.C014.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C014.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C015.label, SectionSixI6CertificateD1010.C015.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C015.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C016.label, SectionSixI6CertificateD1010.C016.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C016.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C017.label, SectionSixI6CertificateD1010.C017.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C017.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C018.label, SectionSixI6CertificateD1010.C018.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C018.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C019.label, SectionSixI6CertificateD1010.C019.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C019.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C020.label, SectionSixI6CertificateD1010.C020.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C020.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C021.label, SectionSixI6CertificateD1010.C021.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C021.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C022.label, SectionSixI6CertificateD1010.C022.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C022.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C023.label, SectionSixI6CertificateD1010.C023.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C023.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C024.label, SectionSixI6CertificateD1010.C024.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C024.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C025.label, SectionSixI6CertificateD1010.C025.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C025.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C026.label, SectionSixI6CertificateD1010.C026.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C026.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C027.label, SectionSixI6CertificateD1010.C027.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C027.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C028.label, SectionSixI6CertificateD1010.C028.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C028.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C029.label, SectionSixI6CertificateD1010.C029.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C029.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C030.label, SectionSixI6CertificateD1010.C030.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C030.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C031.label, SectionSixI6CertificateD1010.C031.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C031.replay

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

end T1
end PrimesRestrictedDigits.SectionSixI6CertificateD1011
