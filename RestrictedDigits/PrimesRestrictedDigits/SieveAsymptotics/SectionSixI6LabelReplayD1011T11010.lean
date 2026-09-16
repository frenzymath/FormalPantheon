import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6NativeChamberReplayD1009
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C092
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C093
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C094
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C095
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C096
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C097
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C098
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C099
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C100
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C101
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C102
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C103
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C104
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C105
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C106
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C107

/-!
# Closed I6 native-label bound: T11010
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
namespace T11010

def label : i6D691Label :=
  (true, (2, ![true, true, false, true, false]))

def trees (p : Fin 7 × Fin 7) : RationalTetraClipD1002 16 Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => SectionSixI6CertificateD1010.C092.tree
  | 0, 1 => SectionSixI6CertificateD1010.C093.tree
  | 0, 4 => SectionSixI6CertificateD1010.C094.tree
  | 0, 6 => SectionSixI6CertificateD1010.C095.tree
  | 2, 0 => SectionSixI6CertificateD1010.C096.tree
  | 2, 1 => SectionSixI6CertificateD1010.C097.tree
  | 2, 4 => SectionSixI6CertificateD1010.C098.tree
  | 2, 6 => SectionSixI6CertificateD1010.C099.tree
  | 3, 0 => SectionSixI6CertificateD1010.C100.tree
  | 3, 1 => SectionSixI6CertificateD1010.C101.tree
  | 3, 4 => SectionSixI6CertificateD1010.C102.tree
  | 3, 6 => SectionSixI6CertificateD1010.C103.tree
  | 5, 0 => SectionSixI6CertificateD1010.C104.tree
  | 5, 1 => SectionSixI6CertificateD1010.C105.tree
  | 5, 4 => SectionSixI6CertificateD1010.C106.tree
  | 5, 6 => SectionSixI6CertificateD1010.C107.tree
  | _, _ => .retain 0

def weights (p : Fin 7 × Fin 7) : Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 4 => 0
  | 0, 6 => 0
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 4 => 0
  | 2, 6 => 0
  | 3, 0 => (273299208497 / 50000000000000)
  | 3, 1 => 0
  | 3, 4 => (87384961833 / 100000000000000)
  | 3, 6 => (249582714189 / 100000000000000)
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 4 => 0
  | 5, 6 => 0
  | _, _ => 0

def total : Rat := (110445761627 / 12500000000000)

theorem valid (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).coverValid (i6D1005ChamberWalls label p.1 p.2)
      (i6D1006LeafValid label.2.1 p.1 p.2) i6D999OrderedPairRoot = true := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C092.label, SectionSixI6CertificateD1010.C092.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C092.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C093.label, SectionSixI6CertificateD1010.C093.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C093.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C094.label, SectionSixI6CertificateD1010.C094.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C094.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C095.label, SectionSixI6CertificateD1010.C095.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C095.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C096.label, SectionSixI6CertificateD1010.C096.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C096.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C097.label, SectionSixI6CertificateD1010.C097.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C097.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C098.label, SectionSixI6CertificateD1010.C098.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C098.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C099.label, SectionSixI6CertificateD1010.C099.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C099.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C100.label, SectionSixI6CertificateD1010.C100.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C100.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C101.label, SectionSixI6CertificateD1010.C101.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C101.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C102.label, SectionSixI6CertificateD1010.C102.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C102.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C103.label, SectionSixI6CertificateD1010.C103.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C103.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C104.label, SectionSixI6CertificateD1010.C104.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C104.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C105.label, SectionSixI6CertificateD1010.C105.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C105.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C106.label, SectionSixI6CertificateD1010.C106.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C106.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C107.label, SectionSixI6CertificateD1010.C107.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C107.valid

theorem replay_eq_weight (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).replayWeightRatD1010 (i6D1005ChamberWalls label p.1 p.2)
      i6D999OrderedPairRoot = weights p := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C092.label, SectionSixI6CertificateD1010.C092.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C092.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C093.label, SectionSixI6CertificateD1010.C093.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C093.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C094.label, SectionSixI6CertificateD1010.C094.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C094.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C095.label, SectionSixI6CertificateD1010.C095.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C095.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C096.label, SectionSixI6CertificateD1010.C096.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C096.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C097.label, SectionSixI6CertificateD1010.C097.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C097.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C098.label, SectionSixI6CertificateD1010.C098.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C098.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C099.label, SectionSixI6CertificateD1010.C099.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C099.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C100.label, SectionSixI6CertificateD1010.C100.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C100.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C101.label, SectionSixI6CertificateD1010.C101.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C101.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C102.label, SectionSixI6CertificateD1010.C102.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C102.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C103.label, SectionSixI6CertificateD1010.C103.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C103.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C104.label, SectionSixI6CertificateD1010.C104.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C104.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C105.label, SectionSixI6CertificateD1010.C105.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C105.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C106.label, SectionSixI6CertificateD1010.C106.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C106.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C107.label, SectionSixI6CertificateD1010.C107.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C107.replay

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

end T11010
end PrimesRestrictedDigits.SectionSixI6CertificateD1011
