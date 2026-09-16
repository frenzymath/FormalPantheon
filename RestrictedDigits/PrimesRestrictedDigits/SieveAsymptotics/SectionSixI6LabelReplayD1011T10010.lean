import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6NativeChamberReplayD1009
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6CertificateSupportD1010
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C077
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C078
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C079
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C080
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C081
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C082
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C083
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C084
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C085
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C086
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C087
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C088
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C089
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C090
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.I6ChambersD1010.C091

/-!
# Closed I6 native-label bound: T10010
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
namespace T10010

def label : i6D691Label :=
  (true, (2, ![true, false, false, true, false]))

def trees (p : Fin 7 × Fin 7) : RationalTetraClipD1002 16 Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => SectionSixI6CertificateD1010.C077.tree
  | 0, 1 => SectionSixI6CertificateD1010.C078.tree
  | 0, 3 => SectionSixI6CertificateD1010.C079.tree
  | 0, 4 => SectionSixI6CertificateD1010.C080.tree
  | 0, 6 => SectionSixI6CertificateD1010.C081.tree
  | 2, 0 => SectionSixI6CertificateD1010.C082.tree
  | 2, 1 => SectionSixI6CertificateD1010.C083.tree
  | 2, 3 => SectionSixI6CertificateD1010.C084.tree
  | 2, 4 => SectionSixI6CertificateD1010.C085.tree
  | 2, 6 => SectionSixI6CertificateD1010.C086.tree
  | 5, 0 => SectionSixI6CertificateD1010.C087.tree
  | 5, 1 => SectionSixI6CertificateD1010.C088.tree
  | 5, 3 => SectionSixI6CertificateD1010.C089.tree
  | 5, 4 => SectionSixI6CertificateD1010.C090.tree
  | 5, 6 => SectionSixI6CertificateD1010.C091.tree
  | _, _ => .retain 0

def weights (p : Fin 7 × Fin 7) : Rat :=
  match p.1.val, p.2.val with
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 3 => 0
  | 0, 4 => 0
  | 0, 6 => 0
  | 2, 0 => (10670702297 / 6250000000000)
  | 2, 1 => 0
  | 2, 3 => (151076228433 / 100000000000000)
  | 2, 4 => 0
  | 2, 6 => 0
  | 5, 0 => 0
  | 5, 1 => 0
  | 5, 3 => 0
  | 5, 4 => 0
  | 5, 6 => 0
  | _, _ => 0

def total : Rat := (64361493037 / 20000000000000)

theorem valid (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).coverValid (i6D1005ChamberWalls label p.1 p.2)
      (i6D1006LeafValid label.2.1 p.1 p.2) i6D999OrderedPairRoot = true := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C077.label, SectionSixI6CertificateD1010.C077.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C077.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C078.label, SectionSixI6CertificateD1010.C078.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C078.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C079.label, SectionSixI6CertificateD1010.C079.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C079.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C080.label, SectionSixI6CertificateD1010.C080.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C080.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C081.label, SectionSixI6CertificateD1010.C081.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C081.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C082.label, SectionSixI6CertificateD1010.C082.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C082.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C083.label, SectionSixI6CertificateD1010.C083.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C083.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C084.label, SectionSixI6CertificateD1010.C084.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C084.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C085.label, SectionSixI6CertificateD1010.C085.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C085.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C086.label, SectionSixI6CertificateD1010.C086.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C086.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C087.label, SectionSixI6CertificateD1010.C087.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C087.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C088.label, SectionSixI6CertificateD1010.C088.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C088.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C089.label, SectionSixI6CertificateD1010.C089.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C089.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C090.label, SectionSixI6CertificateD1010.C090.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C090.valid
  next =>
    simpa only [trees, label, SectionSixI6CertificateD1010.C091.label, SectionSixI6CertificateD1010.C091.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C091.valid

theorem replay_eq_weight (p : Fin 7 × Fin 7) (hp : p ∈ i6D1009ActivePairs label) :
    (trees p).replayWeightRatD1010 (i6D1005ChamberWalls label p.1 p.2)
      i6D999OrderedPairRoot = weights p := by
  rcases p with ⟨l, h⟩
  fin_cases l <;> fin_cases h
  all_goals simp [i6D1009ActivePairs, i6D1004LowerActive, i6D1004UpperActive, label] at hp
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C077.label, SectionSixI6CertificateD1010.C077.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C077.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C078.label, SectionSixI6CertificateD1010.C078.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C078.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C079.label, SectionSixI6CertificateD1010.C079.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C079.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C080.label, SectionSixI6CertificateD1010.C080.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C080.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C081.label, SectionSixI6CertificateD1010.C081.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C081.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C082.label, SectionSixI6CertificateD1010.C082.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C082.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C083.label, SectionSixI6CertificateD1010.C083.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C083.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C084.label, SectionSixI6CertificateD1010.C084.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C084.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C085.label, SectionSixI6CertificateD1010.C085.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C085.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C086.label, SectionSixI6CertificateD1010.C086.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C086.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C087.label, SectionSixI6CertificateD1010.C087.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C087.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C088.label, SectionSixI6CertificateD1010.C088.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C088.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C089.label, SectionSixI6CertificateD1010.C089.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C089.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C090.label, SectionSixI6CertificateD1010.C090.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C090.replay
  next =>
    simpa only [trees, weights, label, SectionSixI6CertificateD1010.C091.label, SectionSixI6CertificateD1010.C091.root_eq_path,
      Fin.reduceFinMk] using SectionSixI6CertificateD1010.C091.replay

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

end T10010
end PrimesRestrictedDigits.SectionSixI6CertificateD1011
