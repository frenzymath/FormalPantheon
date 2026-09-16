import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2CertificateSupportD990
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ThreeRootCoverD974
import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch014
import PrimesRestrictedDigits.SieveAsymptotics.CertificateData.P2ForestD990.Branch015

/-!
# exact P2 forest branch Branch016
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits
namespace SectionSixP2CertificateD990
namespace Branch016

/- Root 1, exact path ((1, 'right'), (2, 'left'), (4, 'left')), 708 retained leaves. -/
def tree : RationalTetraSubdivision SectionSixP2LeafPayloadD988 :=
  (.split (5 : Fin 6)
    Branch014.tree
    Branch015.tree
  )

theorem valid :
    tree.coverValid sectionSixP2LeafValidD988 ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) = true := by
  have hvalid000 :
      Branch014.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) = true := by
    exact Branch014.valid
  have hvalid001 :
      Branch015.tree.coverValid sectionSixP2LeafValidD988 (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) = true := by
    exact Branch015.valid
  have hvalid002 :=
    valid_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hvalid000 hvalid001
  simpa only [tree] using hvalid002

theorem replay :
    tree.replayWeightRat ((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (fun _ p => p.upper) =
      (269455778614379576055087 / 1638400000000000000000000000 : Rat) := by
  have hreplay000 :
      Branch014.tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).leftChild (5 : Fin 6)) (fun _ p => p.upper) =
        (513842946225232601401857 / 16384000000000000000000000000 : Rat) := by
    exact Branch014.replay
  have hreplay001 :
      Branch015.tree.replayWeightRat (((((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)).rightChild (5 : Fin 6)) (fun _ p => p.upper) =
        (2180714839918563159149013 / 16384000000000000000000000000 : Rat) := by
    exact Branch015.replay
  have hraw002 :=
    replay_split (T := (((sectionSixP2RootD974 (1 : Fin 3)).rightChild (1 : Fin 6)).leftChild (2 : Fin 6)).leftChild (4 : Fin 6)) (e := (5 : Fin 6)) hreplay000 hreplay001
  have hreplay002 := hraw002.trans
    (by norm_num : (513842946225232601401857 / 16384000000000000000000000000 : Rat) + (2180714839918563159149013 / 16384000000000000000000000000 : Rat) = (269455778614379576055087 / 1638400000000000000000000000 : Rat))
  simpa only [tree] using hreplay002

end Branch016
end SectionSixP2CertificateD990
end PrimesRestrictedDigits
