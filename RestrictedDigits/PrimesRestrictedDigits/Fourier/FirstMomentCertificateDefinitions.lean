import PrimesRestrictedDigits.Fourier.FirstMomentCachedEdge
import PrimesRestrictedDigits.Fourier.Moment235CertificateDefinitions

/-!
# Definitions for exact first-moment certificates

Common constants and indices for the five representative `t=1` certificate
families. Concrete vector data and row checks are separate.
-/

namespace PrimesRestrictedDigits

/-- Common natural denominator for every first-moment edge certificate. -/
def firstMomentCertificateDenominator : Nat := 10 ^ 18

/-- Numerator of the certified transition growth ratio. -/
def firstMomentCertificateGrowthNumerator : Nat := 22419

/-- Denominator of the certified transition growth ratio. -/
def firstMomentCertificateGrowthDenominator : Nat := 10000

/-- Common checked upper bound for every vector numerator. -/
def firstMomentCertificateVectorMaximum : Nat := 10 ^ 15

/-- Embed one of the five complement representatives into the decimal digits. -/
def firstMomentRepresentativeDigit (a : Fin 5) : Fin 10 :=
  ⟨a.val, lt_trans a.isLt (by omega)⟩

/-- Decimal index of the predecessor obtained by prepending one digit to a
four-digit future state and dropping its final digit. -/
def firstMomentIncomingPreviousIndex
    (first : Fin 10) (future : Fin 10000) : Fin 10000 :=
  ⟨1000 * first.val + future.val / 10, by
    have hfirst := first.isLt
    have hfuture := future.isLt
    omega⟩

theorem firstMomentReflectedHalfVectorEntry_le_of_blocked
    (values : Vector (Vector Nat 100) 50) (bound : Nat)
    (hblocked : forall (block : Fin 50) (offset : Fin 100),
      moment235HalfVectorEntry values
          ⟨block.val * 100 + offset.val, by omega⟩ <= bound)
    (state : Fin 10000) :
    moment235ReflectedHalfVectorEntry values state <= bound := by
  let index : Fin 5000 :=
    if hstate : state.val < 5000 then ⟨state.val, hstate⟩
    else ⟨9999 - state.val, by
      have hlt := state.isLt
      omega⟩
  let block : Fin 50 := ⟨index.val / 100, by
    have hindex := index.isLt
    omega⟩
  let offset : Fin 100 :=
    ⟨index.val % 100, Nat.mod_lt _ (by omega)⟩
  have h := hblocked block offset
  have hindex :
      (⟨block.val * 100 + offset.val, by omega⟩ : Fin 5000) = index := by
    apply Fin.ext
    dsimp [block, offset]
    omega
  rw [hindex] at h
  exact h

end PrimesRestrictedDigits
