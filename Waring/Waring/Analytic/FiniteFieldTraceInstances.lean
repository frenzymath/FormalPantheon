import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Waring.Analytic.WeilWeights

/-!
# Compatibility of the two prime-field algebra structures on extensions

For `FiniteField.Extension (ZMod p) p n`, Mathlib provides both the algebra
data inherited from the generic base field and the directly derived
prime-field algebra structure.  Their maps, and hence their field traces,
agree.  This file packages that compatibility without equating the dependent
typeclass structures themselves.
 -/

namespace Waring.Analytic

namespace FiniteFieldTraceInstances

variable {p n : Nat} [Fact p.Prime] [NeZero n]

/-- The algebra map supplied by the generic base-extension structure. -/
noncomputable def baseAlgebraMap :
    ZMod p →+* FiniteField.Extension (ZMod p) p n := by
  letI : Algebra (ZMod p) (FiniteField.Extension (ZMod p) p n) :=
    FiniteField.instAlgebraExtension (ZMod p) p n
  exact algebraMap (ZMod p) (FiniteField.Extension (ZMod p) p n)

/-- The algebra map supplied directly by the chosen Galois field. -/
noncomputable def primeAlgebraMap :
    ZMod p →+* FiniteField.Extension (ZMod p) p n := by
  letI : Algebra (ZMod p) (FiniteField.Extension (ZMod p) p n) :=
    FiniteField.instAlgebraZModExtension (ZMod p) p n
  exact algebraMap (ZMod p) (FiniteField.Extension (ZMod p) p n)

/-- The trace supplied by the generic base-extension structure. -/
noncomputable def baseTrace :
    FiniteField.Extension (ZMod p) p n → ZMod p := by
  letI : Algebra (ZMod p) (FiniteField.Extension (ZMod p) p n) :=
    FiniteField.instAlgebraExtension (ZMod p) p n
  exact fun x ↦ Algebra.trace (ZMod p)
    (FiniteField.Extension (ZMod p) p n) x

/-- The trace supplied directly by the chosen Galois field. -/
noncomputable def primeTrace :
    FiniteField.Extension (ZMod p) p n → ZMod p := by
  letI : Algebra (ZMod p) (FiniteField.Extension (ZMod p) p n) :=
    FiniteField.instAlgebraZModExtension (ZMod p) p n
  exact fun x ↦ Algebra.trace (ZMod p)
    (FiniteField.Extension (ZMod p) p n) x

/-- The generic and direct prime-field traces agree pointwise. -/
theorem baseTrace_eq_primeTrace
    (x : FiniteField.Extension (ZMod p) p n) :
    baseTrace (p := p) (n := n) x = primeTrace (p := p) (n := n) x := by
  have hbase :
      baseAlgebraMap (p := p) (n := n) (baseTrace (p := p) (n := n) x) =
        ∑ i ∈ Finset.range n, x ^ p ^ i := by
    letI : Algebra (ZMod p) (FiniteField.Extension (ZMod p) p n) :=
      FiniteField.instAlgebraExtension (ZMod p) p n
    dsimp [baseAlgebraMap, baseTrace]
    rw [FiniteField.algebraMap_trace_eq_sum_pow,
      FiniteField.finrank_extension, Nat.card_zmod]
  have hprime :
      primeAlgebraMap (p := p) (n := n) (primeTrace (p := p) (n := n) x) =
        ∑ i ∈ Finset.range n, x ^ p ^ i := by
    letI : Algebra (ZMod p) (FiniteField.Extension (ZMod p) p n) :=
      FiniteField.instAlgebraZModExtension (ZMod p) p n
    dsimp [primeAlgebraMap, primeTrace]
    rw [FiniteField.algebraMap_trace_eq_sum_pow,
      FiniteField.finrank_zmod_extension, Nat.card_zmod]
    simp
  have hmap : baseAlgebraMap (p := p) (n := n) =
      primeAlgebraMap (p := p) (n := n) :=
    Subsingleton.elim _ _
  apply (baseAlgebraMap (p := p) (n := n)).injective
  calc
    baseAlgebraMap (p := p) (n := n) (baseTrace (p := p) (n := n) x) =
        ∑ i ∈ Finset.range n, x ^ p ^ i := hbase
    _ = primeAlgebraMap (p := p) (n := n)
        (primeTrace (p := p) (n := n) x) := hprime.symm
    _ = baseAlgebraMap (p := p) (n := n)
        (primeTrace (p := p) (n := n) x) := by
      rw [hmap]

/-- Character evaluation of a point-phase trace is unchanged when switching
from the directly derived prime-field algebra structure to the generic
base-extension structure. -/
theorem character_trace_pointPhase_eq_base
    (character : AddChar (ZMod p) Complex) (b : Fin 5 → ZMod p)
    (x : FiniteField.Extension (ZMod p) p n) :
    character
        (Algebra.trace (ZMod p) (FiniteField.Extension (ZMod p) p n)
          (Weil.pointPhase
            ((algebraMap (ZMod p)
              (FiniteField.Extension (ZMod p) p n)) ∘ b) x)) =
      character
        (baseTrace (p := p) (n := n)
          (Weil.pointPhase
            ((baseAlgebraMap (p := p) (n := n)) ∘ b) x)) := by
  have hmap : baseAlgebraMap (p := p) (n := n) =
      primeAlgebraMap (p := p) (n := n) :=
    Subsingleton.elim _ _
  have hphase :
      Weil.pointPhase
          ((baseAlgebraMap (p := p) (n := n)) ∘ b) x =
        Weil.pointPhase
          ((primeAlgebraMap (p := p) (n := n)) ∘ b) x := by
    rw [hmap]
  have hnamed :
      character
          (primeTrace (p := p) (n := n)
            (Weil.pointPhase
              ((primeAlgebraMap (p := p) (n := n)) ∘ b) x)) =
        character
          (baseTrace (p := p) (n := n)
            (Weil.pointPhase
              ((baseAlgebraMap (p := p) (n := n)) ∘ b) x)) := by
    congr 1
    calc
      primeTrace (p := p) (n := n)
          (Weil.pointPhase
            ((primeAlgebraMap (p := p) (n := n)) ∘ b) x) =
        baseTrace (p := p) (n := n)
          (Weil.pointPhase
            ((primeAlgebraMap (p := p) (n := n)) ∘ b) x) :=
        (baseTrace_eq_primeTrace _).symm
      _ = baseTrace (p := p) (n := n)
          (Weil.pointPhase
            ((baseAlgebraMap (p := p) (n := n)) ∘ b) x) := by
        rw [hphase]
  simpa only [primeTrace, primeAlgebraMap] using hnamed

end FiniteFieldTraceInstances

end Waring.Analytic
