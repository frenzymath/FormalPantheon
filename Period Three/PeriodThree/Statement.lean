module

public import Mathlib.Data.ENNReal.Real
public import Mathlib.Data.Set.Function
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Public statement of Li-Yorke's Theorem I

This file is intentionally self-contained: it imports only narrow Mathlib
modules and defines
the mathematical vocabulary and propositions that a reviewer must inspect.
The source is Li and Yorke, *Period Three Implies Chaos* (1975), Theorem I,
p. 987, with T2 expanded from Appendix 2, pp. 990-992.

The interval is represented by an `OrdConnected` subset of `ℝ`; `F` is a total
ambient map whose restriction is continuous and maps the interval to itself.
The target set is not assumed nonempty separately: the hypotheses supply the
orbit witness `a ∈ J`. ``Function.minimalPeriod F x = k`` means *least*
positive period, and all public period quantifiers explicitly require `0 < k`.
The distance is coerced with `ENNReal.ofReal`, so the displayed `limsup` and
`liminf` are the literal complete-lattice filter operations at `atTop`, rather
than an implicit real-valued convention. The periodic-point clause quantifies
over `q ∈ J` in addition to `q ∈ Function.periodicPts F`, matching the paper's
periodic points in the interval. Closed interval endpoints in the order
configuration are intentional (`≤`/`≥` at the third iterate); strict
inequalities are retained for the two adjacent orbit points.
-/

@[expose] public section

namespace PeriodThree

open Set

/-- The nonnegative extended-real orbit distance in [LY75, equations
(2.1)-(2.2) and condition (B), p. 987]. -/
def orbitDistance (F : ℝ → ℝ) (p q : ℝ) : ℕ → ENNReal :=
  fun n => ENNReal.ofReal |(F^[n]) p - (F^[n]) q|

/-- The two limit conditions in [LY75, equations (2.1)-(2.2), p. 987]. -/
def LiYorkePair (F : ℝ → ℝ) (p q : ℝ) : Prop :=
  0 < Filter.limsup (orbitDistance F p q) Filter.atTop ∧
    Filter.liminf (orbitDistance F p q) Filter.atTop = 0

/-- Positive upper-limit separation in condition (B) of [LY75, Theorem I, p. 987]. -/
def SeparatedFromPeriodic (F : ℝ → ℝ) (p q : ℝ) : Prop :=
  0 < Filter.limsup (orbitDistance F p q) Filter.atTop

/-- The scrambled-set clauses in [LY75, Theorem I, part T2, p. 987]. -/
def LiYorkeScrambledSet (F : ℝ → ℝ) (J S : Set ℝ) : Prop :=
  S ⊆ J ∧
    ¬S.Countable ∧
      Disjoint S (Function.periodicPts F) ∧
        ∀ ⦃p q : ℝ⦄, p ∈ S → q ∈ S → p ≠ q → LiYorkePair F p q

/-- The two orbit-order alternatives in [LY75, Theorem I, p. 987]. -/
def OrbitOrder (F : ℝ → ℝ) (a : ℝ) : Prop :=
  ((F^[3]) a ≤ a ∧ a < F a ∧ F a < (F^[2]) a) ∨
    ((F^[3]) a ≥ a ∧ a > F a ∧ F a > (F^[2]) a)

/-- The T1 and T2 conclusions of [LY75, Theorem I, p. 987]. -/
def TheoremIConclusion (F : ℝ → ℝ) (J : Set ℝ) : Prop :=
  (∀ k : ℕ, 0 < k → ∃ x ∈ J, Function.minimalPeriod F x = k) ∧
    (∃ S : Set ℝ,
      LiYorkeScrambledSet F J S ∧
        ∀ ⦃p q : ℝ⦄, p ∈ S → q ∈ J → q ∈ Function.periodicPts F →
          SeparatedFromPeriodic F p q)

/-- The complete proposition of [LY75, Theorem I, p. 987]. -/
def LiYorkeTheorem : Prop :=
  ∀ (J : Set ℝ) (F : ℝ → ℝ) (a : ℝ),
    J.OrdConnected → ContinuousOn F J → MapsTo F J J → a ∈ J → OrbitOrder F a →
      TheoremIConclusion F J

/-- The period-three corollary following [LY75, Theorem I, p. 987]. -/
def PeriodThreeImpliesChaos : Prop :=
  ∀ (J : Set ℝ) (F : ℝ → ℝ),
    J.OrdConnected → ContinuousOn F J → MapsTo F J J →
      (∃ a ∈ J, Function.minimalPeriod F a = 3) →
        TheoremIConclusion F J

end PeriodThree
