# Period Three Implies Chaos

## Project

This standalone Lean 4 project formalizes the complete Theorem I of T.-Y. Li
and J. A. Yorke, including the advertised period-three corollary.  It is a
proof-preserving refinement of the verified formalization in the parent
checkout; it builds independently and does not import that checkout as a
dependency.

## Final theorem

The formalization uses a total map `F : Real -> Real`, an order-connected set
`J`, `ContinuousOn F J`, and `MapsTo F J J`.  Under either orbit-order
configuration for a point `a in J` (the increasing or decreasing alternative
in [LY75, Theorem I, p. 987]),
`PeriodThree.TheoremIConclusion F J` proves all of the following:

1. Every positive natural number `k` is the least period of some `x in J`,
   expressed by `Function.minimalPeriod F x = k`.
2. There is an uncountable set `S subset J` disjoint from
   `Function.periodicPts F`.
3. Every two distinct points of `S` form a Li-Yorke pair: their orbit-distance
   sequence has positive `Filter.limsup` and zero `Filter.liminf`.
4. Every `p in S` has positive orbit-distance `Filter.limsup` from every
   periodic `q in J`.

The final public propositions and proofs are:

```lean
PeriodThree.LiYorkeTheorem : PeriodThree.LiYorkeTheorem
PeriodThree.liYorkeTheorem : PeriodThree.LiYorkeTheorem

PeriodThree.PeriodThreeImpliesChaos : PeriodThree.PeriodThreeImpliesChaos
PeriodThree.periodThreeImpliesChaos : PeriodThree.PeriodThreeImpliesChaos
```

`LiYorkeTheorem` universally quantifies over `J`, `F`, and an orbit-order
witness `a`.  `PeriodThreeImpliesChaos` derives that orbit-order witness from
the existence of a point in `J` with least period three, and then returns the
same four conclusions.  Least periods are explicit positive periods; orbit
distances are represented in `ENNReal`, with literal complete-lattice
`Filter.limsup` and `Filter.liminf` at `Filter.atTop`.

## References

The primary source is:

- **[LY75]** T.-Y. Li and J. A. Yorke, "Period Three Implies Chaos," *The
  American Mathematical Monthly* 82 (1975), no. 10, 985--992. DOI:
  [`10.1080/00029890.1975.11994008`](https://doi.org/10.1080/00029890.1975.11994008).

## Comparator verification

`Comparator/Challenge.lean` restates the two final propositions from
`PeriodThree/Statement.lean` with proof holes. `Comparator/Solution.lean` proves
the same declarations using the closed proofs in `PeriodThree/Main.lean`.

Use the [upstream comparator](https://github.com/leanprover/comparator) tag `v4.32.0` (commit
`07bc4ea40f2266dcb861820a2ec1fa3244ed307f`), whose Lean toolchain matches this
project. After building its `comparator` and `lean4export` targets, run from this
directory:

```bash
COMPARATOR_LANDRUN=/path/to/landrun \
COMPARATOR_LEAN4EXPORT=/path/to/lean4export \
lake env /path/to/comparator Comparator/config.json
```

The checked solution is limited to `propext`, `Quot.sound`, and
`Classical.choice`; nanoda checking is disabled in `Comparator/config.json`.
