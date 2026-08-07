# BoundedGapsMathlib

BoundedGapsMathlib is a Lean 4 and Mathlib formalization of James Maynard's
unconditional bounded-gaps theorem. It proves, without project-specific
axioms, that prime pairs separated by at most 600 occur arbitrarily far along
the number line. The project also formalizes the equivalent statements for
consecutive primes and for the liminf of the sequence of prime gaps.

Mathematically, this is a strengthening of the breakthrough initiated by
Yitang Zhang's paper *Bounded gaps between primes*. Zhang proved for the first
time that infinitely many pairs of primes differ by at most one fixed
constant, with an initial explicit bound below 70,000,000. Maynard's
multidimensional refinement of the GPY sieve gave the much stronger explicit
bound 600 formalized here. The primary source for the final result is James
Maynard's *Small gaps between primes*, arXiv:1311.4600v3, Theorem 1.3.

## Main Theorem

The final Lean theorem is
`BoundedGaps.unconditional_boundedGapsStatement`. In ordinary mathematical
notation, it states

```text
for every N in the natural numbers, there exist primes p and q such that
N < p < q and q - p <= 600.
```

Thus there are infinitely many bounded prime gaps. The formalization also
proves that this statement is equivalent to the existence of arbitrarily
large *consecutive* prime pairs with gap at most 600, and to Maynard's paper
formulation

```text
liminf (p_(n+1) - p_n) <= 600.
```

The exact definitions and equivalence theorems are in
[`BoundedGaps/Statement.lean`](BoundedGaps/Statement.lean) and
[`BoundedGaps/Proof/LiminfBridge.lean`](BoundedGaps/Proof/LiminfBridge.lean).
The unconditional export is in
[`BoundedGaps/Proof/MainTheorem.lean`](BoundedGaps/Proof/MainTheorem.lean).

## Proof Route

The proof follows the analytic-number-theory route used by Maynard. A central
input is the Bombieri--Vinogradov theorem (BV), which supplies the required
average distribution of primes in arithmetic progressions. The project first
proves a source-faithful weighted BV theorem and converts it to the natural
prime-counting formulation consumed by the sieve. It then combines BV with
the ordinary prime number theorem, Maynard's multidimensional sieve weights,
an exact rational certificate, and an admissible 105-element tuple. Positivity
of the resulting sieve sum forces two prime shifts inside an interval of
diameter 600, which yields the main theorem.

## Verification

The public bounded-gaps interface and its production-backed solution have
passed the project's comparator checks. The comparator independently fixes
the expected declarations in [`Comparator/Challenge.lean`](Comparator/Challenge.lean)
and checks them against the closed proofs exposed through
[`Comparator/Solution.lean`](Comparator/Solution.lean). The audit compares
the elaborated interfaces, verifies production delegation and isolation from
the challenge placeholders, and checks the permitted axiom footprint. The
broader publication trust replay also passed the BV interface, exact
certificate, final-composition, proof-closure, and axiom gates.

## References And Project Map

- Yitang Zhang, [*Bounded gaps between primes*](https://doi.org/10.4007/annals.2014.179.3.7),
  *Annals of Mathematics* 179 (2014), 1121--1174.
- James Maynard, [*Small gaps between primes*](https://arxiv.org/abs/1311.4600v3),
  arXiv:1311.4600v3, especially Theorem 1.3.
- [`BoundedGaps/Statement.lean`](BoundedGaps/Statement.lean) contains the
  public statement; [`BoundedGaps/Proof/MainTheorem.lean`](BoundedGaps/Proof/MainTheorem.lean)
  contains the final unconditional composition.
- [`BoundedGaps/BombieriVinogradov/`](BoundedGaps/BombieriVinogradov/) contains
  the formalized BV route, while [`BoundedGaps/Maynard/`](BoundedGaps/Maynard/)
  contains the sieve argument and exact constant-600 specialization.
