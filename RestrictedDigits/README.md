# Primes with Restricted Digits in Lean 4

A Lean 4 formalization of James Maynard's published Theorem 1.1 in
[*Primes with restricted digits*](https://doi.org/10.1007/s00222-019-00865-6),
Inventiones mathematicae 217 (2019), 127-218.

Let `A_a(X)` count natural numbers below `X` whose standard decimal expansion
omits digit `a`, and let `P_a(X)` count the primes among them. Uniformly for
every `a in {0,...,9}` and every real `X >= 4`, the theorem proves

$$
P_a(X) \asymp \frac{A_a(X)}{\log X}
\asymp \frac{X^{\log 9/\log 10}}{\log X}.
$$

## Build And Verify

Current pins are Lean `v4.32.0` and Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`.

The independent official comparator additionally requires an unprivileged
Linux x86-64 user with a working user systemd session and Landlock support. The
preparation command builds Comparator, its exporter and Landrun from
[pinned sources](scripts/comparator-tools.lock.json), using a pinned Go binary toolchain:

```sh
bash scripts/prepare_comparator_tools.sh
COMPARATOR_MEMORY_MAX=56G LEAN_NUM_THREADS=1 bash scripts/run_comparator.sh
```

The official replay has a measured runtime of 40 hours 51 minutes 56 seconds
and a 47.1 GiB memory peak. The launcher defaults to the command's 56 GiB,
one-worker profile and disables service swap.

## References

- James Maynard, [*Primes with restricted digits*](https://doi.org/10.1007/s00222-019-00865-6), Inventiones mathematicae 217 (2019).
- James Maynard, [*Primes with restricted digits*](https://arxiv.org/abs/1604.01041v2), arXiv v2, searchable source.
- Henryk Iwaniec, [*Rosser's sieve*](https://doi.org/10.4064/aa-36-2-171-202), Acta Arithmetica 36 (1980).
- D. R. Heath-Brown, [*Lectures on sieves*](https://arxiv.org/abs/math/0209360v1), auxiliary comparison.
- Hugh L. Montgomery and Robert C. Vaughan, [*Multiplicative Number Theory I*](https://doi.org/10.1017/CBO9780511618314).
- A. K. Lenstra, H. W. Lenstra, Jr. and L. Lovász, [*Factoring polynomials with rational coefficients*](https://ir.cwi.nl/pub/9304), CWI report IW 195/82.

In the Rosser-sieve development, equation references to Iwaniec mean
*Rosser's sieve*. Montgomery--Vaughan chapter and equation
references mean the first print edition of *Multiplicative Number Theory I*.
