# Lean proofs of conjectures

## Kimberling’s greedy sequence, OEIS A026488

The sequence contains exactly the positive integers congruent to 1 modulo 3, together with 3. Its first terms are 1, 3, 4, 7, 10, 13. With one-based indexing, its formula is `a(n) = 3n − 5` for every `n ≥ 3`. [OEIS A026488](https://oeis.org/A026488) · [Formal proof](A026488.lean)

Starting with 1, the sequence takes the least larger integer that passes the following test. Append the trial integer `x` to the prefix. Reject it if three entries at indices `i ≤ j ≤ k` satisfy `a(i)a(j) = x + a(k)`. This includes the trial integer itself. For example, 2 rejects itself because `2 × 2 = 2 + 2`.

The proof constructs a forbidden triple for each skipped integer. For every accepted integer above 6, reduction modulo 3 rules out such a triple unless the last entry equals 3. In that case the product minus the last entry is at most 6. Induction then identifies the unique greedy sequence.

`Kimberling488.A026488` proves existence and uniqueness for the recurrence. `Kimberling488.range_A026488` gives the complete range. The Lean file starts its indices at zero.

### Rebuild

Install Lean with Elan, then run these commands from the repository root.

```sh
lake exe cache get
lake build
lake env leanchecker A026488
```

The toolchain file pins Lean 4.36.0. The Lake manifest pins mathlib and its dependencies. The axiom report lists `propext`, `Classical.choice`, and `Quot.sound` for both theorems.

Clark Kimberling authored the OEIS entry. Sean A. Irvine reported checking the conjecture through index 1,300 in 2019. The August 2026 revision still labels the formula conjectural. This repository contains an AI-assisted proof. [Dated OEIS record](https://github.com/oeis/oeisdata/blob/c5bd71de9eee0894df1301baa4f43f6431d8a08d/seq/A026/A026488.seq)
