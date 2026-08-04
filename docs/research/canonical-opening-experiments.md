# Canonical opening: first Lean experiments

*Research notebook, August 3, 2026. These are verified local lemmas and finite
experiments, not evidence that `P != NP`.*

The first pass produced one positive composition theorem, one exact but
asymptotically inadequate opening protocol, and one finite checksum threshold.
That is a useful shape: each result either narrows the missing construction or
turns a tempting shortcut into a theorem-level obstruction.

## One query exposed a vacuity bug

An exact opening accepts a canonical answer for every public challenge and
gives a rejecting challenge for every proof of a noncanonical answer. Replacing
one oracle query by such an opening preserves perfect acceptance.

Lean rejected the first statement because the challenge type could be empty.
In that case, "every challenge accepts" is vacuously true and cannot force the
original verifier to accept anything. The corrected theorem explicitly assumes
`Nonempty Challenge`.

The two-query theorem then tested adaptivity. The general theorem now covers
every well-founded adaptive oracle verifier. A later original query may depend
on earlier claimed answers, but no original answer may depend on the later
opening challenges. We enforce this by batching opening challenges after the
original transcript. This is a formal version of transcript projection:
opening randomness cannot influence which canonical oracle entries were
queried.

The strategy type records only the realized path. It therefore also supports
pathwise resource accounting. If the original verifier fits budget `B0`, every
opening fits budget `B`, and a strategy path asks `q` queries, the expanded
profile fits `B0 + q*B` in every tracked category. The categories explicitly
include rounds, prover and challenge bits, verifier time and workspace,
compiler and preprocessing time, input access, and inherited descriptions.
These are conservative accounting values; an implementation theorem must still
prove that an executable opening realizes its declared profile.

The checked modules are:

```text
ComplexityTheory.ProofComplexity.CanonicalOpening
ComplexityTheory.ProofComplexity.CanonicalOpening.TwoQuery
ComplexityTheory.ProofComplexity.CanonicalOpening.Adaptive
ComplexityTheory.ProofComplexity.CanonicalOpening.AdaptiveResources
```

They prove semantic equivalence only. They make no runtime, communication, or
workspace claim.

## The obvious tensor fold is exact

Suppose a parent value is a weighted contraction of canonical slice values.
The prover can list one alleged value for every slice. A binding challenge
checks that their weighted sum equals the parent claim; a localization
challenge emits one selected slice claim.

This has exact false descent. If the binding equation fails, reject. If it
passes for a false parent, not every listed slice can be canonical, so some
localization challenge emits a false child. Lean proves this over any finite
index type and semiring in
`ComplexityTheory.ProofComplexity.CanonicalOpening.LinearContraction`.

The same module proves why this does not meet the target scale. If parent mass
is `sliceCount * childMass` and both the full slice list and child mass fit a
budget `B`, then parent mass is at most `B^2`. Therefore, for

```text
parent mass = 2^(m^2)
budget      = 2^(C*m),
```

the full-slice protocol cannot bound both quantities by the budget once
`m > 2*C`. A checksum mechanism must genuinely beat this product barrier.

The repeated version is no better. If each of `r` rounds selects one of at most
`B` uniform slices and leaves a child of mass at most `B`, then parent mass is
at most `B^(r+1)`. Lean proves that `B = 2^(C*m)` cannot cover parent mass
`2^(m^2)` whenever `C*(r+1) < m`. Thus every fixed number of plain local-slice
rounds fails at sufficiently large scale. This theorem deliberately does not
cover an algebraic or proximity argument that constructs a genuinely different
compressed child.

## What a checksum actually buys

Chen, Hong, Kalai, and Xi define a radius-`d` unique-decoding checksum: two
distinct words within Hamming distance `d` of one center must have different
checksums. Linear-code syndromes satisfy this when every nonzero kernel word has
weight greater than `2d` (*Towards a Doubly Efficient IP = PSPACE*, ECCC
TR26-102, revision 1, June 19, 2026, Definition 6 and Proposition 1, p. 9
(PDF p. 11)).

The Lean module `CanonicalOpening.Checksum` reuses Mathlib's `hammingDist` and
`hammingNorm` to prove that criterion. It also proves the exact near-far
consequence:

```text
same checksum + distance <= d -> same word
same checksum + different word -> distance > d
```

The checksum supplies binding only in the near case. CHKX still uses a row
interactive proof of proximity to handle the far case; replacing that machinery
with "check a syndrome" would be unsound.

There is also a checksum-only barrier. If a decoder can recover every coordinate
of every word from its checksum, then the checksum map is injective. For binary
words, Lean derives the cardinality consequence directly: a checksum with `r`
binary coordinates cannot exactly open arbitrary coordinates of `n`-bit words
when `r < n`. Any real compression must therefore use proximity information or
additional interaction rather than treating the syndrome as a short local copy
of the word.

The first combined checksum/locality barrier is stronger. Radius-one binding
forces every input coordinate to occur in at least one row of a linear checksum
matrix: an untouched coordinate would let the zero word collide with its unit
vector. If every checksum row touches at most `L` coordinates, incidence
counting gives

```text
input coordinates <= checksum rows * L.
```

Therefore a linear syndrome with at most `2^(C*m)` symbols whose individual
symbols open on supports of mass at most `2^(C*m)` cannot cover an oracle of
mass `2^(m^2)` once `m > 2*C`. This formally rules out the direct
"short sparse syndrome plus open one checksum row" grammar. A surviving
construction must use a proximity interaction that produces a different
compressed child, or make dense checksum rows locally accessible by some
additional algebraic mechanism.

## First finite synthesis result

We exhaustively enumerated binary linear checksum matrices for three-bit words
at decoding radius one. Lean verified:

```text
checksum rows   surviving matrices
0               0
1               0
2               6
```

One survivor is

```text
[1 1 0]
[0 1 1].
```

`CanonicalOpening.Checksum.Finite` retains this matrix, proves its
unique-decoding property, counts all six two-row survivors, and proves that
every one-row matrix has two distinct equal-checksum words within radius one of
a common center. The latter theorem is a complete finite cheating certificate,
not merely a failed search result.

## Next falsifiable step

The next candidate must combine this checksum binding with an executable
localization rule that exposes a row defect in the far case. It succeeds only
if the emitted child is smaller than the parent without sending all slice
values. Otherwise the product barrier applies unchanged.
