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

## Radius-one classification

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

The later symbolic proof explains the search result. Hamming's binary
condition uses nonzero, pairwise-distinct check columns (1950, Section 3,
pp. 150-154). Lean proves the finite-field projective generalization:
radius-one unique decoding holds exactly when every checksum column is nonzero
and no two columns are proportional. It also proves the Hamming inequality

```text
1 + input columns * (field order - 1)
  <= field order ^ checksum rows.
```

For a binary checksum this becomes `n <= 2^r - 1`. The finite count remains a
useful exhaustive regression test.

## The first four-axis candidate exposed response splicing

The first `2 x 2 x 2 x 2` experiment allowed one global word for the checksum
audit and separate answers for coordinate openings. Its checksum was genuinely
radius-one unique-decoding, so checksum quality was not the defect.

For the all-zero canonical tensor and false claimed total one, the prover uses

```text
global response   = (1, 1, 1, 0)
local responses   = (0, 0, 0, 0).
```

The global word lies in the checksum kernel and has odd total, while every
local response is canonical. Lean verifies this explicit strategy and also
exhaustively finds a cheating strategy. The generic theorem
`safeForEveryChallenge_iff` identifies the pattern: independently safe global
and local responses splice whenever the commitment does not bind them to one
candidate.

This negative result covers only the separated-response grammar. It is not a
barrier against commitments or proximity protocols.

## Three bits bind the finite affine fold exactly

The corrected protocol sends no response after the challenge. For any nonzero
binary linear functional `ell` on four block values, Lean constructs a
three-bit checksum with a kernel vector `kappa` satisfying

```text
Hamming weight kappa >= 3
dot ell kappa = 1.
```

The syndrome and public claimed bit are four independent equations, so they
decode one global block word. A true parent uses the checksum of its canonical
word. For a false parent, every syndrome decodes a different word, and some
coordinate challenge emits a false child.

The library now retains three distinct receipts:

- executable finite search finds no cheating strategy for any four-coordinate
  claim;
- `FourCoordinateAffineBinding.exactStep` proves exactness symbolically; and
- `FourAxisAffine.exactStep` instantiates the result for an explicit
  `2 x 2 x 2 x 2` tensor and emits a two-axis tensor claim.

The last theorem is semantic. It does not prove that compiled Lean code copies
four field elements into the child or avoids retaining a closure over the
parent tensor.

## Why the positive primitive does not scale

The generic theorem `messageCardinality_ge_injectiveCanonicalFamily` makes the
remaining burden explicit: exhibit a large injectively indexed family of
canonical words and prove that the proposed decoder covers it.

An affine equation on `n + 1` binary coordinates leaves `n` free coordinates.
Lean proves that a deterministic no-response decoder representing every
solution needs at least `2^n` messages. When the messages are `r`-bit strings,
it derives `n <= r`.

Thus the three-bit four-coordinate binder is cardinality-optimal but cannot
compress an arbitrary exponentially larger block vector to square-log size.
The lower bound assumes every affine solution must be representable; it does
not cover structured canonical tensors or additional interaction.

## Next falsifiable step

The finite correctness interface is no longer missing. The remaining candidate
must beat the `n - 1` message barrier by exploiting structure in canonical
tensors or by using a charged far-case proximity interaction. It must also
connect the semantic two-axis child to an executable representation and full
resource profile. Otherwise the affine cardinality or local-slice product
barrier applies unchanged.
